// EndBASIC
// Copyright 2026 Julio Merino
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not
// use this file except in compliance with the License.  You may obtain a copy
// of the License at:
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.

//! Symbol table for EndBASIC compilation.

use crate::ast::{ExprType, VarRef};
use crate::bytecode::{Register, RegisterScope};
use crate::compiler::ids::HashMapWithIds;
use crate::{CallableMetadata, bytecode};
use std::cell::RefCell;
use std::cmp::max;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;
use std::rc::Rc;

/// Errors related to symbols handling.
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)] // The error messages and names are good enough.
pub(super) enum Error {
    #[error("Cannot redefine {0}")]
    AlreadyDefined(VarRef),

    #[error("Incompatible type annotation in {0} reference")]
    IncompatibleTypeAnnotationInReference(VarRef),

    #[error("Out of {0} registers")]
    OutOfRegisters(RegisterScope),

    #[error("Undefined {1} symbol {0}")]
    UndefinedSymbol(VarRef, RegisterScope),
}

/// Result type for symbol table operations.
type Result<T> = std::result::Result<T, Error>;

/// The key of a symbol in the symbols table.
///
/// The key is stored in a canonicalized form (uppercase) to make all lookups case-insensitive.
#[derive(Clone, Debug, Hash, Eq, Ord, PartialEq, PartialOrd)]
pub struct SymbolKey(String);

impl<R: AsRef<str>> From<R> for SymbolKey {
    fn from(value: R) -> Self {
        Self(value.as_ref().to_ascii_uppercase())
    }
}

impl fmt::Display for SymbolKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Gets the register and type of a local or global variable if it already exists.
fn get_var<MKR>(
    vref: &VarRef,
    table: &HashMapWithIds<SymbolKey, ExprType, u8>,
    make_register: MKR,
    scope: RegisterScope,
) -> Result<(Register, ExprType)>
where
    MKR: FnOnce(u8) -> std::result::Result<Register, bytecode::OutOfRegistersError>,
{
    let key = SymbolKey::from(&vref.name);
    match table.get(&key) {
        Some((etype, reg)) => {
            if !vref.accepts(*etype) {
                return Err(Error::IncompatibleTypeAnnotationInReference(vref.clone()));
            }

            let reg = make_register(reg).map_err(|_| Error::OutOfRegisters(scope))?;
            Ok((reg, *etype))
        }

        None => Err(Error::UndefinedSymbol(vref.clone(), scope)),
    }
}

/// Defines a new local or global variable and assigns a register to it.
///
/// Panics if the variable already exists.
fn put_var<MKR>(
    key: SymbolKey,
    vtype: ExprType,
    table: &mut HashMapWithIds<SymbolKey, ExprType, u8>,
    make_register: MKR,
    scope: RegisterScope,
) -> Result<Register>
where
    MKR: FnOnce(u8) -> std::result::Result<Register, bytecode::OutOfRegistersError>,
{
    match table.insert(key, vtype) {
        Some((None, reg)) => Ok(make_register(reg).map_err(|_| Error::OutOfRegisters(scope))?),

        Some((Some(_old_etype), _reg)) => {
            unreachable!("Cannot redefine variable; caller must check for presence first");
        }

        None => Err(Error::OutOfRegisters(scope)),
    }
}

/// Representation of the symbol table for global symbols.
///
/// Globals are variables and callables that are visible from any scope.
pub(crate) struct GlobalSymtable<'uref, 'ukey, 'umd> {
    /// Map of global variable names to their types and assigned registers.
    globals: HashMapWithIds<SymbolKey, ExprType, u8>,

    /// Reference to the built-in callable metadata provided by the runtime.
    upcalls: &'uref HashMap<&'ukey SymbolKey, &'umd CallableMetadata>,

    /// Map of user-defined callable names to their metadata.
    user_callables: HashMap<SymbolKey, CallableMetadata>,
}

impl<'uref, 'ukey, 'umd> GlobalSymtable<'uref, 'ukey, 'umd> {
    /// Creates a new global symbol table that knows about the given `upcalls`.
    pub(crate) fn new(upcalls: &'uref HashMap<&'ukey SymbolKey, &'umd CallableMetadata>) -> Self {
        Self { globals: HashMapWithIds::default(), upcalls, user_callables: HashMap::default() }
    }

    /// Enters a new local scope.
    pub(crate) fn enter_scope(&mut self) -> LocalSymtable<'uref, 'ukey, 'umd, '_> {
        LocalSymtable::new(self)
    }

    /// Gets a global variable by its `vref`.
    pub(crate) fn get_global(&self, vref: &VarRef) -> Result<(Register, ExprType)> {
        get_var(vref, &self.globals, Register::global, RegisterScope::Global)
    }

    /// Creates a new global variable `key` of `vtype`.
    pub(crate) fn put_global(&mut self, key: SymbolKey, vtype: ExprType) -> Result<Register> {
        put_var(key, vtype, &mut self.globals, Register::global, RegisterScope::Global)
    }

    /// Defines a new user-defined `vref` callable with `md` metadata.
    pub(crate) fn define_user_callable(
        &mut self,
        vref: &VarRef,
        md: CallableMetadata,
    ) -> Result<()> {
        let key = SymbolKey::from(&vref.name);
        let previous = self.user_callables.insert(key, md);
        if previous.is_none() { Ok(()) } else { Err(Error::AlreadyDefined(vref.clone())) }
    }

    /// Gets a callable by its name `key`.
    pub(crate) fn get_callable(&self, key: &SymbolKey) -> Option<&CallableMetadata> {
        self.user_callables.get(key).or(self.upcalls.get(key).copied())
    }
}

/// Representation of the symbol table for a local scope.
///
/// A local scope can see all global symbols and defines its own symbols, which can shadow the
/// global ones.
pub(crate) struct LocalSymtable<'uref, 'ukey, 'umd, 'a> {
    /// Reference to the parent global symbol table.
    symtable: &'a mut GlobalSymtable<'uref, 'ukey, 'umd>,

    /// Map of local variable names to their types and assigned registers.
    locals: HashMapWithIds<SymbolKey, ExprType, u8>,

    /// Maximum number of allocated temporary registers in all possible evaluation scopes created
    /// by this local symtable.  This is used to determine the size of the scope for register
    /// allocation purposes at runtime.
    count_temps: u8,
}

impl<'uref, 'ukey, 'umd, 'a> LocalSymtable<'uref, 'ukey, 'umd, 'a> {
    /// Creates a new local symbol table within the context of a global `symtable`.
    fn new(symtable: &'a mut GlobalSymtable<'uref, 'ukey, 'umd>) -> Self {
        Self { symtable, locals: HashMapWithIds::default(), count_temps: 0 }
    }

    /// Consumes the local scope and returns the number of local variables defined, which includes
    /// the locals themselves and any temporaries used by the scope.
    pub(crate) fn leave_scope(self) -> Result<u8> {
        match u8::try_from(self.locals.len() + usize::from(self.count_temps)) {
            Ok(nregs) => Ok(nregs),
            Err(_) => Err(Error::OutOfRegisters(RegisterScope::Local)),
        }
    }

    /// Defines a new user-defined `vref` callable with `md` metadata.
    pub(crate) fn define_user_callable(
        &mut self,
        vref: &VarRef,
        md: CallableMetadata,
    ) -> Result<()> {
        self.symtable.define_user_callable(vref, md)
    }

    /// Freezes this table to get a `TempSymtable` that can be used to compile expressions.
    pub(crate) fn frozen(&mut self) -> TempSymtable<'uref, 'ukey, 'umd, '_, 'a> {
        TempSymtable::new(self)
    }

    /// Creates a new global variable `key` of `vtype`.
    pub(crate) fn put_global(&mut self, key: SymbolKey, vtype: ExprType) -> Result<Register> {
        self.symtable.put_global(key, vtype)
    }

    /// Gets a variable by its `vref`, looking for it in the local and global scopes.
    pub(crate) fn get_local_or_global(&self, vref: &VarRef) -> Result<(Register, ExprType)> {
        match get_var(vref, &self.locals, Register::local, RegisterScope::Local) {
            Ok(local) => Ok(local),
            Err(Error::UndefinedSymbol(..)) => self.symtable.get_global(vref),
            Err(e) => Err(e),
        }
    }

    /// Gets a callable by its name `key`.
    pub(crate) fn get_callable(&self, key: &SymbolKey) -> Option<&CallableMetadata> {
        self.symtable.get_callable(key)
    }

    /// Creates a new local variable `key` of `vtype`.
    pub(crate) fn put_local(&mut self, key: SymbolKey, vtype: ExprType) -> Result<Register> {
        put_var(key, vtype, &mut self.locals, Register::local, RegisterScope::Local)
    }

    /// Changes the type of an existing local variable `vref` to `new_etype`.
    ///
    /// This is used for type inference on first assignment.
    pub(crate) fn fixup_local_type(&mut self, vref: &VarRef, new_etype: ExprType) -> Result<()> {
        let key = SymbolKey::from(&vref.name);
        // TODO: Verify reference type.
        match self.locals.get_mut(&key) {
            Some((etype, _reg)) => {
                *etype = new_etype;
                Ok(())
            }
            None => Err(Error::UndefinedSymbol(vref.clone(), RegisterScope::Local)),
        }
    }
}

/// A read-only view into a `SymTable` that allows allocating temporary registers.
///
/// This layer on top of `LocalSymtable` may seem redundant because all of the temporary
/// register manipulation happens in `TempScope`, but it is necessary to have this layer
/// to forbid mutations to local variables.  We need to be able to pass a `TempSymtable`
/// across recursive function calls (for expression evaluation), but at the same time we
/// need each call site to have its own `TempScope` for temporary register cleanup.
pub(crate) struct TempSymtable<'uref, 'ukey, 'umd, 'temp, 'local> {
    /// Reference to the underlying local symbol table.
    symtable: &'temp mut LocalSymtable<'uref, 'ukey, 'umd, 'local>,

    /// Index of the next temporary register to allocate.
    next_temp: Rc<RefCell<u8>>,

    /// Maximum number of allocated temporary registers in a given evaluation (recursion) path.
    count_temps: Rc<RefCell<u8>>,
}

impl<'uref, 'ukey, 'umd, 'temp, 'local> Drop for TempSymtable<'uref, 'ukey, 'umd, 'temp, 'local> {
    fn drop(&mut self) {
        debug_assert_eq!(0, *self.next_temp.borrow(), "Unbalanced temp drops");
        self.symtable.count_temps = max(self.symtable.count_temps, *self.count_temps.borrow());
    }
}

impl<'uref, 'ukey, 'umd, 'temp, 'local> TempSymtable<'uref, 'ukey, 'umd, 'temp, 'local> {
    /// Creates a new temporary symbol table from a `local` table.
    fn new(symtable: &'temp mut LocalSymtable<'uref, 'ukey, 'umd, 'local>) -> Self {
        Self {
            symtable,
            next_temp: Rc::from(RefCell::from(0)),
            count_temps: Rc::from(RefCell::from(0)),
        }
    }

    /// Gets a variable by its `vref`, looking for it in the local and global scopes.
    pub(crate) fn get_local_or_global(&self, vref: &VarRef) -> Result<(Register, ExprType)> {
        self.symtable.get_local_or_global(vref)
    }

    /// Gets a callable by its name `key`.
    pub(crate) fn get_callable(&self, key: &SymbolKey) -> Option<&CallableMetadata> {
        self.symtable.get_callable(key)
    }

    /// Enters a new temporary scope.
    pub(crate) fn temp_scope(&self) -> TempScope {
        let nlocals = u8::try_from(self.symtable.locals.len())
            .expect("Cannot have allocated more locals than u8");
        TempScope {
            nlocals,
            ntemps: 0,
            next_temp: self.next_temp.clone(),
            count_temps: self.count_temps.clone(),
        }
    }
}

/// A scope for temporary registers.
///
/// Temporaries are allocated on demand and are cleaned up when the scope is dropped.
pub(crate) struct TempScope {
    /// Number of local variables in the enclosing scope, used as the base for temporary registers.
    nlocals: u8,

    /// Number of temporary registers allocated by this scope.
    ntemps: u8,

    /// Shared counter for the next temporary register index to allocate.
    next_temp: Rc<RefCell<u8>>,

    /// Shared counter tracking the maximum number of temporary registers used.
    count_temps: Rc<RefCell<u8>>,
}

impl Drop for TempScope {
    fn drop(&mut self) {
        let mut next_temp = self.next_temp.borrow_mut();
        debug_assert!(*next_temp >= self.ntemps);
        *next_temp -= self.ntemps;
    }
}

impl TempScope {
    /// Returns the first register available for this scope.
    pub(crate) fn first(&mut self) -> Result<Register> {
        Register::local(self.nlocals).map_err(|_| Error::OutOfRegisters(RegisterScope::Temp))
    }

    /// Allocates a new temporary register.
    pub(crate) fn alloc(&mut self) -> Result<Register> {
        let temp;
        let new_next_temp;
        {
            let mut next_temp = self.next_temp.borrow_mut();
            temp = *next_temp;
            self.ntemps += 1;
            new_next_temp = match next_temp.checked_add(1) {
                Some(reg) => reg,
                None => return Err(Error::OutOfRegisters(RegisterScope::Temp)),
            };
            *next_temp = new_next_temp;
        }

        {
            let mut count_temps = self.count_temps.borrow_mut();
            *count_temps = max(*count_temps, new_next_temp);
        }

        match u8::try_from(usize::from(self.nlocals) + usize::from(temp)) {
            Ok(reg) => {
                Ok(Register::local(reg).map_err(|_| Error::OutOfRegisters(RegisterScope::Temp))?)
            }
            Err(_) => Err(Error::OutOfRegisters(RegisterScope::Temp)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CallableMetadataBuilder;

    #[test]
    fn test_symbol_key_case_insensitive() {
        assert_eq!(SymbolKey::from("foo"), SymbolKey::from("FOO"));
        assert_eq!(SymbolKey::from("Foo"), SymbolKey::from("fOo"));
    }

    #[test]
    fn test_symbol_key_display() {
        assert_eq!("FOO", format!("{}", SymbolKey::from("foo")));
    }

    #[test]
    fn test_global_put_and_get() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);

        let reg = global.put_global(SymbolKey::from("x"), ExprType::Integer)?;
        assert_eq!(Register::global(0).unwrap(), reg);

        let reg = global.put_global(SymbolKey::from("y"), ExprType::Text)?;
        assert_eq!(Register::global(1).unwrap(), reg);

        // Lookup with untyped ref succeeds.
        let (reg, etype) = global.get_global(&VarRef::new("x", None))?;
        assert_eq!(Register::global(0).unwrap(), reg);
        assert_eq!(ExprType::Integer, etype);

        // Lookup with matching typed ref succeeds.
        let (reg, etype) = global.get_global(&VarRef::new("y", Some(ExprType::Text)))?;
        assert_eq!(Register::global(1).unwrap(), reg);
        assert_eq!(ExprType::Text, etype);

        Ok(())
    }

    #[test]
    fn test_global_get_case_insensitive() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        global.put_global(SymbolKey::from("MyVar"), ExprType::Double)?;

        let (reg, etype) = global.get_global(&VarRef::new("myvar", None))?;
        assert_eq!(Register::global(0).unwrap(), reg);
        assert_eq!(ExprType::Double, etype);

        let (reg2, _) = global.get_global(&VarRef::new("MYVAR", None))?;
        assert_eq!(reg, reg2);
        Ok(())
    }

    #[test]
    fn test_global_get_incompatible_type() {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        global.put_global(SymbolKey::from("x"), ExprType::Integer).unwrap();

        let err = global.get_global(&VarRef::new("x", Some(ExprType::Text))).unwrap_err();
        assert_eq!("Incompatible type annotation in x$ reference", err.to_string());
    }

    #[test]
    fn test_global_get_undefined() {
        let upcalls = HashMap::default();
        let global = GlobalSymtable::new(&upcalls);

        let err = global.get_global(&VarRef::new("x", None)).unwrap_err();
        assert_eq!("Undefined global symbol x", err.to_string());
    }

    #[test]
    fn test_local_put_and_get() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        let mut local = global.enter_scope();

        let reg = local.put_local(SymbolKey::from("a"), ExprType::Boolean)?;
        assert_eq!(Register::local(0).unwrap(), reg);

        let reg = local.put_local(SymbolKey::from("b"), ExprType::Double)?;
        assert_eq!(Register::local(1).unwrap(), reg);

        let (reg, etype) = local.get_local_or_global(&VarRef::new("a", None))?;
        assert_eq!(Register::local(0).unwrap(), reg);
        assert_eq!(ExprType::Boolean, etype);

        Ok(())
    }

    #[test]
    fn test_local_shadows_global() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        global.put_global(SymbolKey::from("x"), ExprType::Integer)?;

        let mut local = global.enter_scope();
        local.put_local(SymbolKey::from("x"), ExprType::Text)?;

        let (reg, etype) = local.get_local_or_global(&VarRef::new("x", None))?;
        assert_eq!(Register::local(0).unwrap(), reg);
        assert_eq!(ExprType::Text, etype);

        Ok(())
    }

    #[test]
    fn test_local_falls_through_to_global() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        global.put_global(SymbolKey::from("g"), ExprType::Integer)?;

        let local = global.enter_scope();
        let (reg, etype) = local.get_local_or_global(&VarRef::new("g", None))?;
        assert_eq!(Register::global(0).unwrap(), reg);
        assert_eq!(ExprType::Integer, etype);

        Ok(())
    }

    #[test]
    fn test_local_get_undefined() {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        let local = global.enter_scope();

        let err = local.get_local_or_global(&VarRef::new("nope", None)).unwrap_err();
        assert_eq!("Undefined global symbol nope", err.to_string());
    }

    #[test]
    fn test_local_put_global_through_local() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        let mut local = global.enter_scope();

        let reg = local.put_global(SymbolKey::from("g"), ExprType::Integer)?;
        assert_eq!(Register::global(0).unwrap(), reg);

        // Should be visible from the local scope via fallthrough.
        let (reg, etype) = local.get_local_or_global(&VarRef::new("g", None))?;
        assert_eq!(Register::global(0).unwrap(), reg);
        assert_eq!(ExprType::Integer, etype);

        Ok(())
    }

    #[test]
    fn test_fixup_local_type() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        let mut local = global.enter_scope();

        local.put_local(SymbolKey::from("x"), ExprType::Integer)?;
        local.fixup_local_type(&VarRef::new("x", None), ExprType::Double)?;

        let (_, etype) = local.get_local_or_global(&VarRef::new("x", None))?;
        assert_eq!(ExprType::Double, etype);

        Ok(())
    }

    #[test]
    fn test_fixup_local_type_undefined() {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        let mut local = global.enter_scope();

        let err =
            local.fixup_local_type(&VarRef::new("nope", None), ExprType::Integer).unwrap_err();
        assert_eq!("Undefined local symbol nope", err.to_string());
    }

    #[test]
    fn test_leave_scope_counts_locals_only() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        let mut local = global.enter_scope();
        local.put_local(SymbolKey::from("a"), ExprType::Integer)?;
        local.put_local(SymbolKey::from("b"), ExprType::Integer)?;
        assert_eq!(2, local.leave_scope()?);
        Ok(())
    }

    #[test]
    fn test_leave_scope_counts_locals_and_temps() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        let mut local = global.enter_scope();
        local.put_local(SymbolKey::from("a"), ExprType::Integer)?;
        {
            let temp = local.frozen();
            let mut scope = temp.temp_scope();
            scope.alloc()?;
            scope.alloc()?;
        }
        assert_eq!(3, local.leave_scope()?);
        Ok(())
    }

    #[test]
    fn test_leave_scope_empty() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        let local = global.enter_scope();
        assert_eq!(0, local.leave_scope()?);
        Ok(())
    }

    #[test]
    fn test_define_and_get_user_callable() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);

        let md = CallableMetadataBuilder::new("MY_FUNC")
            .with_return_type(ExprType::Integer)
            .test_build();
        global.define_user_callable(&VarRef::new("my_func", None), md)?;

        let found = global.get_callable(&SymbolKey::from("my_func"));
        assert!(found.is_some());
        assert_eq!("MY_FUNC", found.unwrap().name());

        Ok(())
    }

    #[test]
    fn test_define_user_callable_already_defined() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);

        let md = CallableMetadataBuilder::new("DUP").test_build();
        global.define_user_callable(&VarRef::new("dup", None), md)?;

        let md2 = CallableMetadataBuilder::new("DUP").test_build();
        let err = global.define_user_callable(&VarRef::new("dup", None), md2).unwrap_err();
        assert_eq!("Cannot redefine dup", err.to_string());

        Ok(())
    }

    #[test]
    fn test_define_user_callable_via_local() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        let mut local = global.enter_scope();

        let md = CallableMetadataBuilder::new("SUB1").test_build();
        local.define_user_callable(&VarRef::new("sub1", None), md)?;

        let found = local.get_callable(&SymbolKey::from("sub1"));
        assert!(found.is_some());

        Ok(())
    }

    #[test]
    fn test_get_callable_upcall() {
        let key = SymbolKey::from("BUILTIN");
        let md = CallableMetadataBuilder::new("BUILTIN").test_build();
        let mut upcalls_map = HashMap::new();
        upcalls_map.insert(&key, &md);

        let global = GlobalSymtable::new(&upcalls_map);
        let found = global.get_callable(&SymbolKey::from("builtin"));
        assert!(found.is_some());
        assert_eq!("BUILTIN", found.unwrap().name());
    }

    #[test]
    fn test_user_callable_shadows_upcall() {
        let key = SymbolKey::from("SHARED");
        let builtin_md =
            CallableMetadataBuilder::new("SHARED").with_return_type(ExprType::Boolean).test_build();
        let mut upcalls_map = HashMap::new();
        upcalls_map.insert(&key, &builtin_md);

        let mut global = GlobalSymtable::new(&upcalls_map);
        let user_md =
            CallableMetadataBuilder::new("SHARED").with_return_type(ExprType::Integer).test_build();
        global.define_user_callable(&VarRef::new("shared", None), user_md).unwrap();

        let found = global.get_callable(&SymbolKey::from("shared")).unwrap();
        assert_eq!(Some(ExprType::Integer), found.return_type());
    }

    #[test]
    fn test_get_callable_not_found() {
        let upcalls = HashMap::default();
        let global = GlobalSymtable::new(&upcalls);
        assert!(global.get_callable(&SymbolKey::from("nope")).is_none());
    }

    #[test]
    fn test_temp_scope_first() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        let mut local = global.enter_scope();
        local.put_local(SymbolKey::from("a"), ExprType::Integer)?;
        local.put_local(SymbolKey::from("b"), ExprType::Integer)?;
        {
            let temp = local.frozen();
            let mut scope = temp.temp_scope();
            assert_eq!(Register::local(2).unwrap(), scope.first()?);
        }
        Ok(())
    }

    #[test]
    fn test_temp_scope_first_no_locals() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        let mut local = global.enter_scope();
        {
            let temp = local.frozen();
            let mut scope = temp.temp_scope();
            assert_eq!(Register::local(0).unwrap(), scope.first()?);
        }
        Ok(())
    }

    #[test]
    fn test_temp_scope() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        let mut local = global.enter_scope();
        assert_eq!(
            Register::local(0).unwrap(),
            local.put_local(SymbolKey::from("foo"), ExprType::Integer)?
        );
        {
            let temp = local.frozen();
            {
                let mut scope = temp.temp_scope();
                assert_eq!(Register::local(1).unwrap(), scope.alloc()?);
                {
                    let mut scope = temp.temp_scope();
                    assert_eq!(Register::local(2).unwrap(), scope.alloc()?);
                    assert_eq!(Register::local(3).unwrap(), scope.alloc()?);
                    assert_eq!(Register::local(4).unwrap(), scope.alloc()?);
                }
                {
                    let mut scope = temp.temp_scope();
                    assert_eq!(Register::local(2).unwrap(), scope.alloc()?);
                    assert_eq!(Register::local(3).unwrap(), scope.alloc()?);
                }
                assert_eq!(Register::local(2).unwrap(), scope.alloc()?);
            }
        }
        {
            let temp = local.frozen();
            {
                let mut scope = temp.temp_scope();
                assert_eq!(Register::local(1).unwrap(), scope.alloc()?);
            }
        }
        assert_eq!(5, local.leave_scope()?);
        Ok(())
    }

    #[test]
    fn test_temp_scope_lookup_vars() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        global.put_global(SymbolKey::from("g"), ExprType::Integer)?;
        let mut local = global.enter_scope();
        local.put_local(SymbolKey::from("l"), ExprType::Text)?;

        {
            let temp = local.frozen();

            let (reg, etype) = temp.get_local_or_global(&VarRef::new("l", None))?;
            assert_eq!(Register::local(0).unwrap(), reg);
            assert_eq!(ExprType::Text, etype);

            let (reg, etype) = temp.get_local_or_global(&VarRef::new("g", None))?;
            assert_eq!(Register::global(0).unwrap(), reg);
            assert_eq!(ExprType::Integer, etype);
        }

        Ok(())
    }

    #[test]
    fn test_temp_scope_lookup_callable() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);
        let md = CallableMetadataBuilder::new("FOO").test_build();
        global.define_user_callable(&VarRef::new("foo", None), md)?;

        let mut local = global.enter_scope();
        {
            let temp = local.frozen();
            assert!(temp.get_callable(&SymbolKey::from("foo")).is_some());
            assert!(temp.get_callable(&SymbolKey::from("nope")).is_none());
        }

        Ok(())
    }

    #[test]
    fn test_multiple_scopes_independent_locals() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(&upcalls);

        {
            let mut local = global.enter_scope();
            local.put_local(SymbolKey::from("x"), ExprType::Integer)?;
            assert_eq!(1, local.leave_scope()?);
        }

        {
            let mut local = global.enter_scope();
            // "x" should not exist in this new scope.
            let err = local.get_local_or_global(&VarRef::new("x", None)).unwrap_err();
            assert_eq!("Undefined global symbol x", err.to_string());

            let reg = local.put_local(SymbolKey::from("y"), ExprType::Double)?;
            assert_eq!(Register::local(0).unwrap(), reg);
            assert_eq!(1, local.leave_scope()?);
        }

        Ok(())
    }
}
