// EndBASIC
// Copyright 2026 Julio Merino
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

//! Symbol table for EndBASIC compilation.

use crate::ast::{ExprType, VarRef};
use crate::bytecode::{Register, RegisterScope};
use crate::compiler::ids::HashMapWithIds;
use crate::{CallableMetadata, bytecode};
use std::cell::Cell;
use std::cell::RefCell;
use std::cmp::max;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;
use std::rc::Rc;

/// Information about an array tracked in the symbol table.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(super) struct ArrayInfo {
    /// Element type of the array.
    pub(super) subtype: ExprType,

    /// Number of dimensions.
    pub(super) ndims: usize,
}

/// Prototype for a variable-like symbol (scalar or array).
#[derive(Clone, Copy, Debug, PartialEq)]
pub(super) enum SymbolPrototype {
    /// An array with the given element type and number of dimensions.
    Array(ArrayInfo),

    /// A scalar variable of the given type.
    Scalar(ExprType),
}

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

/// Gets the register and prototype of a local or global variable if it already exists.
fn get_var<MKR>(
    vref: &VarRef,
    table: &HashMapWithIds<SymbolKey, SymbolPrototype, u8>,
    make_register: MKR,
    scope: RegisterScope,
) -> Result<(Register, SymbolPrototype)>
where
    MKR: FnOnce(u8) -> std::result::Result<Register, bytecode::OutOfRegistersError>,
{
    let key = SymbolKey::from(&vref.name);
    match table.get(&key) {
        Some((SymbolPrototype::Array(info), reg)) => {
            if !vref.accepts(info.subtype) {
                return Err(Error::IncompatibleTypeAnnotationInReference(vref.clone()));
            }

            let reg = make_register(reg).map_err(|_| Error::OutOfRegisters(scope))?;
            Ok((reg, SymbolPrototype::Array(*info)))
        }

        Some((SymbolPrototype::Scalar(etype), reg)) => {
            if !vref.accepts(*etype) {
                return Err(Error::IncompatibleTypeAnnotationInReference(vref.clone()));
            }

            let reg = make_register(reg).map_err(|_| Error::OutOfRegisters(scope))?;
            Ok((reg, SymbolPrototype::Scalar(*etype)))
        }

        None => Err(Error::UndefinedSymbol(vref.clone(), scope)),
    }
}

/// Defines a new local or global variable (or array) and assigns a register to it.
///
/// Panics if the symbol already exists.
fn put_var<MKR>(
    key: SymbolKey,
    proto: SymbolPrototype,
    table: &mut HashMapWithIds<SymbolKey, SymbolPrototype, u8>,
    make_register: MKR,
    scope: RegisterScope,
) -> Result<Register>
where
    MKR: FnOnce(u8) -> std::result::Result<Register, bytecode::OutOfRegistersError>,
{
    match table.insert(key, proto) {
        Some((None, reg)) => Ok(make_register(reg).map_err(|_| Error::OutOfRegisters(scope))?),

        Some((Some(_old_proto), _reg)) => {
            unreachable!("Cannot redefine symbol; caller must check for presence first");
        }

        None => Err(Error::OutOfRegisters(scope)),
    }
}

/// Representation of the symbol table for global symbols.
///
/// Globals are variables and callables that are visible from any scope.
pub(crate) struct GlobalSymtable {
    /// Map of global variable names to their prototypes and assigned registers.
    globals: HashMapWithIds<SymbolKey, SymbolPrototype, u8>,

    /// Reference to the built-in callable metadata provided by the runtime.
    upcalls: HashMap<SymbolKey, Rc<CallableMetadata>>,

    /// Map of user-defined callable names to their metadata.
    user_callables: HashMap<SymbolKey, Rc<CallableMetadata>>,
}

impl GlobalSymtable {
    /// Creates a new global symbol table that knows about the given `upcalls`.
    pub(crate) fn new(upcalls: HashMap<SymbolKey, Rc<CallableMetadata>>) -> Self {
        Self { globals: HashMapWithIds::default(), upcalls, user_callables: HashMap::default() }
    }

    /// Enters a new local scope.
    pub(crate) fn enter_scope(&mut self) -> LocalSymtable<'_> {
        LocalSymtable::new(self)
    }

    /// Gets a global symbol by its `vref`, returning its register and prototype.
    pub(crate) fn get_global(&self, vref: &VarRef) -> Result<(Register, SymbolPrototype)> {
        get_var(vref, &self.globals, Register::global, RegisterScope::Global)
    }

    /// Creates a new global symbol `key` with `proto`.
    pub(crate) fn put_global(
        &mut self,
        key: SymbolKey,
        proto: SymbolPrototype,
    ) -> Result<Register> {
        put_var(key, proto, &mut self.globals, Register::global, RegisterScope::Global)
    }

    /// Returns true if a global variable `key` is already defined.
    pub(crate) fn contains_global(&self, key: &SymbolKey) -> bool {
        self.globals.get(key).is_some()
    }

    /// Iterates over all global variables, yielding `(key, prototype, register_index)` tuples.
    pub(crate) fn iter_globals(
        &self,
    ) -> impl Iterator<Item = (&SymbolKey, SymbolPrototype, u8)> + '_ {
        self.globals.iter().map(|(k, v, i)| (k, *v, i))
    }

    /// Defines a new user-defined `vref` callable with `md` metadata.
    pub(crate) fn define_user_callable(
        &mut self,
        vref: &VarRef,
        md: Rc<CallableMetadata>,
    ) -> Result<()> {
        let key = SymbolKey::from(&vref.name);
        if self.globals.get(&key).is_some() {
            return Err(Error::AlreadyDefined(vref.clone()));
        }
        let previous = self.user_callables.insert(key, md);
        if previous.is_none() { Ok(()) } else { Err(Error::AlreadyDefined(vref.clone())) }
    }

    /// Gets a callable by its name `key`.
    pub(crate) fn get_callable(&self, key: &SymbolKey) -> Option<Rc<CallableMetadata>> {
        self.user_callables.get(key).or(self.upcalls.get(key)).cloned()
    }
}

/// Representation of the symbol table for a local scope.
///
/// A local scope can see all global symbols and defines its own symbols, which can shadow the
/// global ones.
pub(crate) struct LocalSymtable<'a> {
    /// Reference to the parent global symbol table.
    symtable: &'a mut GlobalSymtable,

    /// Map of local variable names to their prototypes and assigned registers.
    locals: HashMapWithIds<SymbolKey, SymbolPrototype, u8>,

    /// Maximum number of allocated temporary registers in all possible evaluation scopes created
    /// by this local symtable.  This is used to determine the size of the scope for register
    /// allocation purposes at runtime.
    count_temps: u8,

    /// Number of reserved temporary registers that are active outside of `TempScope`.
    active_temps: Rc<Cell<u8>>,
}

impl<'a> LocalSymtable<'a> {
    /// Creates a new local symbol table within the context of a global `symtable`.
    fn new(symtable: &'a mut GlobalSymtable) -> Self {
        Self {
            symtable,
            locals: HashMapWithIds::default(),
            count_temps: 0,
            active_temps: Rc::from(Cell::new(0)),
        }
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
        md: Rc<CallableMetadata>,
    ) -> Result<()> {
        self.symtable.define_user_callable(vref, md)
    }

    /// Freezes this table to get a `TempSymtable` that can be used to compile expressions.
    pub(crate) fn frozen(&mut self) -> TempSymtable<'_, 'a> {
        TempSymtable::new(self)
    }

    /// Reserves one temporary register for the duration of `f`.
    pub(crate) fn with_reserved_temp<T, E, ME, F>(
        &mut self,
        map_error: ME,
        f: F,
    ) -> std::result::Result<T, E>
    where
        ME: Fn(Error) -> E,
        F: FnOnce(Register, &mut TempSymtable<'_, 'a>) -> std::result::Result<T, E>,
    {
        struct TempReservationGuard {
            active_temps: Rc<Cell<u8>>,
        }

        impl Drop for TempReservationGuard {
            fn drop(&mut self) {
                let active_temps = self.active_temps.get();
                debug_assert!(active_temps > 0);
                self.active_temps.set(active_temps - 1);
            }
        }

        let nlocals = u8::try_from(self.locals.len())
            .map_err(|_| map_error(Error::OutOfRegisters(RegisterScope::Local)))?;
        let first_temp = self.active_temps.get();
        let new_active_temps = first_temp
            .checked_add(1)
            .ok_or(map_error(Error::OutOfRegisters(RegisterScope::Temp)))?;
        self.active_temps.set(new_active_temps);
        self.count_temps = max(self.count_temps, new_active_temps);
        let _guard = TempReservationGuard { active_temps: self.active_temps.clone() };

        let reg_idx = u8::try_from(usize::from(nlocals) + usize::from(first_temp))
            .map_err(|_| map_error(Error::OutOfRegisters(RegisterScope::Temp)))?;
        let reg = Register::local(reg_idx)
            .map_err(|_| map_error(Error::OutOfRegisters(RegisterScope::Temp)))?;

        let mut temp = self.frozen();
        f(reg, &mut temp)
    }

    /// Creates a new global symbol `key` with `proto` via the parent global symbol table.
    pub(crate) fn put_global(
        &mut self,
        key: SymbolKey,
        proto: SymbolPrototype,
    ) -> Result<Register> {
        self.symtable.put_global(key, proto)
    }

    /// Gets a symbol by its `vref`, looking for it in the local and global scopes.
    pub(crate) fn get_local_or_global(&self, vref: &VarRef) -> Result<(Register, SymbolPrototype)> {
        match get_var(vref, &self.locals, Register::local, RegisterScope::Local) {
            Ok(local) => Ok(local),
            Err(Error::UndefinedSymbol(..)) => self.symtable.get_global(vref),
            Err(e) => Err(e),
        }
    }

    /// Gets a callable by its name `key`.
    pub(crate) fn get_callable(&self, key: &SymbolKey) -> Option<Rc<CallableMetadata>> {
        self.symtable.get_callable(key)
    }

    /// Creates a new local symbol `key` with `proto`.
    pub(crate) fn put_local(&mut self, key: SymbolKey, proto: SymbolPrototype) -> Result<Register> {
        put_var(key, proto, &mut self.locals, Register::local, RegisterScope::Local)
    }

    /// Returns true if a local variable `key` is already defined.
    pub(crate) fn contains_local(&self, key: &SymbolKey) -> bool {
        self.locals.get(key).is_some()
    }

    /// Returns true if a global variable `key` is already defined.
    pub(crate) fn contains_global(&self, key: &SymbolKey) -> bool {
        self.symtable.contains_global(key)
    }

    /// Changes the type of an existing local variable `vref` to `new_etype`.
    ///
    /// This is used for type inference on first assignment.
    pub(crate) fn fixup_local_type(&mut self, vref: &VarRef, new_etype: ExprType) -> Result<()> {
        let key = SymbolKey::from(&vref.name);
        // TODO: Verify reference type.
        match self.locals.get_mut(&key) {
            Some((SymbolPrototype::Array(_), _)) | None => {
                Err(Error::UndefinedSymbol(vref.clone(), RegisterScope::Local))
            }

            Some((SymbolPrototype::Scalar(etype), _reg)) => {
                *etype = new_etype;
                Ok(())
            }
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
pub(crate) struct TempSymtable<'temp, 'local> {
    /// Reference to the underlying local symbol table.
    symtable: &'temp mut LocalSymtable<'local>,

    /// Number of temporary registers that were already reserved on creation.
    base_temp: u8,

    /// Index of the next temporary register to allocate.
    next_temp: Rc<RefCell<u8>>,

    /// Maximum number of allocated temporary registers in a given evaluation (recursion) path.
    count_temps: Rc<RefCell<u8>>,
}

impl<'temp, 'local> Drop for TempSymtable<'temp, 'local> {
    fn drop(&mut self) {
        debug_assert_eq!(self.base_temp, *self.next_temp.borrow(), "Unbalanced temp drops");
        self.symtable.count_temps = max(self.symtable.count_temps, *self.count_temps.borrow());
    }
}

impl<'temp, 'local> TempSymtable<'temp, 'local> {
    /// Creates a new temporary symbol table from a `local` table.
    fn new(symtable: &'temp mut LocalSymtable<'local>) -> Self {
        let base_temp = symtable.active_temps.get();
        Self {
            symtable,
            base_temp,
            next_temp: Rc::from(RefCell::from(base_temp)),
            count_temps: Rc::from(RefCell::from(base_temp)),
        }
    }

    /// Gets a symbol by its `vref`, looking for it in the local and global scopes.
    pub(crate) fn get_local_or_global(&self, vref: &VarRef) -> Result<(Register, SymbolPrototype)> {
        self.symtable.get_local_or_global(vref)
    }

    /// Gets a callable by its name `key`.
    pub(crate) fn get_callable(&self, key: &SymbolKey) -> Option<Rc<CallableMetadata>> {
        self.symtable.get_callable(key)
    }

    /// Enters a new temporary scope.
    pub(crate) fn temp_scope(&self) -> TempScope {
        let nlocals = u8::try_from(self.symtable.locals.len())
            .expect("Cannot have allocated more locals than u8");
        TempScope {
            base_temp: *self.next_temp.borrow(),
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
    /// Number of temporary registers that were already active on scope creation.
    base_temp: u8,

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
        let reg = u8::try_from(usize::from(self.nlocals) + usize::from(self.base_temp))
            .map_err(|_| Error::OutOfRegisters(RegisterScope::Temp))?;
        Register::local(reg).map_err(|_| Error::OutOfRegisters(RegisterScope::Temp))
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
        let mut global = GlobalSymtable::new(upcalls);

        let reg =
            global.put_global(SymbolKey::from("x"), SymbolPrototype::Scalar(ExprType::Integer))?;
        assert_eq!(Register::global(0).unwrap(), reg);

        let reg =
            global.put_global(SymbolKey::from("y"), SymbolPrototype::Scalar(ExprType::Text))?;
        assert_eq!(Register::global(1).unwrap(), reg);

        // Lookup with untyped ref succeeds.
        let (reg, proto) = global.get_global(&VarRef::new("x", None))?;
        assert_eq!(Register::global(0).unwrap(), reg);
        assert_eq!(SymbolPrototype::Scalar(ExprType::Integer), proto);

        // Lookup with matching typed ref succeeds.
        let (reg, proto) = global.get_global(&VarRef::new("y", Some(ExprType::Text)))?;
        assert_eq!(Register::global(1).unwrap(), reg);
        assert_eq!(SymbolPrototype::Scalar(ExprType::Text), proto);

        Ok(())
    }

    #[test]
    fn test_global_get_case_insensitive() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        global.put_global(SymbolKey::from("MyVar"), SymbolPrototype::Scalar(ExprType::Double))?;

        let (reg, proto) = global.get_global(&VarRef::new("myvar", None))?;
        assert_eq!(Register::global(0).unwrap(), reg);
        assert_eq!(SymbolPrototype::Scalar(ExprType::Double), proto);

        let (reg2, _) = global.get_global(&VarRef::new("MYVAR", None))?;
        assert_eq!(reg, reg2);
        Ok(())
    }

    #[test]
    fn test_global_get_incompatible_type() {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        global
            .put_global(SymbolKey::from("x"), SymbolPrototype::Scalar(ExprType::Integer))
            .unwrap();

        let err = global.get_global(&VarRef::new("x", Some(ExprType::Text))).unwrap_err();
        assert_eq!("Incompatible type annotation in x$ reference", err.to_string());
    }

    #[test]
    fn test_global_get_undefined() {
        let upcalls = HashMap::default();
        let global = GlobalSymtable::new(upcalls);

        let err = global.get_global(&VarRef::new("x", None)).unwrap_err();
        assert_eq!("Undefined global symbol x", err.to_string());
    }

    #[test]
    fn test_local_put_and_get() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        let mut local = global.enter_scope();

        let reg =
            local.put_local(SymbolKey::from("a"), SymbolPrototype::Scalar(ExprType::Boolean))?;
        assert_eq!(Register::local(0).unwrap(), reg);

        let reg =
            local.put_local(SymbolKey::from("b"), SymbolPrototype::Scalar(ExprType::Double))?;
        assert_eq!(Register::local(1).unwrap(), reg);

        let (reg, proto) = local.get_local_or_global(&VarRef::new("a", None))?;
        assert_eq!(Register::local(0).unwrap(), reg);
        assert_eq!(SymbolPrototype::Scalar(ExprType::Boolean), proto);

        Ok(())
    }

    #[test]
    fn test_local_shadows_global() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        global.put_global(SymbolKey::from("x"), SymbolPrototype::Scalar(ExprType::Integer))?;

        let mut local = global.enter_scope();
        local.put_local(SymbolKey::from("x"), SymbolPrototype::Scalar(ExprType::Text))?;

        let (reg, proto) = local.get_local_or_global(&VarRef::new("x", None))?;
        assert_eq!(Register::local(0).unwrap(), reg);
        assert_eq!(SymbolPrototype::Scalar(ExprType::Text), proto);

        Ok(())
    }

    #[test]
    fn test_local_falls_through_to_global() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        global.put_global(SymbolKey::from("g"), SymbolPrototype::Scalar(ExprType::Integer))?;

        let local = global.enter_scope();
        let (reg, proto) = local.get_local_or_global(&VarRef::new("g", None))?;
        assert_eq!(Register::global(0).unwrap(), reg);
        assert_eq!(SymbolPrototype::Scalar(ExprType::Integer), proto);

        Ok(())
    }

    #[test]
    fn test_local_get_undefined() {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        let local = global.enter_scope();

        let err = local.get_local_or_global(&VarRef::new("nope", None)).unwrap_err();
        assert_eq!("Undefined global symbol nope", err.to_string());
    }

    #[test]
    fn test_local_put_global_through_local() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        let mut local = global.enter_scope();

        let reg =
            local.put_global(SymbolKey::from("g"), SymbolPrototype::Scalar(ExprType::Integer))?;
        assert_eq!(Register::global(0).unwrap(), reg);

        // Should be visible from the local scope via fallthrough.
        let (reg, proto) = local.get_local_or_global(&VarRef::new("g", None))?;
        assert_eq!(Register::global(0).unwrap(), reg);
        assert_eq!(SymbolPrototype::Scalar(ExprType::Integer), proto);

        Ok(())
    }

    #[test]
    fn test_fixup_local_type() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        let mut local = global.enter_scope();

        local.put_local(SymbolKey::from("x"), SymbolPrototype::Scalar(ExprType::Integer))?;
        local.fixup_local_type(&VarRef::new("x", None), ExprType::Double)?;

        let (_, proto) = local.get_local_or_global(&VarRef::new("x", None))?;
        assert_eq!(SymbolPrototype::Scalar(ExprType::Double), proto);

        Ok(())
    }

    #[test]
    fn test_fixup_local_type_undefined() {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        let mut local = global.enter_scope();

        let err =
            local.fixup_local_type(&VarRef::new("nope", None), ExprType::Integer).unwrap_err();
        assert_eq!("Undefined local symbol nope", err.to_string());
    }

    #[test]
    fn test_leave_scope_counts_locals_only() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        let mut local = global.enter_scope();
        local.put_local(SymbolKey::from("a"), SymbolPrototype::Scalar(ExprType::Integer))?;
        local.put_local(SymbolKey::from("b"), SymbolPrototype::Scalar(ExprType::Integer))?;
        assert_eq!(2, local.leave_scope()?);
        Ok(())
    }

    #[test]
    fn test_leave_scope_counts_locals_and_temps() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        let mut local = global.enter_scope();
        local.put_local(SymbolKey::from("a"), SymbolPrototype::Scalar(ExprType::Integer))?;
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
        let mut global = GlobalSymtable::new(upcalls);
        let local = global.enter_scope();
        assert_eq!(0, local.leave_scope()?);
        Ok(())
    }

    #[test]
    fn test_define_and_get_user_callable() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);

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
        let mut global = GlobalSymtable::new(upcalls);

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
        let mut global = GlobalSymtable::new(upcalls);
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
        upcalls_map.insert(key, md);

        let global = GlobalSymtable::new(upcalls_map);
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
        upcalls_map.insert(key, builtin_md);

        let mut global = GlobalSymtable::new(upcalls_map);
        let user_md =
            CallableMetadataBuilder::new("SHARED").with_return_type(ExprType::Integer).test_build();
        global.define_user_callable(&VarRef::new("shared", None), user_md).unwrap();

        let found = global.get_callable(&SymbolKey::from("shared")).unwrap();
        assert_eq!(Some(ExprType::Integer), found.return_type());
    }

    #[test]
    fn test_get_callable_not_found() {
        let upcalls = HashMap::default();
        let global = GlobalSymtable::new(upcalls);
        assert!(global.get_callable(&SymbolKey::from("nope")).is_none());
    }

    #[test]
    fn test_temp_scope_first() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        let mut local = global.enter_scope();
        local.put_local(SymbolKey::from("a"), SymbolPrototype::Scalar(ExprType::Integer))?;
        local.put_local(SymbolKey::from("b"), SymbolPrototype::Scalar(ExprType::Integer))?;
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
        let mut global = GlobalSymtable::new(upcalls);
        let mut local = global.enter_scope();
        {
            let temp = local.frozen();
            let mut scope = temp.temp_scope();
            assert_eq!(Register::local(0).unwrap(), scope.first()?);
        }
        Ok(())
    }

    #[test]
    fn test_temp_scope_first_with_outer_allocation() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        let mut local = global.enter_scope();
        local.put_local(SymbolKey::from("a"), SymbolPrototype::Scalar(ExprType::Integer))?;
        {
            let temp = local.frozen();
            let mut outer = temp.temp_scope();
            assert_eq!(Register::local(1).unwrap(), outer.alloc()?);

            let mut inner = temp.temp_scope();
            assert_eq!(Register::local(2).unwrap(), inner.first()?);
        }
        Ok(())
    }

    #[test]
    fn test_temp_scope() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        let mut local = global.enter_scope();
        assert_eq!(
            Register::local(0).unwrap(),
            local.put_local(SymbolKey::from("foo"), SymbolPrototype::Scalar(ExprType::Integer))?
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
    fn test_with_reserved_temp_register_index() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        let mut local = global.enter_scope();
        local.put_local(SymbolKey::from("a"), SymbolPrototype::Scalar(ExprType::Integer))?;
        local.put_local(SymbolKey::from("b"), SymbolPrototype::Scalar(ExprType::Integer))?;

        local.with_reserved_temp(
            |e| e,
            |reg, _| {
                assert_eq!(Register::local(2).unwrap(), reg);
                Ok(())
            },
        )?;

        assert_eq!(3, local.leave_scope()?);
        Ok(())
    }

    #[test]
    fn test_with_reserved_temp_shifts_temp_scope_base() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        let mut local = global.enter_scope();
        local.put_local(SymbolKey::from("a"), SymbolPrototype::Scalar(ExprType::Integer))?;

        local.with_reserved_temp(
            |e| e,
            |reserved, temp| {
                assert_eq!(Register::local(1).unwrap(), reserved);
                let mut scope = temp.temp_scope();
                assert_eq!(Register::local(2).unwrap(), scope.alloc()?);
                Ok(())
            },
        )?;

        assert_eq!(3, local.leave_scope()?);
        Ok(())
    }

    #[test]
    fn test_with_reserved_temp_released_after_error() {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        let mut local = global.enter_scope();

        let err = local
            .with_reserved_temp(
                |e| e,
                |_, _| Err::<(), Error>(Error::OutOfRegisters(RegisterScope::Temp)),
            )
            .unwrap_err();
        assert_eq!("Out of temp registers", err.to_string());

        local
            .with_reserved_temp(
                |e| e,
                |reg, _| {
                    assert_eq!(Register::local(0).unwrap(), reg);
                    Ok(())
                },
            )
            .unwrap();
    }

    #[test]
    fn test_temp_scope_lookup_vars() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        global.put_global(SymbolKey::from("g"), SymbolPrototype::Scalar(ExprType::Integer))?;
        let mut local = global.enter_scope();
        local.put_local(SymbolKey::from("l"), SymbolPrototype::Scalar(ExprType::Text))?;

        {
            let temp = local.frozen();

            let (reg, proto) = temp.get_local_or_global(&VarRef::new("l", None))?;
            assert_eq!(Register::local(0).unwrap(), reg);
            assert_eq!(SymbolPrototype::Scalar(ExprType::Text), proto);

            let (reg, proto) = temp.get_local_or_global(&VarRef::new("g", None))?;
            assert_eq!(Register::global(0).unwrap(), reg);
            assert_eq!(SymbolPrototype::Scalar(ExprType::Integer), proto);
        }

        Ok(())
    }

    #[test]
    fn test_temp_scope_lookup_callable() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
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
        let mut global = GlobalSymtable::new(upcalls);

        {
            let mut local = global.enter_scope();
            local.put_local(SymbolKey::from("x"), SymbolPrototype::Scalar(ExprType::Integer))?;
            assert_eq!(1, local.leave_scope()?);
        }

        {
            let mut local = global.enter_scope();
            // "x" should not exist in this new scope.
            let err = local.get_local_or_global(&VarRef::new("x", None)).unwrap_err();
            assert_eq!("Undefined global symbol x", err.to_string());

            let reg =
                local.put_local(SymbolKey::from("y"), SymbolPrototype::Scalar(ExprType::Double))?;
            assert_eq!(Register::local(0).unwrap(), reg);
            assert_eq!(1, local.leave_scope()?);
        }

        Ok(())
    }

    #[test]
    fn test_global_put_and_get_array() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);

        let reg = global.put_global(
            SymbolKey::from("arr"),
            SymbolPrototype::Array(ArrayInfo { subtype: ExprType::Integer, ndims: 2 }),
        )?;
        assert_eq!(Register::global(0).unwrap(), reg);

        let (got_reg, proto) = global.get_global(&VarRef::new("arr", None)).unwrap();
        assert_eq!(Register::global(0).unwrap(), got_reg);
        let SymbolPrototype::Array(info) = proto else { panic!("Expected Array prototype") };
        assert_eq!(ExprType::Integer, info.subtype);
        assert_eq!(2, info.ndims);

        Ok(())
    }

    #[test]
    fn test_local_put_and_get_array() -> Result<()> {
        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        let mut local = global.enter_scope();

        let reg = local.put_local(
            SymbolKey::from("arr"),
            SymbolPrototype::Array(ArrayInfo { subtype: ExprType::Double, ndims: 1 }),
        )?;
        assert_eq!(Register::local(0).unwrap(), reg);

        let (got_reg, proto) = local.get_local_or_global(&VarRef::new("arr", None)).unwrap();
        assert_eq!(Register::local(0).unwrap(), got_reg);
        let SymbolPrototype::Array(info) = proto else { panic!("Expected Array prototype") };
        assert_eq!(ExprType::Double, info.subtype);
        assert_eq!(1, info.ndims);

        Ok(())
    }
}
