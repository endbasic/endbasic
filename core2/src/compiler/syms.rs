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
use crate::compiler::HashMapWithIds;
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

    #[error("Out of {0} registers")]
    OutOfRegisters(RegisterScope),

    #[error("Undefined {1} symbol {0}")]
    UndefinedSymbol(VarRef, RegisterScope),
}

type Result<T> = std::result::Result<T, Error>;

/// The key of a symbol in the symbols table.
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

#[derive(Default)]
pub(crate) struct GlobalSymtable {
    globals: HashMapWithIds<SymbolKey, ExprType, u8>,
    user_callables: HashMap<SymbolKey, (Option<ExprType>, Vec<VarRef>)>,
}

impl GlobalSymtable {
    pub(crate) fn enter_scope(&mut self) -> LocalSymtable<'_> {
        LocalSymtable::new(self)
    }

    pub(crate) fn get_global(&self, vref: &VarRef) -> Result<(Register, ExprType)> {
        let key = SymbolKey::from(&vref.name);
        // TODO: Verify reference type.
        match self.globals.get(&key) {
            Some((etype, reg)) => {
                let reg = Register::global(reg)
                    .map_err(|_| Error::OutOfRegisters(RegisterScope::Global))?;
                Ok((reg, *etype))
            }
            None => Err(Error::UndefinedSymbol(vref.clone(), RegisterScope::Global)),
        }
    }

    pub(crate) fn put_global(&mut self, vref: &VarRef) -> Result<Register> {
        let key = SymbolKey::from(&vref.name);
        let etype = vref.ref_type.unwrap_or(ExprType::Integer);
        match self.globals.insert(key, etype) {
            Some((_previous, reg)) => {
                // DO NOT SUBMIT: Verify etype match.
                // DO NOT SUBMIT: Verify double insert (redefinition).
                let reg = Register::global(reg)
                    .map_err(|_| Error::OutOfRegisters(RegisterScope::Global))?;
                Ok(reg)
            }
            None => Err(Error::OutOfRegisters(RegisterScope::Global)),
        }
    }

    pub(crate) fn fixup_global_type(&mut self, vref: &VarRef, new_etype: ExprType) -> Result<()> {
        let key = SymbolKey::from(&vref.name);
        // TODO: Verify reference type.
        match self.globals.get_mut(&key) {
            Some((etype, _reg)) => {
                *etype = new_etype;
                Ok(())
            }
            None => Err(Error::UndefinedSymbol(vref.clone(), RegisterScope::Global)),
        }
    }

    pub(crate) fn define_user_callable(
        &mut self,
        vref: &VarRef,
        params: Vec<VarRef>,
    ) -> Result<()> {
        let key = SymbolKey::from(&vref.name);
        let previous = self.user_callables.insert(key, (vref.ref_type, params));
        if previous.is_none() { Ok(()) } else { Err(Error::AlreadyDefined(vref.clone())) }
    }

    pub(crate) fn get_user_callable(
        &self,
        key: &SymbolKey,
    ) -> Option<&(Option<ExprType>, Vec<VarRef>)> {
        self.user_callables.get(&key)
    }
}

pub(crate) struct LocalSymtable<'a> {
    symtable: &'a mut GlobalSymtable,
    locals: HashMapWithIds<SymbolKey, ExprType, u8>,

    /// Maximum number of allocated temporary registers in all possible evaluation scopes created
    /// by this local symtable.  This is used to determine the size of the scope for register
    /// allocation purposes at runtime.
    count_temps: u8,
}

impl<'a> LocalSymtable<'a> {
    fn new(symtable: &'a mut GlobalSymtable) -> Self {
        Self { symtable, locals: HashMapWithIds::default(), count_temps: 0 }
    }

    pub(crate) fn leave_scope(self) -> Result<u8> {
        match u8::try_from(self.locals.len() + usize::from(self.count_temps)) {
            Ok(nregs) => Ok(nregs),
            Err(_) => Err(Error::OutOfRegisters(RegisterScope::Local)),
        }
    }

    pub(crate) fn define_user_callable(
        &mut self,
        vref: &VarRef,
        params: Vec<VarRef>,
    ) -> Result<()> {
        self.symtable.define_user_callable(vref, params)
    }

    pub(crate) fn frozen(&mut self) -> TempSymtable<'_, 'a> {
        TempSymtable::new(self)
    }

    pub(crate) fn get_global(&self, vref: &VarRef) -> Result<(Register, ExprType)> {
        self.symtable.get_global(vref)
    }

    pub(crate) fn put_global(&mut self, vref: &VarRef) -> Result<Register> {
        self.symtable.put_global(vref)
    }

    pub(crate) fn fixup_global_type(&mut self, vref: &VarRef, new_etype: ExprType) -> Result<()> {
        self.symtable.fixup_global_type(vref, new_etype)
    }

    fn get_local(&self, vref: &VarRef) -> Result<(Register, ExprType)> {
        let key = SymbolKey::from(&vref.name);
        // TODO: Verify reference type.
        match self.locals.get(&key) {
            Some((etype, reg)) => {
                let reg = Register::local(reg)
                    .map_err(|_| Error::OutOfRegisters(RegisterScope::Local))?;
                Ok((reg, *etype))
            }
            None => Err(Error::UndefinedSymbol(vref.clone(), RegisterScope::Local)),
        }
    }

    pub(crate) fn get_local_or_global(&self, vref: &VarRef) -> Result<(Register, ExprType)> {
        match self.symtable.get_global(vref) {
            Ok(global) => Ok(global),
            Err(Error::UndefinedSymbol(..)) => self.get_local(vref),
            Err(e) => Err(e),
        }
    }

    pub(crate) fn put_local(&mut self, vref: &VarRef) -> Result<Register> {
        let key = SymbolKey::from(&vref.name);
        let etype = vref.ref_type.unwrap_or(ExprType::Integer);
        match self.locals.insert(key, etype) {
            Some((_previous, reg)) => {
                // DO NOT SUBMIT: Verify etype match.
                // DO NOT SUBMIT: Verify double insert (redefinition).
                let reg = Register::local(reg)
                    .map_err(|_| Error::OutOfRegisters(RegisterScope::Local))?;
                Ok(reg)
            }
            None => Err(Error::OutOfRegisters(RegisterScope::Local)),
        }
    }

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
pub(crate) struct TempSymtable<'temp, 'local> {
    symtable: &'temp mut LocalSymtable<'local>,

    /// Index of the next temporary register to allocate.
    next_temp: Rc<RefCell<u8>>,

    /// Maximum number of allocated temporary registers in a given evaluation (recursion) path.
    count_temps: Rc<RefCell<u8>>,
}

impl<'temp, 'local> Drop for TempSymtable<'temp, 'local> {
    fn drop(&mut self) {
        debug_assert_eq!(0, *self.next_temp.borrow(), "Unbalanced temp drops");
        self.symtable.count_temps = max(self.symtable.count_temps, *self.count_temps.borrow());
    }
}

impl<'temp, 'local> TempSymtable<'temp, 'local> {
    fn new(symtable: &'temp mut LocalSymtable<'local>) -> Self {
        Self {
            symtable,
            next_temp: Rc::from(RefCell::from(0)),
            count_temps: Rc::from(RefCell::from(0)),
        }
    }

    pub(crate) fn get_local_or_global(&self, vref: &VarRef) -> Result<(Register, ExprType)> {
        self.symtable.get_local_or_global(vref)
    }

    pub(crate) fn get_user_callable(
        &self,
        key: &SymbolKey,
    ) -> Option<&(Option<ExprType>, Vec<VarRef>)> {
        self.symtable.symtable.get_user_callable(key)
    }

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

pub(crate) struct TempScope {
    nlocals: u8,
    ntemps: u8,
    next_temp: Rc<RefCell<u8>>,
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
    pub(crate) fn first(&mut self) -> Result<Register> {
        Ok(Register::local(self.nlocals).map_err(|_| Error::OutOfRegisters(RegisterScope::Temp))?)
    }

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

    // DO NOT SUBMIT: We definitely need more unit tests here.

    #[test]
    fn test_temp_scope() -> Result<()> {
        let mut global = GlobalSymtable::default();
        let mut local = global.enter_scope();
        debug_assert_eq!(Register::local(0).unwrap(), local.put_local(&VarRef::new("foo", None))?);
        {
            let temp = local.frozen();
            {
                let mut scope = temp.temp_scope();
                debug_assert_eq!(Register::local(1).unwrap(), scope.alloc()?);
                {
                    let mut scope = temp.temp_scope();
                    debug_assert_eq!(Register::local(2).unwrap(), scope.alloc()?);
                    debug_assert_eq!(Register::local(3).unwrap(), scope.alloc()?);
                    debug_assert_eq!(Register::local(4).unwrap(), scope.alloc()?);
                }
                {
                    let mut scope = temp.temp_scope();
                    debug_assert_eq!(Register::local(2).unwrap(), scope.alloc()?);
                    debug_assert_eq!(Register::local(3).unwrap(), scope.alloc()?);
                }
                debug_assert_eq!(Register::local(2).unwrap(), scope.alloc()?);
            }
        }
        {
            let temp = local.frozen();
            {
                let mut scope = temp.temp_scope();
                debug_assert_eq!(Register::local(1).unwrap(), scope.alloc()?);
            }
        }
        debug_assert_eq!(5, local.leave_scope()?);
        Ok(())
    }
}
