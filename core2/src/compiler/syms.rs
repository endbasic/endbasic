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
use crate::bytecode::Register;
use crate::compiler::{Error, HashMapWithIds, Result, map_bytecode_make_error};
use crate::reader::LineCol;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;

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
struct Temps {
    next: u8,
    count: u8,
}

impl Temps {
    fn alloc(&mut self) -> u8 {
        let reg = self.next;
        self.next = self.next.checked_add(1).expect(
            "Cannot run out of u8s before the caller detects we ran out of local registers",
        );
        self.count = self.count.checked_add(1).expect(
            "Cannot run out of u8s before the caller detects we ran out of local registers",
        );
        reg
    }

    fn dealloc(&mut self, count: u8) {
        self.next = self
            .next
            .checked_sub(count)
            .expect("Attempted to deallocate more temps than were allocated");
    }
}

#[derive(Default)]
pub(crate) struct Symtable {
    globals: HashMapWithIds<SymbolKey, ExprType, u8>,
    locals: Vec<(HashMapWithIds<SymbolKey, ExprType, u8>, Temps)>,
    user_callables: HashMap<SymbolKey, (Option<ExprType>, Vec<VarRef>)>,
}

impl Symtable {
    //pub(crate) fn global(
    //    &mut self,
    //    key: SymbolKey,
    //    etype: ExprType,
    //    pos: LineCol,
    //) -> Result<Register> {
    //    let Some((etype, reg)) = self.globals.get_or_put(key, etype) else {
    //        return Err(Error::OutOfRegisters(pos, "global"));
    //    };
    //    Register::global(*reg).map_err(|e| map_bytecode_error(pos, e))
    //}

    pub(crate) fn enter_scope(&mut self) {
        self.locals.push((HashMapWithIds::default(), Temps::default()));
    }

    pub(crate) fn leave_scope(&mut self) {
        self.locals.pop();
    }

    pub(crate) fn first_temp(&mut self, pos: LineCol) -> Result<Register> {
        let (locals, _temps) = self.locals.last_mut().unwrap();
        let reg = locals.len();
        Register::local(u8::try_from(reg).expect("DO NOT SUBMIT"))
            .map_err(|e| map_bytecode_make_error(pos, e))
    }

    pub(crate) fn alloc_temp(&mut self, pos: LineCol) -> Result<Register> {
        let (locals, temps) = self.locals.last_mut().unwrap();
        let reg = locals.len() + usize::from(temps.alloc());
        Register::local(u8::try_from(reg).expect("DO NOT SUBMIT"))
            .map_err(|e| map_bytecode_make_error(pos, e))
    }

    pub(crate) fn dealloc_temps(&mut self, count: u8) {
        let (_locals, temps) = self.locals.last_mut().unwrap();
        temps.dealloc(count);
    }

    pub(crate) fn frame_size(&self) -> u8 {
        let (locals, temps) = self.locals.last().unwrap();
        u8::try_from(locals.len() + usize::from(temps.count)).expect("DO NOT SUBMIT")
    }

    pub(crate) fn get_local(
        &mut self,
        vref: &VarRef,
        pos: LineCol,
    ) -> Result<(Register, ExprType)> {
        let key = SymbolKey::from(&vref.name);
        // TODO: Verify reference type.
        let locals = &mut self.locals.last_mut().unwrap().0;
        match locals.get(&key) {
            Some((etype, reg)) => {
                let reg = Register::local(reg).map_err(|e| map_bytecode_make_error(pos, e))?;
                Ok((reg, *etype))
            }
            None => Err(Error::UndefinedSymbol(pos, vref.clone(), "local")),
        }
    }

    pub(crate) fn put_local(&mut self, vref: &VarRef, pos: LineCol) -> Result<Register> {
        let key = SymbolKey::from(&vref.name);
        let etype = vref.ref_type.unwrap_or(ExprType::Integer);
        let locals = &mut self.locals.last_mut().unwrap().0;
        match locals.insert(key, etype) {
            Some((_previous, reg)) => {
                // DO NOT SUBMIT: Verify etype match.
                // DO NOT SUBMIT: Verify double insert (redefinition).
                let reg = Register::local(reg).map_err(|e| map_bytecode_make_error(pos, e))?;
                Ok(reg)
            }
            None => Err(Error::OutOfRegisters(pos.clone(), "global")),
        }
    }

    pub(crate) fn fixup_local_type(
        &mut self,
        vref: &VarRef,
        new_etype: ExprType,
        pos: LineCol,
    ) -> Result<()> {
        let key = SymbolKey::from(&vref.name);
        // TODO: Verify reference type.
        let locals = &mut self.locals.last_mut().unwrap().0;
        match locals.get_mut(&key) {
            Some((etype, _reg)) => {
                *etype = new_etype;
                Ok(())
            }
            None => Err(Error::UndefinedSymbol(pos, vref.clone(), "local")),
        }
    }

    pub(crate) fn define_user_callable(
        &mut self,
        vref: &VarRef,
        params: Vec<VarRef>,
        pos: LineCol,
    ) -> Result<()> {
        let key = SymbolKey::from(&vref.name);
        let previous = self.user_callables.insert(key, (vref.ref_type, params));
        if previous.is_none() { Ok(()) } else { Err(Error::AlreadyDefined(pos, vref.clone())) }
    }

    pub(crate) fn get_user_callable(
        &mut self,
        key: &SymbolKey,
    ) -> Option<&(Option<ExprType>, Vec<VarRef>)> {
        self.user_callables.get(&key)
    }
}
