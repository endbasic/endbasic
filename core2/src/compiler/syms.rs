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

use crate::bytecode::Register;
use crate::compiler::{IdAssigner, Result};
use crate::reader::LineCol;
use std::convert::TryFrom;
use std::fmt;

use super::map_bytecode_error;

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

pub(crate) struct Symtable {
    globals: IdAssigner<SymbolKey, u8>,
    locals: Vec<(IdAssigner<SymbolKey, u8>, Temps)>,
}

impl Default for Symtable {
    fn default() -> Self {
        Self {
            globals: IdAssigner::default(),
            locals: vec![(IdAssigner::default(), Temps::default())],
        }
    }
}

impl Symtable {
    pub(crate) fn global(&mut self, key: &SymbolKey, pos: LineCol) -> Result<Register> {
        Register::global(self.globals.get(key)).map_err(|e| map_bytecode_error(pos, e))
    }

    pub(crate) fn local(&mut self, key: &SymbolKey, pos: LineCol) -> Result<Register> {
        Register::local(self.locals.last_mut().unwrap().0.get(key))
            .map_err(|e| map_bytecode_error(pos, e))
    }

    pub(crate) fn alloc_temp(&mut self, pos: LineCol) -> Result<Register> {
        let (locals, temps) = self.locals.last_mut().unwrap();
        let reg = locals.len() + usize::from(temps.alloc());
        Register::local(u8::try_from(reg).expect("DO NOT SUBMIT"))
            .map_err(|e| map_bytecode_error(pos, e))
    }

    pub(crate) fn dealloc_temps(&mut self, count: u8) {
        let (_locals, temps) = self.locals.last_mut().unwrap();
        temps.dealloc(count);
    }

    pub(crate) fn frame_size(&self) -> u8 {
        let (locals, temps) = self.locals.last().unwrap();
        u8::try_from(locals.len() + usize::from(temps.count)).expect("DO NOT SUBMIT")
    }
}
