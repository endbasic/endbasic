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

use crate::ast::ExprType;
use crate::bytecode::{self, Register};
use crate::compiler::ids::HashMapWithIds;
use crate::compiler::{Error, Result, SymbolKey};
use crate::image::{DebugInfo, Image};
use crate::mem::Datum;
use crate::reader::LineCol;
use std::collections::HashMap;

type Address = usize;

pub(super) enum Fixup {
    Call(Register, SymbolKey),
    Enter(u8),
    Gosub(SymbolKey),
    Goto(SymbolKey),
}

#[derive(Default)]
pub(super) struct Codegen {
    code: Vec<u32>,
    constants: HashMapWithIds<Datum, ExprType, u16>,
    fixups: HashMap<Address, Fixup>,
    instr_linecols: Vec<LineCol>,
    labels: HashMap<SymbolKey, Address>,
    user_callables_addresses: HashMap<SymbolKey, Address>,
}

impl Codegen {
    pub(super) fn next_pc(&self) -> Address {
        self.code.len()
    }

    pub(super) fn emit(&mut self, op: u32, pos: LineCol) -> Address {
        self.code.push(op);
        self.instr_linecols.push(pos);
        self.code.len() - 1
    }

    pub(super) fn add_fixup(&mut self, addr: usize, fixup: Fixup) {
        let previous = self.fixups.insert(addr, fixup);
        debug_assert!(previous.is_none(), "Cannot handle more than one fixup per address");
    }

    pub(super) fn get_constant(&mut self, constant: Datum, pos: LineCol) -> Result<u16> {
        match self.constants.get(&constant) {
            Some((_etype, id)) => Ok(id),
            None => {
                let etype = constant.etype();
                match self.constants.insert(constant, etype) {
                    Some((_etype, id)) => Ok(id),
                    None => Err(Error::OutOfConstants(pos)),
                }
            }
        }
    }

    pub(super) fn define_user_callable(&mut self, key: SymbolKey, address: Address) {
        self.user_callables_addresses.insert(key, address);
    }

    pub(super) fn define_label(&mut self, key: SymbolKey, address: Address) {
        self.labels.insert(key, address);
    }

    fn apply_fixups(&mut self) {
        for (addr, fixup) in &self.fixups {
            let instr = match fixup {
                Fixup::Call(reg, key) => {
                    let target = self.user_callables_addresses.get(key).expect("Must be present");
                    // DO NOT SUBMIT: Validate int change.
                    bytecode::make_call(*reg, (target - *addr) as u16)
                }
                Fixup::Enter(nargs) => bytecode::make_enter(*nargs),
                Fixup::Gosub(key) => {
                    let target = self.labels.get(key).expect("Must be present");
                    bytecode::make_gosub((*target as i16 - *addr as i16) as u16)
                }
                Fixup::Goto(key) => {
                    let target = self.labels.get(key).expect("Must be present");
                    // DO NOT SUBMIT: Validate int change.
                    bytecode::make_jump((*target as i16 - *addr as i16) as u16)
                }
            };
            self.code[*addr] = instr;
        }
        self.fixups.clear();
    }

    pub(super) fn build_image(
        mut self,
        upcalls: HashMapWithIds<SymbolKey, Option<ExprType>, u16>,
    ) -> Image {
        self.apply_fixups();

        let mut callables = HashMap::default();
        for (key, pc) in self.user_callables_addresses {
            let previous = callables.insert(pc, key);
            debug_assert!(previous.is_none(), "An address can only start one callable");
        }

        Image::new(
            self.code,
            upcalls.keys_to_vec(),
            self.constants.keys_to_vec(),
            DebugInfo { instr_linecols: self.instr_linecols, callables },
        )
    }
}
