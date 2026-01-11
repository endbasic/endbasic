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

//! Code generation for the EndBASIC compiler.

use crate::ast::ExprType;
use crate::bytecode::{self, Register};
use crate::compiler::ids::HashMapWithIds;
use crate::compiler::{Error, Result, SymbolKey};
use crate::image::{DebugInfo, Image};
use crate::mem::Datum;
use crate::reader::LineCol;
use std::collections::HashMap;
use std::convert::TryFrom;

/// Alias for instruction addresses in the generated code.
type Address = usize;

/// Represents a fixup that needs to be applied to an instruction after all symbols have been
/// located.
pub(super) enum Fixup {
    /// Fixup to resolve a user-defined call target address into a `CALL` instruction.
    Call(Register, SymbolKey),

    /// Fixup to record the number of local variables to allocate in an `ENTER` instruction.
    Enter(u8),

    /// Fixup to resolve a label target address into a `GOSUB` instruction.
    Gosub(SymbolKey),

    /// Fixup to resolve a label target address into a `GOTO` (jump) instruction.
    Goto(SymbolKey),
}

/// The code generator.
#[derive(Default)]
pub(super) struct Codegen {
    /// The instructions being generated.
    code: Vec<u32>,

    /// The constants pool for the image being generated.
    constants: HashMapWithIds<Datum, ExprType, u16>,

    /// Collection of fixups to apply after code generation.
    fixups: HashMap<Address, Fixup>,

    /// Line/column information for every instruction in `code`.
    instr_linecols: Vec<LineCol>,

    /// Map of label names to their target addresses.
    labels: HashMap<SymbolKey, Address>,

    /// Map of user callable names to their target addresses.
    user_callables_addresses: HashMap<SymbolKey, Address>,
}

impl Codegen {
    /// Returns the address of the next instruction to be emitted.
    pub(super) fn next_pc(&self) -> Address {
        self.code.len()
    }

    /// Appends a new instruction `op` generated at `pos` to the code and returns its address.
    pub(super) fn emit(&mut self, op: u32, pos: LineCol) -> Address {
        self.code.push(op);
        self.instr_linecols.push(pos);
        self.code.len() - 1
    }

    /// Records a `fixup` that needs to be applied at `addr`.
    pub(super) fn add_fixup(&mut self, addr: usize, fixup: Fixup) {
        let previous = self.fixups.insert(addr, fixup);
        debug_assert!(previous.is_none(), "Cannot handle more than one fixup per address");
    }

    /// Gets the ID of a `constant`, adding it to the constants table if it isn't yet there.
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

    /// Records the location of a user-defined callable.
    pub(super) fn define_user_callable(&mut self, key: SymbolKey, address: Address) {
        self.user_callables_addresses.insert(key, address);
    }

    /// Records the location of a label.
    pub(super) fn define_label(&mut self, key: SymbolKey, address: Address) {
        self.labels.insert(key, address);
    }

    /// Converts a symbolic `target` address into a 16-bit relative address from `pos`.
    fn make_target(target: usize, pos: LineCol) -> Result<u16> {
        match u16::try_from(target) {
            Ok(num) => Ok(num),
            Err(_) => Err(Error::TargetTooFar(pos, target)),
        }
    }

    /// Applies all registered fixups to the generated code.
    fn apply_fixups(&mut self) -> Result<()> {
        for (addr, fixup) in self.fixups.drain() {
            let pos = self.instr_linecols[addr];
            let instr = match fixup {
                Fixup::Call(reg, key) => {
                    let target = self.user_callables_addresses.get(&key).expect("Must be present");
                    bytecode::make_call(reg, Self::make_target(*target, pos)?)
                }
                Fixup::Enter(nargs) => bytecode::make_enter(nargs),
                Fixup::Gosub(key) => {
                    let target = self.labels.get(&key).expect("Must be present");
                    bytecode::make_gosub(Self::make_target(*target, pos)?)
                }
                Fixup::Goto(key) => {
                    let target = self.labels.get(&key).expect("Must be present");
                    bytecode::make_jump(Self::make_target(*target, pos)?)
                }
            };
            self.code[addr] = instr;
        }
        debug_assert!(self.fixups.is_empty());
        Ok(())
    }

    /// Consumes the code generator and builds a ready-to-use `Image`.
    pub(super) fn build_image(
        mut self,
        upcalls: HashMapWithIds<SymbolKey, Option<ExprType>, u16>,
    ) -> Result<Image> {
        self.apply_fixups()?;

        let mut callables = HashMap::default();
        for (key, pc) in self.user_callables_addresses {
            let previous = callables.insert(pc, key);
            debug_assert!(previous.is_none(), "An address can only start one callable");
        }

        Ok(Image::new(
            self.code,
            upcalls.keys_to_vec(),
            self.constants.keys_to_vec(),
            DebugInfo { instr_linecols: self.instr_linecols, callables },
        ))
    }
}
