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

//! Code generation for the EndBASIC compiler.

use crate::ast::ExprType;
use crate::bytecode::{self, Register};
use crate::compiler::ids::HashMapWithIds;
use crate::compiler::{Error, Result, SymbolKey};
use crate::image::{DebugInfo, Image};
use crate::mem::ConstantDatum;
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
    constants: HashMapWithIds<ConstantDatum, ExprType, u16>,

    /// Collection of fixups to apply after code generation.
    fixups: HashMap<Address, Fixup>,

    /// Line/column information for every instruction in `code`.
    instr_linecols: Vec<LineCol>,

    /// Map of label names to their target addresses.
    labels: HashMap<SymbolKey, Address>,

    /// Map of user callable names to their target addresses.
    user_callables_addresses: HashMap<SymbolKey, Address>,

    /// Map of built-in callable names to their return types and assigned upcall IDs.
    upcalls: HashMapWithIds<SymbolKey, Option<ExprType>, u16>,
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

    /// Emits code to set `reg` to the default value for `vtype`.
    pub(super) fn emit_default(&mut self, reg: Register, vtype: ExprType, pos: LineCol) {
        let instr = match vtype {
            ExprType::Boolean | ExprType::Double | ExprType::Integer => {
                bytecode::make_load_integer(reg, 0)
            }
            ExprType::Text => bytecode::make_alloc(reg, ExprType::Text),
        };
        self.emit(instr, pos);
    }

    /// Records a `fixup` that needs to be applied at `addr`.
    pub(super) fn add_fixup(&mut self, addr: usize, fixup: Fixup) {
        let previous = self.fixups.insert(addr, fixup);
        debug_assert!(previous.is_none(), "Cannot handle more than one fixup per address");
    }

    /// Gets the ID of a `constant`, adding it to the constants table if it isn't yet there.
    pub(super) fn get_constant(&mut self, constant: ConstantDatum, pos: LineCol) -> Result<u16> {
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

    /// Gets the existing upcall ID for the given `key` or creates a new one.
    pub(super) fn get_upcall(
        &mut self,
        key: SymbolKey,
        etype: Option<ExprType>,
        pos: LineCol,
    ) -> Result<u16> {
        match self.upcalls.get(&key) {
            Some((_etype, id)) => Ok(id),
            None => match self.upcalls.insert(key, etype) {
                Some((_etype, id)) => Ok(id),
                None => Err(Error::OutOfUpcalls(pos)),
            },
        }
    }

    /// Consumes the code generator and builds a ready-to-use `Image`.
    pub(super) fn build_image(mut self) -> Result<Image> {
        self.apply_fixups()?;

        let mut callables = HashMap::default();
        for (key, pc) in self.user_callables_addresses {
            let previous = callables.insert(pc, key);
            debug_assert!(previous.is_none(), "An address can only start one callable");
        }

        Ok(Image::new(
            self.code,
            self.upcalls.keys_to_vec(),
            self.constants.keys_to_vec(),
            DebugInfo { instr_linecols: self.instr_linecols, callables },
        ))
    }
}
