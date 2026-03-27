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
use crate::bytecode::{self, ErrorHandlerMode, Register};
use crate::compiler::ids::HashMapWithIds;
use crate::compiler::{Error, Result, SymbolKey};
use crate::image::{GlobalVarInfo, Image, ImageDelta, InstrMetadata};
use crate::mem::ConstantDatum;
use crate::reader::LineCol;
use std::collections::HashMap;
use std::convert::TryFrom;

/// Alias for instruction addresses in the generated code.
type Address = usize;

/// Represents a fixup that needs to be applied to an instruction after all symbols have been
/// located.
#[derive(Clone)]
pub(super) enum Fixup {
    /// Fixup to resolve a user-defined call target address into a `CALL` instruction.
    Call(Register, SymbolKey),

    /// Fixup to resolve a label target address into a `GOSUB` instruction.
    Gosub(String),

    /// Fixup to resolve a label target address into a `GOTO` (jump) instruction.
    Goto(String),

    /// Fixup to resolve a label target address into a `SET_ERROR_HANDLER` instruction.
    OnErrorGoto(String),
}

/// The code generator.
#[derive(Clone, Default)]
pub(super) struct Codegen {
    /// The instructions being generated.
    code: Vec<u32>,

    /// The constants pool for the image being generated.
    constants: HashMapWithIds<ConstantDatum, ExprType, u16>,

    /// Collection of fixups to apply after code generation.
    fixups: HashMap<Address, Fixup>,

    /// Per-instruction metadata for every instruction in `code`.
    instrs: Vec<InstrMetadata>,

    /// Map of label names to their target addresses.
    labels: HashMap<SymbolKey, Address>,

    /// Map of user callable names to their target start and end addresses.
    user_callables_addresses: HashMap<SymbolKey, (Address, Address)>,

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
        self.instrs.push(InstrMetadata {
            linecol: pos,
            is_stmt_start: false,
            arg_linecols: vec![],
        });
        self.code.len() - 1
    }

    /// Marks the instruction at `addr` as the start of a statement.
    pub(super) fn mark_statement_start(&mut self, addr: Address) {
        self.instrs[addr].is_stmt_start = true;
    }

    /// Attaches argument source locations to the instruction at `addr`.
    ///
    /// `arg_linecols` has one entry per register slot in the argument area, in the same order
    /// that `compile_args` allocates them.  This should be called after emitting a UPCALL or
    /// CALL instruction.
    pub(super) fn set_arg_linecols(&mut self, addr: Address, arg_linecols: Vec<LineCol>) {
        self.instrs[addr].arg_linecols = arg_linecols;
    }

    /// Removes the EOF instruction from the program, if any.
    pub(super) fn pop_eof(&mut self) {
        if let Some(instr) = self.code.pop() {
            debug_assert_eq!(bytecode::make_eof(), instr);
            self.instrs.pop();
        }
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

    /// Emits code to set `reg` to the specific `datum` value.
    pub(super) fn emit_value(
        &mut self,
        reg: Register,
        datum: ConstantDatum,
        pos: LineCol,
    ) -> Result<()> {
        match datum {
            ConstantDatum::Boolean(b) => {
                self.emit(bytecode::make_load_integer(reg, if b { 1 } else { 0 }), pos);
            }
            ConstantDatum::Integer(i) => {
                if let Ok(v) = u16::try_from(i) {
                    self.emit(bytecode::make_load_integer(reg, v), pos);
                } else {
                    let idx = self.get_constant(ConstantDatum::Integer(i), pos)?;
                    self.emit(bytecode::make_load_constant(reg, idx), pos);
                }
            }
            ConstantDatum::Double(d) => {
                let idx = self.get_constant(ConstantDatum::Double(d), pos)?;
                self.emit(bytecode::make_load_constant(reg, idx), pos);
            }
            ConstantDatum::Text(s) => {
                let idx = self.get_constant(ConstantDatum::Text(s), pos)?;
                self.emit(bytecode::make_load_integer(reg, idx), pos);
            }
        }
        Ok(())
    }

    /// Overwrites the instruction at `addr` with `op`.
    ///
    /// Used by the compiler to back-patch placeholder instructions with resolved jump targets.
    pub(super) fn patch(&mut self, addr: Address, op: u32) {
        self.code[addr] = op;
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
    pub(super) fn define_user_callable(&mut self, key: SymbolKey, start: Address, end: Address) {
        self.user_callables_addresses.insert(key, (start, end));
    }

    /// Records the location of a label.  Returns false on failure (if the label already existed).
    pub(super) fn define_label(&mut self, key: SymbolKey, address: Address) -> bool {
        self.labels.insert(key, address).is_none()
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
            let pos = self.instrs[addr].linecol;
            let instr = match fixup {
                Fixup::Call(reg, key) => {
                    let (target, _end) =
                        self.user_callables_addresses.get(&key).expect("Must be present");
                    bytecode::make_call(reg, Self::make_target(*target, pos)?)
                }
                Fixup::Gosub(label) => {
                    let key = SymbolKey::from(&label);
                    let Some(target) = self.labels.get(&key) else {
                        return Err(Error::UnknownLabel(pos, label));
                    };
                    bytecode::make_gosub(Self::make_target(*target, pos)?)
                }
                Fixup::Goto(label) => {
                    let key = SymbolKey::from(&label);
                    let Some(target) = self.labels.get(&key) else {
                        return Err(Error::UnknownLabel(pos, label));
                    };
                    bytecode::make_jump(Self::make_target(*target, pos)?)
                }
                Fixup::OnErrorGoto(label) => {
                    let key = SymbolKey::from(&label);
                    let Some(target) = self.labels.get(&key) else {
                        return Err(Error::UnknownLabel(pos, label));
                    };
                    bytecode::make_set_error_handler(
                        ErrorHandlerMode::Jump,
                        Self::make_target(*target, pos)?,
                    )
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

    /// Builds an incremental update to append into `image`.
    pub(super) fn build_image_delta(
        &mut self,
        image: &Image,
        global_vars: HashMap<SymbolKey, GlobalVarInfo>,
        data: &[Option<ConstantDatum>],
    ) -> Result<ImageDelta> {
        self.apply_fixups()?;

        let code_start = image.code.len().saturating_sub(1);
        let constants_start = image.constants.len();
        let instrs_start = image.debug_info.instrs.len().saturating_sub(1);
        let upcalls_start = image.upcalls.len();

        debug_assert_eq!(code_start, instrs_start);
        debug_assert!(code_start <= self.code.len());
        debug_assert!(constants_start <= self.constants.len());
        debug_assert!(image.data.len() <= data.len());
        debug_assert!(upcalls_start <= self.upcalls.len());

        debug_assert_eq!(&image.code[..code_start], &self.code[..code_start]);
        debug_assert_eq!(&image.debug_info.instrs[..instrs_start], &self.instrs[..instrs_start],);
        debug_assert!(
            self.constants.keys_to_vec().starts_with(image.constants.as_slice()),
            "Image constants must match the compiler state prefix",
        );
        debug_assert!(
            self.upcalls.keys_to_vec().starts_with(image.upcalls.as_slice()),
            "Image upcalls must match the compiler state prefix",
        );
        debug_assert_eq!(image.data.as_slice(), &data[..image.data.len()]);

        let mut callables = HashMap::default();
        for (key, (start_pc, end_pc)) in &self.user_callables_addresses {
            let previous = callables.insert(*start_pc, (key.clone(), true));
            debug_assert!(previous.is_none(), "An address can only start one callable");

            let previous = callables.insert(*end_pc, (key.clone(), false));
            debug_assert!(previous.is_none(), "An address can only start one callable");
        }

        Ok(ImageDelta {
            code: self.code[code_start..].to_vec(),
            upcalls: self.upcalls.keys_to_vec_from(upcalls_start),
            constants: self.constants.keys_to_vec_from(constants_start),
            data: data[image.data.len()..].to_vec(),
            instrs: self.instrs[instrs_start..].to_vec(),
            callables,
            global_vars,
        })
    }

    #[cfg(test)]
    /// Builds a ready-to-use `Image`.
    pub(super) fn build_image(
        &mut self,
        global_vars: HashMap<SymbolKey, GlobalVarInfo>,
        data: Vec<Option<ConstantDatum>>,
    ) -> Result<Image> {
        let mut image = Image::default();
        let delta = self.build_image_delta(&image, global_vars, &data)?;
        image.append(delta);
        Ok(image)
    }
}
