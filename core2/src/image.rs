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

//! Compiled program representation.

use crate::ast::ExprType;
use crate::bytecode::{self, Opcode, Register, opcode_of};
use crate::compiler::SymbolKey;
use crate::mem::ConstantDatum;
use crate::reader::LineCol;
use std::collections::HashMap;

/// Formats an instruction for debugging.
///
/// Panics if the instruction is malformed.
pub(crate) fn format_instr(instr: u32) -> String {
    match opcode_of(instr) {
        Opcode::AddDouble => bytecode::format_add_double(instr),
        Opcode::AddInteger => bytecode::format_add_integer(instr),
        Opcode::Alloc => bytecode::format_alloc(instr),
        Opcode::AllocArray => bytecode::format_alloc_array(instr),
        Opcode::Call => bytecode::format_call(instr),
        Opcode::Concat => bytecode::format_concat(instr),
        Opcode::DivideDouble => bytecode::format_divide_double(instr),
        Opcode::DivideInteger => bytecode::format_divide_integer(instr),
        Opcode::DoubleToInteger => bytecode::format_double_to_integer(instr),
        Opcode::End => bytecode::format_end(instr),
        Opcode::Enter => bytecode::format_enter(instr),
        Opcode::Gosub => bytecode::format_gosub(instr),
        Opcode::IntegerToDouble => bytecode::format_integer_to_double(instr),
        Opcode::Jump => bytecode::format_jump(instr),
        Opcode::Leave => bytecode::format_leave(instr),
        Opcode::LoadArray => bytecode::format_load_array(instr),
        Opcode::LoadConstant => bytecode::format_load_constant(instr),
        Opcode::LoadInteger => bytecode::format_load_integer(instr),
        Opcode::LoadRegisterPointer => bytecode::format_load_register_ptr(instr),
        Opcode::ModuloDouble => bytecode::format_modulo_double(instr),
        Opcode::ModuloInteger => bytecode::format_modulo_integer(instr),
        Opcode::Move => bytecode::format_move(instr),
        Opcode::MultiplyDouble => bytecode::format_multiply_double(instr),
        Opcode::MultiplyInteger => bytecode::format_multiply_integer(instr),
        Opcode::NegateDouble => bytecode::format_negate_double(instr),
        Opcode::NegateInteger => bytecode::format_negate_integer(instr),
        Opcode::Nop => bytecode::format_nop(instr),
        Opcode::PowerDouble => bytecode::format_power_double(instr),
        Opcode::PowerInteger => bytecode::format_power_integer(instr),
        Opcode::Return => bytecode::format_return(instr),
        Opcode::StoreArray => bytecode::format_store_array(instr),
        Opcode::SubtractDouble => bytecode::format_subtract_double(instr),
        Opcode::SubtractInteger => bytecode::format_subtract_integer(instr),
        Opcode::Upcall => bytecode::format_upcall(instr),
    }
}

/// Information about a global variable tracked for post-execution querying.
pub(crate) struct GlobalVarInfo {
    /// Global register index (0 to `Register::MAX_GLOBAL - 1`).
    pub(crate) reg: u8,

    /// Element type (for arrays, the element type; for scalars, the scalar type).
    pub(crate) subtype: ExprType,

    /// Number of dimensions: 0 for scalars, >=1 for arrays.
    pub(crate) ndims: usize,
}

/// Per-instruction metadata stored in `DebugInfo`.
pub(crate) struct InstrMetadata {
    /// Source location that generated this instruction.
    pub(crate) linecol: LineCol,

    /// Source locations of the call arguments, if this is a UPCALL instruction.
    ///
    /// Each entry corresponds to one register slot in the argument area, in the same order
    /// that `compile_args` allocates them.  Empty for all other instruction types.
    pub(crate) arg_linecols: Vec<LineCol>,
}

/// Debugging information for a compiled program.
#[derive(Default)]
pub struct DebugInfo {
    /// Per-instruction metadata, one entry per instruction in the image's code.
    pub(crate) instrs: Vec<InstrMetadata>,

    /// Maps instruction addresses to the names of user-defined callables that start at those
    /// addresses.
    pub(crate) callables: HashMap<usize, SymbolKey>,

    /// Maps global variable names to their register assignments and type information.
    ///
    /// This includes both host-pre-defined globals (from `compile_with_globals`) and
    /// globals declared via `DIM SHARED` in the user's program.
    pub(crate) global_vars: HashMap<SymbolKey, GlobalVarInfo>,
}

/// Representation of a compiled EndBASIC program.
///
/// Images always have at least one instruction so that the VM can make this assumption.
pub struct Image {
    /// The bytecode instructions of the compiled program.
    pub(crate) code: Vec<u32>,

    /// Names of external callables referenced by the program, indexed by upcall ID.
    pub(crate) upcalls: Vec<SymbolKey>,

    /// Pool of constant values used by the program.
    pub(crate) constants: Vec<ConstantDatum>,

    /// Debugging information for error reporting and disassembly.
    pub(crate) debug_info: DebugInfo,

    /// Marker to prevent external construction; ensures `code` is never empty.
    _internal: (),
}

impl Default for Image {
    fn default() -> Self {
        Self::new(
            vec![
                // The minimum valid program requires an explicit `END` so that the VM knows to
                // exit.  We can directly reference register 0 because all registers would have
                // been cleared and accessing them would result in their default values.
                bytecode::make_end(Register::global(0).expect("Global 0 register be valid")),
            ],
            vec![],
            vec![],
            DebugInfo {
                instrs: vec![InstrMetadata {
                    linecol: LineCol { line: 0, col: 0 },
                    arg_linecols: vec![],
                }],
                callables: HashMap::default(),
                global_vars: HashMap::default(),
            },
        )
    }
}

impl Image {
    pub(crate) fn new(
        code: Vec<u32>,
        upcalls: Vec<SymbolKey>,
        constants: Vec<ConstantDatum>,
        debug_info: DebugInfo,
    ) -> Self {
        debug_assert!(!code.is_empty(), "Compiler must ensure the image is not empty");
        debug_assert_eq!(code.len(), debug_info.instrs.len());
        Self { code, upcalls, constants, debug_info, _internal: () }
    }

    /// Disassembles the image into a textual representation for debugging.
    pub fn disasm(&self) -> Vec<String> {
        let mut lines = Vec::with_capacity(self.code.len());

        for ((i, instr), meta) in
            self.code.iter().copied().enumerate().zip(self.debug_info.instrs.iter())
        {
            let pos = meta.linecol;
            if let Some(key) = self.debug_info.callables.get(&i) {
                lines.push("".to_owned());
                lines.push(format!("-- {} ", key));
            }

            let mut line = format!("{:04}:   {}", i, format_instr(instr));

            while line.len() < 40 {
                line.push(' ');
            }
            line.push_str(&format!("# {}", pos));

            match opcode_of(instr) {
                Opcode::Call => {
                    let (_reg, target) = bytecode::parse_call(instr);
                    let target = usize::from(target);
                    let name = self
                        .debug_info
                        .callables
                        .get(&target)
                        .expect("All CALL targets must be defined");
                    line.push_str(&format!(", {}", name))
                }

                Opcode::Upcall => {
                    let (index, _first_reg) = bytecode::parse_upcall(instr);
                    let name = &self.upcalls[usize::from(index)];
                    line.push_str(&format!(", {}", name))
                }

                _ => (),
            }

            lines.push(line);
        }

        lines
    }
}
