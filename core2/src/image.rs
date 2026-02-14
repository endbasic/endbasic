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

//! Compiled program representation.

use crate::bytecode::{self, Opcode, Register, opcode_of};
use crate::compiler::SymbolKey;
use crate::mem::Datum;
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
        Opcode::Call => bytecode::format_call(instr),
        Opcode::Concat => bytecode::format_concat(instr),
        Opcode::DoubleToInteger => bytecode::format_double_to_integer(instr),
        Opcode::End => bytecode::format_end(instr),
        Opcode::Enter => bytecode::format_enter(instr),
        Opcode::Gosub => bytecode::format_gosub(instr),
        Opcode::IntegerToDouble => bytecode::format_integer_to_double(instr),
        Opcode::Jump => bytecode::format_jump(instr),
        Opcode::LoadConstant => bytecode::format_load_constant(instr),
        Opcode::LoadInteger => bytecode::format_load_integer(instr),
        Opcode::LoadRegisterPointer => bytecode::format_load_register_ptr(instr),
        Opcode::Move => bytecode::format_move(instr),
        Opcode::Nop => bytecode::format_nop(instr),
        Opcode::Return => bytecode::format_return(instr),
        Opcode::Upcall => bytecode::format_upcall(instr),
    }
}

/// Debugging information for a compiled program.
#[derive(Default)]
pub struct DebugInfo {
    /// Maps each instruction index to its source location (line and column).
    pub(crate) instr_linecols: Vec<LineCol>,

    /// Maps instruction addresses to the names of user-defined callables that start at those
    /// addresses.
    pub(crate) callables: HashMap<usize, SymbolKey>,
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
    pub(crate) constants: Vec<Datum>,

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
                instr_linecols: vec![LineCol { line: 0, col: 0 }],
                callables: HashMap::default(),
            },
        )
    }
}

impl Image {
    pub(crate) fn new(
        code: Vec<u32>,
        upcalls: Vec<SymbolKey>,
        constants: Vec<Datum>,
        debug_info: DebugInfo,
    ) -> Self {
        debug_assert!(!code.is_empty(), "Compiler must ensure the image is not empty");
        debug_assert_eq!(code.len(), debug_info.instr_linecols.len());
        Self { code, upcalls, constants, debug_info, _internal: () }
    }

    /// Disassembles the image into a textual representation for debugging.
    pub fn disasm(&self) -> Vec<String> {
        let mut lines = Vec::with_capacity(self.code.len());

        for ((i, instr), pos) in self
            .code
            .iter()
            .copied()
            .enumerate()
            .zip(self.debug_info.instr_linecols.iter().copied())
        {
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
