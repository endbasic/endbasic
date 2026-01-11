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

use crate::bytecode::{self, format_instr};
use crate::callable::Callable;
use crate::compiler::SymbolKey;
use crate::mem::Datum;
use crate::reader::LineCol;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Default)]
pub struct DebugInfo {
    pub(crate) instr_linecols: Vec<LineCol>,
    pub(crate) callables: HashMap<usize, SymbolKey>,
}

/// Representation of a compiled EndBASIC program.
///
/// Images always have at least one instruction so that the VM can make this assumption.
pub struct Image {
    pub(crate) code: Vec<u32>,
    pub(crate) upcalls: Vec<SymbolKey>,
    pub(crate) constants: Vec<Datum>,
    pub(crate) debug_info: DebugInfo,

    // Prevent construction from the crate because we must ensure `code` is never empty.
    _internal: (),
}

impl Default for Image {
    fn default() -> Self {
        Self::new(
            vec![bytecode::make_end()],
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

    pub fn disasm(&self) -> Vec<String> {
        self.code
            .iter()
            .copied()
            .enumerate()
            .zip(self.debug_info.instr_linecols.iter().copied())
            .map(|((i, instr), pos)| {
                let mut line = format!("{:04}    {}", i, format_instr(instr));
                while line.len() < 48 {
                    line.push(' ');
                }
                line.push_str(&format!("# {}", pos));
                if let Some(key) = self.debug_info.callables.get(&i) {
                    line.push_str(&format!(" <= {}", key));
                }
                line
            })
            .collect()
    }

    pub fn map_upcalls(
        &self,
        upcalls_by_name: &HashMap<SymbolKey, Rc<dyn Callable>>,
    ) -> Vec<Rc<dyn Callable>> {
        let mut upcalls = Vec::with_capacity(self.upcalls.len());
        for key in &self.upcalls {
            upcalls.push(upcalls_by_name.get(&key).expect("DO NOT SUBMIT").clone());
        }
        upcalls
    }
}
