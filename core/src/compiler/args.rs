// EndBASIC
// Copyright 2024 Julio Merino
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

//! Common compilers for callable arguments.

use super::{compile_expr, compile_expr_in_command, CallableArgsCompiler, SymbolsTable};
use crate::ast::*;
use crate::bytecode::*;
use crate::reader::LineCol;
use crate::syms::CallError;

/// Result for argument compilation return values.
pub type Result<T> = std::result::Result<T, CallError>;

/// A callable arguments compiler that just passes through all arguments to the runtime `exec`
/// method.
///
/// This exists for transitional reasons only until all callables have migrated to doing
/// compile-time validation of their arguments.
#[derive(Debug, Default)]
pub(crate) struct PassthroughArgsCompiler {}

impl CallableArgsCompiler for PassthroughArgsCompiler {
    fn compile_complex(
        &self,
        instrs: &mut Vec<Instruction>,
        symtable: &mut SymbolsTable,
        _pos: LineCol,
        args: Vec<ArgSpan>,
    ) -> Result<usize> {
        let mut nargs = 0;
        for argspan in args.into_iter().rev() {
            if argspan.sep != ArgSep::End {
                instrs.push(Instruction::Push(Value::Separator(argspan.sep), argspan.sep_pos));
                nargs += 1;
            }

            match argspan.expr {
                Some(expr) => {
                    compile_expr_in_command(instrs, symtable, expr)?;
                }
                None => {
                    instrs.push(Instruction::Push(Value::Missing, argspan.sep_pos));
                }
            }
            nargs += 1;
        }
        Ok(nargs)
    }

    fn compile_simple(
        &self,
        instrs: &mut Vec<Instruction>,
        symtable: &SymbolsTable,
        _pos: LineCol,
        args: Vec<Expr>,
    ) -> Result<usize> {
        let nargs = args.len();
        for arg in args.into_iter().rev() {
            compile_expr(instrs, symtable, arg, true)?;
        }
        Ok(nargs)
    }
}
