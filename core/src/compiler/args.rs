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

use super::ExprType;
use super::{compile_expr, CallableArgsCompiler, SymbolsTable};
use crate::ast::*;
use crate::bytecode::*;
use crate::reader::LineCol;
use crate::syms::CallError;

/// Result for argument compilation return values.
pub type Result<T> = std::result::Result<T, CallError>;

/// An arguments compiler for a callable that receives no arguments.
#[derive(Debug, Default)]
pub struct NoArgsCompiler {}

impl CallableArgsCompiler for NoArgsCompiler {
    fn compile_complex(
        &self,
        _instrs: &mut Vec<Instruction>,
        _symtable: &mut SymbolsTable,
        _pos: LineCol,
        args: Vec<ArgSpan>,
    ) -> Result<usize> {
        if !args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        Ok(0)
    }

    fn compile_simple(
        &self,
        _instrs: &mut Vec<Instruction>,
        _symtable: &SymbolsTable,
        _pos: LineCol,
        args: Vec<Expr>,
    ) -> Result<usize> {
        if !args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        Ok(0)
    }
}

/// Compiles a single expression, expecting it to be of a `target` type.  Applies casts if
/// possible.
pub fn compile_arg_expr(
    instrs: &mut Vec<Instruction>,
    symtable: &SymbolsTable,
    expr: Expr,
    target: ExprType,
) -> Result<()> {
    let epos = expr.start_pos();
    let etype = compile_expr(instrs, symtable, expr, false)?;
    if etype == ExprType::Double && target.is_numerical() {
        if target == ExprType::Integer {
            instrs.push(Instruction::DoubleToInteger);
        }
        Ok(())
    } else if etype == ExprType::Integer && target.is_numerical() {
        if target == ExprType::Double {
            instrs.push(Instruction::IntegerToDouble);
        }
        Ok(())
    } else if etype == target {
        Ok(())
    } else {
        if target.is_numerical() {
            Err(CallError::ArgumentError(epos, format!("{} is not a number", etype)))
        } else {
            Err(CallError::ArgumentError(epos, format!("{} is not a {}", etype, target)))
        }
    }
}

/// Compiles an argument, expecting it to be of a `target` type.  Applies casts if possible.
pub fn compile_arg<I>(
    instrs: &mut Vec<Instruction>,
    symtable: &SymbolsTable,
    iter: &mut I,
    target: ExprType,
) -> Result<()>
where
    I: Iterator<Item = Expr>,
{
    match iter.next() {
        Some(expr) => compile_arg_expr(instrs, symtable, expr, target),
        None => Err(CallError::SyntaxError),
    }
}

/// An arguments compiler for a callable that takes multiple arguments of the same type.
///
/// In the case of commands, the arguments are expected to be separated by commas and none are
/// optional.
#[derive(Debug)]
pub struct SameTypeArgsCompiler {
    min: usize,
    max: usize,
    target: ExprType,
}

impl SameTypeArgsCompiler {
    /// Creates a new arguments compiler.
    pub fn new(min: usize, max: usize, target: ExprType) -> Self {
        Self { min, max, target }
    }
}

impl CallableArgsCompiler for SameTypeArgsCompiler {
    fn compile_complex(
        &self,
        instrs: &mut Vec<Instruction>,
        symtable: &mut SymbolsTable,
        _pos: LineCol,
        args: Vec<ArgSpan>,
    ) -> Result<usize> {
        if args.len() < self.min || args.len() > self.max {
            return Err(CallError::SyntaxError);
        }

        let mut iter = args.into_iter().rev();
        let mut i = 0;
        loop {
            debug_assert!(i <= self.max);

            let sep = match iter.next() {
                Some(span) => match span.expr {
                    Some(expr) => {
                        compile_arg_expr(instrs, symtable, expr, self.target)?;
                        span.sep
                    }
                    None => return Err(CallError::SyntaxError),
                },
                None => {
                    break;
                }
            };

            i += 1;

            match sep {
                ArgSep::Long | ArgSep::End => (),
                _ => return Err(CallError::SyntaxError),
            }
        }
        debug_assert!(i >= self.min);
        Ok(i)
    }

    fn compile_simple(
        &self,
        instrs: &mut Vec<Instruction>,
        symtable: &SymbolsTable,
        _pos: LineCol,
        args: Vec<Expr>,
    ) -> Result<usize> {
        if args.len() < self.min || args.len() > self.max {
            return Err(CallError::SyntaxError);
        }

        let mut iter = args.into_iter().rev();
        let mut i = 0;
        loop {
            debug_assert!(i <= self.max);

            match iter.next() {
                Some(expr) => compile_arg_expr(instrs, symtable, expr, self.target)?,
                None => {
                    break;
                }
            }

            i += 1;
        }
        debug_assert!(i >= self.min);
        Ok(i)
    }
}
