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

//! Functions to convert expressions into bytecode.

use crate::ast::{BinaryOpSpan, Expr, ExprType};
use crate::bytecode::{self, Register, RegisterScope};
use crate::compiler::args::compile_args;
use crate::compiler::codegen::{Codegen, Fixup};
use crate::compiler::syms::{self, SymbolKey, TempSymtable};
use crate::compiler::{Error, Result};
use crate::mem::Datum;
use std::convert::TryFrom;

/// Compiles an arithmetic binary operation `span` that returns its value into `reg`.
fn compile_arithmetic_binary_op(
    codegen: &mut Codegen,
    symtable: &mut TempSymtable<'_, '_, '_, '_, '_>,
    reg: Register,
    span: BinaryOpSpan,
    op_name: &'static str,
) -> Result<ExprType> {
    let mut scope = symtable.temp_scope();

    let lpos = span.lhs.start_pos();
    let ltemp = scope.alloc().map_err(|e| Error::from_syms(e, lpos))?;
    let ltype = compile_expr(codegen, symtable, ltemp, span.lhs)?;

    let rpos = span.rhs.start_pos();
    let rtemp = scope.alloc().map_err(|e| Error::from_syms(e, rpos))?;
    let rtype = compile_expr(codegen, symtable, rtemp, span.rhs)?;

    let rtype = match (ltype, rtype) {
        // Type-compatible operands.
        (ExprType::Double, ExprType::Double) => ExprType::Double,
        (ExprType::Integer, ExprType::Integer) => ExprType::Integer,
        (ExprType::Text, ExprType::Text) if op_name == "+" => ExprType::Text,

        // Operands requiring type promotion.
        (ExprType::Double, ExprType::Integer) => {
            codegen.emit(bytecode::make_integer_to_double(rtemp), rpos);
            ExprType::Double
        }
        (ExprType::Integer, ExprType::Double) => {
            codegen.emit(bytecode::make_integer_to_double(ltemp), lpos);
            ExprType::Double
        }

        // Unsupported operand types.
        _ => {
            return Err(Error::BinaryOpType(span.pos, "+", ltype, rtype));
        }
    };

    match rtype {
        ExprType::Boolean => unreachable!(),

        ExprType::Double => {
            codegen.emit(bytecode::make_add_double(reg, ltemp, rtemp), span.pos);
        }

        ExprType::Integer => {
            codegen.emit(bytecode::make_add_integer(reg, ltemp, rtemp), span.pos);
        }

        ExprType::Text => {
            codegen.emit(bytecode::make_concat(reg, ltemp, rtemp), span.pos);
        }
    }

    Ok(rtype)
}

/// Compiles a single expression `expr` and leaves its value in `reg`.
pub(super) fn compile_expr(
    codegen: &mut Codegen,
    symtable: &mut TempSymtable<'_, '_, '_, '_, '_>,
    reg: Register,
    expr: Expr,
) -> Result<ExprType> {
    match expr {
        Expr::Add(span) => compile_arithmetic_binary_op(codegen, symtable, reg, *span, "+"),

        Expr::Boolean(span) => {
            let value = if span.value { 1 } else { 0 };
            codegen.emit(bytecode::make_load_integer(reg, value), span.pos);
            Ok(ExprType::Boolean)
        }

        Expr::Call(span) => {
            let key = SymbolKey::from(&span.vref.name);
            let key_pos = span.vref_pos;

            let Some(md) = symtable.get_callable(&key) else {
                return Err(Error::UndefinedSymbol(
                    span.vref_pos,
                    span.vref,
                    RegisterScope::Global,
                ));
            };

            let Some(etype) = md.return_type() else {
                return Err(Error::NotAFunction(span.vref_pos, span.vref));
            };

            if md.is_argless() {
                return Err(Error::CallableSyntax(span.vref_pos, md.clone()));
            }

            if md.is_user_defined() {
                let (is_global, _index) = reg.to_parts();

                let mut alloc = symtable.temp_scope();
                let ret_reg = if is_global {
                    // The call instruction can only carry one register, and this register
                    // indicates where to store the result and where arguments start.  So,
                    // if we are going to save the result to a global register, we must
                    // allocate a temp register first so that argument passing can work.
                    alloc.alloc().map_err(|e| Error::from_syms(e, key_pos))?
                } else {
                    reg
                };
                let _first_temp = compile_args(span, md.clone(), symtable, codegen)?;

                let addr = codegen.emit(bytecode::make_nop(), key_pos);
                codegen.add_fixup(addr, Fixup::Call(ret_reg, key));

                if is_global {
                    codegen.emit(bytecode::make_move(reg, ret_reg), key_pos);
                }
            } else {
                let (is_global, _index) = reg.to_parts();
                let mut alloc = symtable.temp_scope();
                let ret_reg = if is_global {
                    alloc.alloc().map_err(|e| Error::from_syms(e, key_pos))?
                } else {
                    reg
                };
                let _first_temp = compile_args(span, md.clone(), symtable, codegen)?;
                let upcall = codegen.get_upcall(key, Some(etype), key_pos)?;
                codegen.emit(bytecode::make_upcall(upcall, ret_reg), key_pos);
                if is_global {
                    codegen.emit(bytecode::make_move(reg, ret_reg), key_pos);
                }
            }
            Ok(etype)
        }

        Expr::Double(span) => {
            let index = codegen.get_constant(Datum::Double(span.value), span.pos)?;
            codegen.emit(bytecode::make_load_constant(reg, index), span.pos);
            Ok(ExprType::Double)
        }

        Expr::Integer(span) => {
            match u16::try_from(span.value) {
                Ok(i) => {
                    codegen.emit(bytecode::make_load_integer(reg, i), span.pos);
                }
                Err(_) => {
                    let index = codegen.get_constant(Datum::Integer(span.value), span.pos)?;
                    codegen.emit(bytecode::make_load_constant(reg, index), span.pos);
                }
            }
            Ok(ExprType::Integer)
        }

        Expr::Symbol(span) => match symtable.get_local_or_global(&span.vref) {
            Ok((local, etype)) => {
                codegen.emit(bytecode::make_move(reg, local), span.pos);
                Ok(etype)
            }

            Err(syms::Error::UndefinedSymbol(..)) => {
                let key = SymbolKey::from(&span.vref.name);

                let Some(md) = symtable.get_callable(&key) else {
                    return Err(Error::UndefinedSymbol(span.pos, span.vref, RegisterScope::Global));
                };

                let Some(etype) = md.return_type() else {
                    return Err(Error::NotAFunction(span.pos, span.vref));
                };

                if !md.is_argless() {
                    return Err(Error::CallableSyntax(span.pos, md.clone()));
                }

                if md.is_user_defined() {
                    let addr = codegen.emit(bytecode::make_nop(), span.pos);
                    codegen.add_fixup(addr, Fixup::Call(reg, key));
                } else {
                    let upcall = codegen.get_upcall(key, Some(etype), span.pos)?;
                    let (is_global, _) = reg.to_parts();
                    if is_global {
                        let mut scope = symtable.temp_scope();
                        let temp = scope.alloc().map_err(|e| Error::from_syms(e, span.pos))?;
                        codegen.emit(bytecode::make_upcall(upcall, temp), span.pos);
                        codegen.emit(bytecode::make_move(reg, temp), span.pos);
                    } else {
                        codegen.emit(bytecode::make_upcall(upcall, reg), span.pos);
                    }
                }
                Ok(etype)
            }

            Err(e) => Err(Error::from_syms(e, span.pos)),
        },

        Expr::Text(span) => {
            let index = codegen.get_constant(Datum::Text(span.value), span.pos)?;
            codegen.emit(bytecode::make_load_integer(reg, index), span.pos);
            Ok(ExprType::Text)
        }

        _ => todo!(),
    }
}

/// Compiles a single expression, expecting it to be of a `target` type.  Applies casts if
/// possible.
pub(super) fn compile_expr_as_type(
    codegen: &mut Codegen,
    symtable: &mut TempSymtable<'_, '_, '_, '_, '_>,
    reg: Register,
    expr: Expr,
    target: ExprType,
) -> Result<()> {
    let epos = expr.start_pos();
    let etype = compile_expr(codegen, symtable, reg, expr)?;
    if etype == ExprType::Double && target.is_numerical() {
        if target == ExprType::Integer {
            codegen.emit(bytecode::make_double_to_integer(reg), epos);
        }
        Ok(())
    } else if etype == ExprType::Integer && target.is_numerical() {
        if target == ExprType::Double {
            codegen.emit(bytecode::make_integer_to_double(reg), epos);
        }
        Ok(())
    } else if etype == target {
        Ok(())
    } else {
        if target.is_numerical() {
            Err(Error::NotANumber(epos, etype))
        } else {
            Err(Error::TypeMismatch(epos, etype, target))
        }
    }
}
