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

//! Functions to convert expressions into bytecode.

use crate::ast::{BinaryOpSpan, Expr, ExprType};
use crate::bytecode::{self, Register, RegisterScope};
use crate::compiler::args::compile_args;
use crate::compiler::codegen::{Codegen, Fixup};
use crate::compiler::syms::{self, SymbolKey, SymbolPrototype, TempScope, TempSymtable};
use crate::compiler::{Error, Result};
use crate::mem::Datum;
use std::convert::TryFrom;

/// Compiles `exprs` into consecutive integer registers allocated from `scope` and returns the
/// first register.  The caller must guarantee that `exprs` is non-empty.
pub(super) fn compile_integer_exprs(
    codegen: &mut Codegen,
    symtable: &mut TempSymtable<'_, '_, '_, '_, '_>,
    scope: &mut TempScope,
    pos: crate::reader::LineCol,
    exprs: impl Iterator<Item = Expr>,
) -> Result<Register> {
    let mut first_reg = None;
    for expr in exprs {
        let reg = scope.alloc().map_err(|e| Error::from_syms(e, pos))?;
        if first_reg.is_none() {
            first_reg = Some(reg);
        }
        compile_expr_as_type(codegen, symtable, reg, expr, ExprType::Integer)?;
    }
    Ok(first_reg.expect("Must have at least one expression"))
}

/// Compiles an array element access expression into `reg`.
fn compile_array_access(
    codegen: &mut Codegen,
    symtable: &mut TempSymtable<'_, '_, '_, '_, '_>,
    reg: Register,
    key_pos: crate::reader::LineCol,
    arr_reg: Register,
    info: &syms::ArrayInfo,
    args: Vec<crate::ast::ArgSpan>,
) -> Result<ExprType> {
    if args.len() != info.ndims {
        return Err(Error::WrongNumberOfSubscripts(key_pos, info.ndims, args.len()));
    }

    let mut outer_scope = symtable.temp_scope();
    let first_sub_reg = compile_integer_exprs(
        codegen,
        symtable,
        &mut outer_scope,
        key_pos,
        args.into_iter().map(|a| a.expr.expect("Array subscripts must have expressions")),
    )?;
    codegen.emit(bytecode::make_load_array(reg, arr_reg, first_sub_reg), key_pos);
    Ok(info.subtype)
}

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
                match symtable.get_local_or_global(&span.vref) {
                    Ok((arr_reg, SymbolPrototype::Array(info))) => {
                        return compile_array_access(
                            codegen, symtable, reg, key_pos, arr_reg, &info, span.args,
                        );
                    }
                    Err(syms::Error::UndefinedSymbol(..)) | Ok((_, SymbolPrototype::Scalar(_))) => {
                        return Err(Error::UndefinedSymbol(
                            span.vref_pos,
                            span.vref,
                            RegisterScope::Global,
                        ));
                    }
                    Err(e) => return Err(Error::from_syms(e, key_pos)),
                }
            };

            let Some(etype) = md.return_type() else {
                return Err(Error::NotAFunction(span.vref_pos, span.vref));
            };

            if md.is_argless() {
                return Err(Error::CallableSyntax(span.vref_pos, md.clone()));
            }

            let is_user_defined = md.is_user_defined();
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
            compile_args(span, md.clone(), symtable, codegen)?;

            if is_user_defined {
                let addr = codegen.emit(bytecode::make_nop(), key_pos);
                codegen.add_fixup(addr, Fixup::Call(ret_reg, key));
            } else {
                let upcall = codegen.get_upcall(key, Some(etype), key_pos)?;
                codegen.emit(bytecode::make_upcall(upcall, ret_reg), key_pos);
            }
            if is_global {
                codegen.emit(bytecode::make_move(reg, ret_reg), key_pos);
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

        Expr::Negate(span) => {
            let pos = span.pos;
            let etype = compile_expr(codegen, symtable, reg, span.expr)?;
            match etype {
                ExprType::Double => {
                    codegen.emit(bytecode::make_negate_double(reg), pos);
                }
                ExprType::Integer => {
                    codegen.emit(bytecode::make_negate_integer(reg), pos);
                }
                _ => {
                    return Err(Error::NotANumber(pos, etype));
                }
            }
            Ok(etype)
        }

        Expr::Symbol(span) => match symtable.get_local_or_global(&span.vref) {
            Ok((local, SymbolPrototype::Scalar(etype))) => {
                codegen.emit(bytecode::make_move(reg, local), span.pos);
                Ok(etype)
            }

            Ok((_, SymbolPrototype::Array(_))) => {
                Err(Error::ArrayUsedAsScalar(span.pos, span.vref))
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
