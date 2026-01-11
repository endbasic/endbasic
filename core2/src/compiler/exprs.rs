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
use crate::compiler::codegen::{Codegen, Fixup};
use crate::compiler::syms::{SymbolKey, TempSymtable};
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

            if md.is_user_defined() {
                let addr = codegen.emit(bytecode::make_nop(), span.vref_pos);
                codegen.add_fixup(addr, Fixup::Call(reg, key));
            } else {
                todo!("Function upcalls not implemented yet");
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

        Expr::Symbol(span) => {
            let (local, etype) = symtable
                .get_local_or_global(&span.vref)
                .map_err(|e| Error::from_syms(e, span.pos))?;
            codegen.emit(bytecode::make_move(reg, local), span.pos);
            Ok(etype)
        }

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
