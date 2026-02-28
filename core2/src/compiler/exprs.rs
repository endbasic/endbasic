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

use crate::ast::{Expr, ExprType};
use crate::bytecode::{self, Register, RegisterScope};
use crate::compiler::args::compile_args;
use crate::compiler::codegen::{Codegen, Fixup};
use crate::compiler::syms::{self, SymbolKey, SymbolPrototype, TempScope, TempSymtable};
use crate::compiler::{Error, Result};
use crate::mem::ConstantDatum;
use crate::reader::LineCol;

/// Compiles `exprs` into consecutive integer registers allocated from `scope` and returns the
/// first register.  The caller must guarantee that `exprs` is non-empty.
pub(super) fn compile_integer_exprs(
    codegen: &mut Codegen,
    symtable: &mut TempSymtable<'_, '_, '_, '_, '_>,
    scope: &mut TempScope,
    pos: LineCol,
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
    key_pos: LineCol,
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

/// A pending arithmetic binary operation waiting to be applied, used to flatten
/// expressions and avoid recursive calls during processing.
struct PendingBinaryOp {
    pos: LineCol,
    rhs: Expr,
    op_name: &'static str,
    make_double: fn(Register, Register, Register) -> u32,
    make_integer: fn(Register, Register, Register) -> u32,
    make_text: Option<fn(Register, Register, Register) -> u32>,
}

/// Peels the left-recursive chain of arithmetic binary ops into a vector of pending
/// binary ops to avoid deep recursion.
///
/// Returns the input `expr` holding the leftmost non-binary expression and the list
/// of pending ops.
fn peel_binary_ops(mut expr: Expr) -> (Expr, Vec<PendingBinaryOp>) {
    let mut pending: Vec<PendingBinaryOp> = vec![];
    #[allow(clippy::while_let_loop)]
    loop {
        match expr {
            Expr::Add(span) => {
                let span = *span;
                pending.push(PendingBinaryOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: "+",
                    make_double: bytecode::make_add_double,
                    make_integer: bytecode::make_add_integer,
                    make_text: Some(bytecode::make_concat),
                });
                expr = span.lhs;
            }
            _ => break,
        }
    }
    (expr, pending)
}

/// Processes `pending` arithmetic binary ops from innermost to outermost, using
/// `reg` as the accumulator.
///
/// This avoids the deep recursion that would arise if we compiled binary op chains
/// by recursing on the lhs.
fn compile_pending_ops(
    codegen: &mut Codegen,
    symtable: &mut TempSymtable<'_, '_, '_, '_, '_>,
    reg: Register,
    mut etype: ExprType,
    mut pending: Vec<PendingBinaryOp>,
) -> Result<ExprType> {
    while let Some(op) = pending.pop() {
        let rpos = op.rhs.start_pos();
        let mut scope = symtable.temp_scope();
        let rtemp = scope.alloc().map_err(|e| Error::from_syms(e, rpos))?;
        let rtype = compile_expr(codegen, symtable, rtemp, op.rhs)?;

        let result_type = match (etype, rtype) {
            (ExprType::Double, ExprType::Double) => ExprType::Double,
            (ExprType::Integer, ExprType::Integer) => ExprType::Integer,
            (ExprType::Text, ExprType::Text) if op.make_text.is_some() => ExprType::Text,
            (ExprType::Double, ExprType::Integer) => {
                codegen.emit(bytecode::make_integer_to_double(rtemp), rpos);
                ExprType::Double
            }
            (ExprType::Integer, ExprType::Double) => {
                codegen.emit(bytecode::make_integer_to_double(reg), op.pos);
                ExprType::Double
            }
            _ => return Err(Error::BinaryOpType(op.pos, op.op_name, etype, rtype)),
        };

        match result_type {
            ExprType::Boolean => unreachable!(),
            ExprType::Double => {
                codegen.emit((op.make_double)(reg, reg, rtemp), op.pos);
            }
            ExprType::Integer => {
                codegen.emit((op.make_integer)(reg, reg, rtemp), op.pos);
            }
            ExprType::Text => {
                codegen.emit(op.make_text.unwrap()(reg, reg, rtemp), op.pos);
            }
        }

        etype = result_type;
    }

    Ok(etype)
}

/// Compiles a single expression `expr` and leaves its value in `reg`.
///
/// For left-recursive arithmetic binary operations (like `a + b + c`), this function
/// iterates rather than recurses so that very long expression chains do not overflow
/// the call stack.
pub(super) fn compile_expr(
    codegen: &mut Codegen,
    symtable: &mut TempSymtable<'_, '_, '_, '_, '_>,
    reg: Register,
    expr: Expr,
) -> Result<ExprType> {
    let (expr, pending) = peel_binary_ops(expr);

    let etype = match expr {
        Expr::Add(..) => unreachable!("Peeled by peel_binary_ops"),

        Expr::Boolean(span) => {
            codegen.emit_value(reg, ConstantDatum::Boolean(span.value), span.pos)?;
            Ok(ExprType::Boolean)
        }

        Expr::Call(span) => {
            let key = SymbolKey::from(&span.vref.name);
            let key_pos = span.vref_pos;

            if let Some(md) = symtable.get_callable(&key) {
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
                let (_first_temp, arg_linecols) =
                    compile_args(span, md.clone(), symtable, codegen)?;

                if is_user_defined {
                    let addr = codegen.emit(bytecode::make_nop(), key_pos);
                    codegen.set_arg_linecols(addr, arg_linecols);
                    codegen.add_fixup(addr, Fixup::Call(ret_reg, key));
                } else {
                    let upcall = codegen.get_upcall(key, Some(etype), key_pos)?;
                    let addr = codegen.emit(bytecode::make_upcall(upcall, ret_reg), key_pos);
                    codegen.set_arg_linecols(addr, arg_linecols);
                }
                if is_global {
                    codegen.emit(bytecode::make_move(reg, ret_reg), key_pos);
                }

                Ok(etype)
            } else {
                match symtable.get_local_or_global(&span.vref) {
                    Ok((arr_reg, SymbolPrototype::Array(info))) => compile_array_access(
                        codegen, symtable, reg, key_pos, arr_reg, &info, span.args,
                    ),
                    Err(syms::Error::UndefinedSymbol(..)) | Ok((_, SymbolPrototype::Scalar(_))) => {
                        return Err(Error::UndefinedSymbol(
                            span.vref_pos,
                            span.vref,
                            RegisterScope::Global,
                        ));
                    }
                    Err(e) => return Err(Error::from_syms(e, key_pos)),
                }
            }
        }

        Expr::Double(span) => {
            codegen.emit_value(reg, ConstantDatum::Double(span.value), span.pos)?;
            Ok(ExprType::Double)
        }

        Expr::Integer(span) => {
            codegen.emit_value(reg, ConstantDatum::Integer(span.value), span.pos)?;
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
            codegen.emit_value(reg, ConstantDatum::Text(span.value), span.pos)?;
            Ok(ExprType::Text)
        }

        _ => todo!(),
    }?;

    compile_pending_ops(codegen, symtable, reg, etype, pending)
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
