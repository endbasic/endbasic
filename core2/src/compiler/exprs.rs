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
use crate::bytecode::{self, Register};
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
    symtable: &mut TempSymtable<'_, '_>,
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
    symtable: &mut TempSymtable<'_, '_>,
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

/// The type of unary operation waiting to be applied.
enum PendingUnaryKind {
    Negate,
    Not,
}

/// A pending unary operation waiting to be applied.
struct PendingUnaryOp {
    pos: LineCol,
    kind: PendingUnaryKind,
    make_boolean: Option<fn(Register, Register, Register) -> u32>,
    make_integer: fn(Register) -> u32,
    make_double: Option<fn(Register) -> u32>,
}

/// A pending binary operation waiting to be applied.
struct PendingBinaryOp {
    pos: LineCol,
    rhs: Expr,
    op_name: &'static str,
    make_boolean: Option<fn(Register, Register, Register) -> u32>,
    make_double: Option<fn(Register, Register, Register) -> u32>,
    make_integer: fn(Register, Register, Register) -> u32,
    make_text: Option<fn(Register, Register, Register) -> u32>,
}

/// A pending relational operation waiting to be applied.
struct PendingRelationalOp {
    pos: LineCol,
    rhs: Expr,
    op_name: &'static str,
    make_boolean: Option<fn(Register, Register, Register) -> u32>,
    make_double: Option<fn(Register, Register, Register) -> u32>,
    make_integer: Option<fn(Register, Register, Register) -> u32>,
    make_text: Option<fn(Register, Register, Register) -> u32>,
}

/// A pending expression operation waiting to be applied, used to flatten expression chains
/// and avoid recursive calls during processing.
enum PendingOp {
    Unary(PendingUnaryOp),
    Binary(PendingBinaryOp),
    Relational(PendingRelationalOp),
}

/// Peels the expression chain into a vector of pending ops to avoid deep recursion.
///
/// Returns the input `expr` holding the innermost non-op expression and the list of
/// pending ops.
fn peel_ops(mut expr: Expr) -> (Expr, Vec<PendingOp>) {
    let mut pending: Vec<PendingOp> = vec![];
    loop {
        match expr {
            Expr::Add(span) => {
                let span = *span;
                pending.push(PendingOp::Binary(PendingBinaryOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: "+",
                    make_boolean: None,
                    make_double: Some(bytecode::make_add_double),
                    make_integer: bytecode::make_add_integer,
                    make_text: Some(bytecode::make_concat),
                }));
                expr = span.lhs;
            }

            Expr::And(span) => {
                let span = *span;
                pending.push(PendingOp::Binary(PendingBinaryOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: "AND",
                    make_boolean: Some(bytecode::make_bitwise_and),
                    make_double: None,
                    make_integer: bytecode::make_bitwise_and,
                    make_text: None,
                }));
                expr = span.lhs;
            }

            Expr::Divide(span) => {
                let span = *span;
                pending.push(PendingOp::Binary(PendingBinaryOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: "/",
                    make_boolean: None,
                    make_double: Some(bytecode::make_divide_double),
                    make_integer: bytecode::make_divide_integer,
                    make_text: None,
                }));
                expr = span.lhs;
            }

            Expr::Equal(span) => {
                let span = *span;
                pending.push(PendingOp::Relational(PendingRelationalOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: "=",
                    make_boolean: Some(bytecode::make_equal_boolean),
                    make_double: Some(bytecode::make_equal_double),
                    make_integer: Some(bytecode::make_equal_integer),
                    make_text: Some(bytecode::make_equal_text),
                }));
                expr = span.lhs;
            }

            Expr::Greater(span) => {
                let span = *span;
                pending.push(PendingOp::Relational(PendingRelationalOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: ">",
                    make_boolean: None,
                    make_double: Some(bytecode::make_greater_double),
                    make_integer: Some(bytecode::make_greater_integer),
                    make_text: Some(bytecode::make_greater_text),
                }));
                expr = span.lhs;
            }

            Expr::GreaterEqual(span) => {
                let span = *span;
                pending.push(PendingOp::Relational(PendingRelationalOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: ">=",
                    make_boolean: None,
                    make_double: Some(bytecode::make_greater_equal_double),
                    make_integer: Some(bytecode::make_greater_equal_integer),
                    make_text: Some(bytecode::make_greater_equal_text),
                }));
                expr = span.lhs;
            }

            Expr::Less(span) => {
                let span = *span;
                pending.push(PendingOp::Relational(PendingRelationalOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: "<",
                    make_boolean: None,
                    make_double: Some(bytecode::make_less_double),
                    make_integer: Some(bytecode::make_less_integer),
                    make_text: Some(bytecode::make_less_text),
                }));
                expr = span.lhs;
            }

            Expr::LessEqual(span) => {
                let span = *span;
                pending.push(PendingOp::Relational(PendingRelationalOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: "<=",
                    make_boolean: None,
                    make_double: Some(bytecode::make_less_equal_double),
                    make_integer: Some(bytecode::make_less_equal_integer),
                    make_text: Some(bytecode::make_less_equal_text),
                }));
                expr = span.lhs;
            }

            Expr::Modulo(span) => {
                let span = *span;
                pending.push(PendingOp::Binary(PendingBinaryOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: "MOD",
                    make_boolean: None,
                    make_double: Some(bytecode::make_modulo_double),
                    make_integer: bytecode::make_modulo_integer,
                    make_text: None,
                }));
                expr = span.lhs;
            }

            Expr::Multiply(span) => {
                let span = *span;
                pending.push(PendingOp::Binary(PendingBinaryOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: "*",
                    make_boolean: None,
                    make_double: Some(bytecode::make_multiply_double),
                    make_integer: bytecode::make_multiply_integer,
                    make_text: None,
                }));
                expr = span.lhs;
            }

            Expr::Negate(span) => {
                let span = *span;
                pending.push(PendingOp::Unary(PendingUnaryOp {
                    pos: span.pos,
                    kind: PendingUnaryKind::Negate,
                    make_boolean: None,
                    make_integer: bytecode::make_negate_integer,
                    make_double: Some(bytecode::make_negate_double),
                }));
                expr = span.expr;
            }

            Expr::Not(span) => {
                let span = *span;
                pending.push(PendingOp::Unary(PendingUnaryOp {
                    pos: span.pos,
                    kind: PendingUnaryKind::Not,
                    make_boolean: Some(bytecode::make_bitwise_xor),
                    make_integer: bytecode::make_bitwise_not,
                    make_double: None,
                }));
                expr = span.expr;
            }

            Expr::NotEqual(span) => {
                let span = *span;
                pending.push(PendingOp::Relational(PendingRelationalOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: "<>",
                    make_boolean: Some(bytecode::make_not_equal_boolean),
                    make_double: Some(bytecode::make_not_equal_double),
                    make_integer: Some(bytecode::make_not_equal_integer),
                    make_text: Some(bytecode::make_not_equal_text),
                }));
                expr = span.lhs;
            }

            Expr::Or(span) => {
                let span = *span;
                pending.push(PendingOp::Binary(PendingBinaryOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: "OR",
                    make_boolean: Some(bytecode::make_bitwise_or),
                    make_double: None,
                    make_integer: bytecode::make_bitwise_or,
                    make_text: None,
                }));
                expr = span.lhs;
            }

            Expr::Power(span) => {
                let span = *span;
                pending.push(PendingOp::Binary(PendingBinaryOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: "^",
                    make_boolean: None,
                    make_double: Some(bytecode::make_power_double),
                    make_integer: bytecode::make_power_integer,
                    make_text: None,
                }));
                expr = span.lhs;
            }

            Expr::ShiftLeft(span) => {
                let span = *span;
                pending.push(PendingOp::Binary(PendingBinaryOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: "<<",
                    make_boolean: None,
                    make_double: None,
                    make_integer: bytecode::make_shift_left,
                    make_text: None,
                }));
                expr = span.lhs;
            }

            Expr::ShiftRight(span) => {
                let span = *span;
                pending.push(PendingOp::Binary(PendingBinaryOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: ">>",
                    make_boolean: None,
                    make_double: None,
                    make_integer: bytecode::make_shift_right,
                    make_text: None,
                }));
                expr = span.lhs;
            }
            Expr::Subtract(span) => {
                let span = *span;
                pending.push(PendingOp::Binary(PendingBinaryOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: "-",
                    make_boolean: None,
                    make_double: Some(bytecode::make_subtract_double),
                    make_integer: bytecode::make_subtract_integer,
                    make_text: None,
                }));
                expr = span.lhs;
            }

            Expr::Xor(span) => {
                let span = *span;
                pending.push(PendingOp::Binary(PendingBinaryOp {
                    pos: span.pos,
                    rhs: span.rhs,
                    op_name: "XOR",
                    make_boolean: Some(bytecode::make_bitwise_xor),
                    make_double: None,
                    make_integer: bytecode::make_bitwise_xor,
                    make_text: None,
                }));
                expr = span.lhs;
            }

            _ => break,
        }
    }
    (expr, pending)
}

/// Emits a cast in `reg` to convert from `from` to `to` if these are numerical types.
///
/// Returns true if the conversion is valid, regardless of whether a cast was needed.
fn cast_numerical_type(
    codegen: &mut Codegen,
    reg: Register,
    from: ExprType,
    to: ExprType,
    pos: LineCol,
) -> bool {
    match (from, to) {
        (ExprType::Double, ExprType::Integer) => {
            codegen.emit(bytecode::make_double_to_integer(reg), pos);
            true
        }
        (ExprType::Integer, ExprType::Double) => {
            codegen.emit(bytecode::make_integer_to_double(reg), pos);
            true
        }
        (ExprType::Double, ExprType::Double) | (ExprType::Integer, ExprType::Integer) => true,
        _ => false,
    }
}

/// Resolves the numeric operand type for a binary operation and emits any required casts.
fn resolve_numeric_binary_type(
    codegen: &mut Codegen,
    reg: Register,
    etype: ExprType,
    rtemp: Register,
    rtype: ExprType,
    rpos: LineCol,
    op_pos: LineCol,
) -> Option<ExprType> {
    match (etype, rtype) {
        (ExprType::Double, ExprType::Double) => Some(ExprType::Double),
        (ExprType::Integer, ExprType::Integer) => Some(ExprType::Integer),
        (ExprType::Double, ExprType::Integer) => {
            let cast_ok =
                cast_numerical_type(codegen, rtemp, ExprType::Integer, ExprType::Double, rpos);
            debug_assert!(cast_ok);
            Some(ExprType::Double)
        }
        (ExprType::Integer, ExprType::Double) => {
            let cast_ok =
                cast_numerical_type(codegen, reg, ExprType::Integer, ExprType::Double, op_pos);
            debug_assert!(cast_ok);
            Some(ExprType::Double)
        }
        _ => None,
    }
}

/// Processes `pending` binary ops from innermost to outermost, using `reg` as the
/// accumulator.
///
/// This avoids the deep recursion that would arise if we compiled binary op chains
/// by recursing on the lhs.
fn compile_pending_ops(
    codegen: &mut Codegen,
    symtable: &mut TempSymtable<'_, '_>,
    reg: Register,
    mut etype: ExprType,
    mut pending: Vec<PendingOp>,
) -> Result<ExprType> {
    while let Some(op) = pending.pop() {
        match op {
            PendingOp::Unary(op) => {
                let result_type = match etype {
                    ExprType::Boolean if op.make_boolean.is_some() => ExprType::Boolean,
                    ExprType::Double if op.make_double.is_some() => ExprType::Double,
                    ExprType::Integer => ExprType::Integer,
                    _ => match op.kind {
                        PendingUnaryKind::Negate => return Err(Error::NotANumber(op.pos, etype)),
                        PendingUnaryKind::Not => {
                            return Err(Error::TypeMismatch(op.pos, etype, ExprType::Integer));
                        }
                    },
                };
                match result_type {
                    ExprType::Boolean => {
                        let mut scope = symtable.temp_scope();
                        let temp = scope.alloc().map_err(|e| Error::from_syms(e, op.pos))?;
                        codegen.emit_value(temp, ConstantDatum::Integer(1), op.pos)?;
                        codegen.emit(op.make_boolean.unwrap()(reg, reg, temp), op.pos);
                    }
                    ExprType::Double => {
                        codegen.emit(op.make_double.unwrap()(reg), op.pos);
                    }
                    ExprType::Integer => {
                        codegen.emit((op.make_integer)(reg), op.pos);
                    }
                    ExprType::Text => unreachable!(),
                }
                etype = result_type;
            }
            PendingOp::Binary(op) => {
                let rpos = op.rhs.start_pos();
                let mut scope = symtable.temp_scope();
                let rtemp = scope.alloc().map_err(|e| Error::from_syms(e, rpos))?;
                let rtype = compile_expr(codegen, symtable, rtemp, op.rhs)?;

                let result_type = match (etype, rtype) {
                    (ExprType::Boolean, ExprType::Boolean) if op.make_boolean.is_some() => {
                        ExprType::Boolean
                    }
                    (ExprType::Text, ExprType::Text) if op.make_text.is_some() => ExprType::Text,
                    (_, _) if op.make_double.is_some() => {
                        match resolve_numeric_binary_type(
                            codegen, reg, etype, rtemp, rtype, rpos, op.pos,
                        ) {
                            Some(v) => v,
                            None => {
                                return Err(Error::BinaryOpType(op.pos, op.op_name, etype, rtype));
                            }
                        }
                    }
                    (ExprType::Integer, ExprType::Integer) => ExprType::Integer,
                    _ => return Err(Error::BinaryOpType(op.pos, op.op_name, etype, rtype)),
                };

                match result_type {
                    ExprType::Boolean => {
                        codegen.emit(op.make_boolean.unwrap()(reg, reg, rtemp), op.pos);
                    }
                    ExprType::Double => {
                        codegen.emit(op.make_double.unwrap()(reg, reg, rtemp), op.pos);
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

            PendingOp::Relational(op) => {
                let rpos = op.rhs.start_pos();
                let mut scope = symtable.temp_scope();
                let rtemp = scope.alloc().map_err(|e| Error::from_syms(e, rpos))?;
                let rtype = compile_expr(codegen, symtable, rtemp, op.rhs)?;

                let make_opcode = match (etype, rtype) {
                    (ExprType::Boolean, ExprType::Boolean) if op.make_boolean.is_some() => {
                        op.make_boolean.unwrap()
                    }

                    (ExprType::Text, ExprType::Text) if op.make_text.is_some() => {
                        op.make_text.unwrap()
                    }

                    (_, _) if op.make_double.is_some() || op.make_integer.is_some() => {
                        match resolve_numeric_binary_type(
                            codegen, reg, etype, rtemp, rtype, rpos, op.pos,
                        ) {
                            Some(ExprType::Double) => op.make_double.expect("Must exist"),
                            Some(ExprType::Integer) => op.make_integer.expect("Must exist"),
                            _ => {
                                return Err(Error::BinaryOpType(op.pos, op.op_name, etype, rtype));
                            }
                        }
                    }

                    _ => return Err(Error::BinaryOpType(op.pos, op.op_name, etype, rtype)),
                };

                codegen.emit(make_opcode(reg, reg, rtemp), op.pos);
                etype = ExprType::Boolean;
            }
        }
    }

    Ok(etype)
}

/// Compiles a single expression `expr` and leaves its value in `reg`.
///
/// For left-recursive binary operations (like `a + b + c`), this function iterates rather
/// than recurses so that very long expression chains do not overflow the call stack.
pub(super) fn compile_expr(
    codegen: &mut Codegen,
    symtable: &mut TempSymtable<'_, '_>,
    reg: Register,
    expr: Expr,
) -> Result<ExprType> {
    let (expr, pending) = peel_ops(expr);

    let etype = match expr {
        Expr::Add(..)
        | Expr::And(..)
        | Expr::Divide(..)
        | Expr::Equal(..)
        | Expr::Greater(..)
        | Expr::GreaterEqual(..)
        | Expr::Less(..)
        | Expr::LessEqual(..)
        | Expr::Modulo(..)
        | Expr::Multiply(..)
        | Expr::Negate(..)
        | Expr::Not(..)
        | Expr::NotEqual(..)
        | Expr::Or(..)
        | Expr::Power(..)
        | Expr::ShiftLeft(..)
        | Expr::ShiftRight(..)
        | Expr::Subtract(..)
        | Expr::Xor(..) => unreachable!("Peeled by peel_ops"),

        Expr::Boolean(span) => {
            codegen.emit_value(reg, ConstantDatum::Boolean(span.value), span.pos)?;
            Ok(ExprType::Boolean)
        }

        Expr::Call(span) => {
            let key = SymbolKey::from(&span.vref.name);
            let key_pos = span.vref_pos;

            if let Some(md) = symtable.get_callable(&key) {
                let md = md.clone();

                let Some(etype) = md.return_type() else {
                    return Err(Error::NotAFunction(span.vref_pos, span.vref));
                };

                if !span.vref.accepts_callable(Some(etype)) {
                    return Err(Error::IncompatibleTypeAnnotationInReference(
                        span.vref_pos,
                        span.vref,
                    ));
                }

                if md.is_argless() {
                    return Err(Error::CallableSyntax(span.vref_pos, md.as_ref().clone()));
                }

                let is_user_defined = md.is_user_defined();
                let mut call_scope = symtable.temp_scope();
                let ret_reg = call_scope.alloc().map_err(|e| Error::from_syms(e, key_pos))?;
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
                if reg != ret_reg {
                    codegen.emit(bytecode::make_move(reg, ret_reg), key_pos);
                }

                Ok(etype)
            } else {
                match symtable.get_local_or_global(&span.vref) {
                    Ok((arr_reg, SymbolPrototype::Array(info))) => compile_array_access(
                        codegen, symtable, reg, key_pos, arr_reg, &info, span.args,
                    ),
                    Ok((_, SymbolPrototype::Scalar(_))) => {
                        return Err(Error::NotAFunction(span.vref_pos, span.vref));
                    }
                    Err(syms::Error::UndefinedSymbol(..)) => {
                        return Err(Error::UndefinedSymbol(span.vref_pos, span.vref));
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
                    return Err(Error::UndefinedSymbol(span.pos, span.vref));
                };

                let Some(etype) = md.return_type() else {
                    return Err(Error::NotAFunction(span.pos, span.vref));
                };

                if !span.vref.accepts_callable(Some(etype)) {
                    return Err(Error::IncompatibleTypeAnnotationInReference(span.pos, span.vref));
                }

                if !md.is_argless() {
                    return Err(Error::CallableSyntax(span.pos, md.as_ref().clone()));
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
    }?;

    compile_pending_ops(codegen, symtable, reg, etype, pending)
}

/// Compiles a single expression, expecting it to be of a `target` type.  Applies casts if
/// possible.
pub(super) fn compile_expr_as_type(
    codegen: &mut Codegen,
    symtable: &mut TempSymtable<'_, '_>,
    reg: Register,
    expr: Expr,
    target: ExprType,
) -> Result<()> {
    let epos = expr.start_pos();
    let etype = compile_expr(codegen, symtable, reg, expr)?;
    if etype == target || cast_numerical_type(codegen, reg, etype, target, epos) {
        Ok(())
    } else {
        if target.is_numerical() {
            Err(Error::NotANumber(epos, etype))
        } else {
            Err(Error::TypeMismatch(epos, etype, target))
        }
    }
}
