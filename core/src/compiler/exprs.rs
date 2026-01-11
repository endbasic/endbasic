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

//! Functions to convert expressions into bytecode.

use super::{Error, ExprType, Fixup, Result, SymbolPrototype, SymbolsTable};
use crate::ast::*;
use crate::bytecode::*;
use crate::compiler::compile_function_args;
use crate::parser::argspans_to_exprs;
use crate::reader::LineCol;
use crate::syms::SymbolKey;
use std::collections::HashMap;

/// Adjusts `src` fixups by -1 if `adjust` is true else leaves them as is, and then merges the
/// results into `dest`.
fn merge_fixups(dest: &mut HashMap<Address, Fixup>, src: HashMap<Address, Fixup>, adjust: bool) {
    let expected_size = dest.len() + src.len();
    if !adjust {
        dest.extend(src);
    } else {
        for (pc, fixup) in src {
            let previous = dest.insert(pc - 1, fixup);
            debug_assert!(previous.is_none());
        }
    }
    debug_assert_eq!(dest.len(), expected_size);
}

/// Compiles the indices used to address an array.
pub(super) fn compile_array_indices(
    instrs: &mut Vec<Instruction>,
    fixups: &mut HashMap<Address, Fixup>,
    symtable: &SymbolsTable,
    exp_nargs: usize,
    args: Vec<Expr>,
    name_pos: LineCol,
) -> Result<()> {
    if exp_nargs != args.len() {
        return Err(Error::ArrayIndexSubscriptsError(name_pos, args.len(), exp_nargs));
    }

    for arg in args.into_iter().rev() {
        let arg_pos = arg.start_pos();
        match compile_expr(instrs, fixups, symtable, arg, false)? {
            ExprType::Integer => (),
            ExprType::Double => {
                instrs.push(Instruction::DoubleToInteger);
            }
            itype => {
                return Err(Error::NotANumber(arg_pos, itype));
            }
        }
    }

    Ok(())
}

/// Compiles a logical or bitwise unary operator and appends its instructions to `instrs`.
fn compile_not_op(
    instrs: &mut Vec<Instruction>,
    fixups: &mut HashMap<Address, Fixup>,
    symtable: &SymbolsTable,
    span: UnaryOpSpan,
) -> Result<ExprType> {
    let expr_type = compile_expr(instrs, fixups, symtable, span.expr, false)?;
    match expr_type {
        ExprType::Boolean => {
            instrs.push(Instruction::LogicalNot(span.pos));
            Ok(ExprType::Boolean)
        }
        ExprType::Integer => {
            instrs.push(Instruction::BitwiseNot(span.pos));
            Ok(ExprType::Integer)
        }
        _ => Err(Error::UnaryOpTypeError(span.pos, "NOT", expr_type)),
    }
}

/// Compiles a negate operator and appends its instructions to `instrs`.
fn compile_neg_op(
    instrs: &mut Vec<Instruction>,
    fixups: &mut HashMap<Address, Fixup>,
    symtable: &SymbolsTable,
    span: UnaryOpSpan,
) -> Result<ExprType> {
    let expr_type = compile_expr(instrs, fixups, symtable, span.expr, false)?;
    match expr_type {
        ExprType::Double => {
            instrs.push(Instruction::NegateDouble(span.pos));
            Ok(ExprType::Double)
        }
        ExprType::Integer => {
            instrs.push(Instruction::NegateInteger(span.pos));
            Ok(ExprType::Integer)
        }
        _ => Err(Error::UnaryOpTypeError(span.pos, "negate", expr_type)),
    }
}

/// Compiles a logical binary operator and appends its instructions to `instrs`.
fn compile_logical_binary_op<F1: Fn(LineCol) -> Instruction, F2: Fn(LineCol) -> Instruction>(
    instrs: &mut Vec<Instruction>,
    fixups: &mut HashMap<Address, Fixup>,
    symtable: &SymbolsTable,
    logical_make_inst: F1,
    bitwise_make_inst: F2,
    span: BinaryOpSpan,
    op_name: &'static str,
) -> Result<ExprType> {
    let lhs_type = compile_expr(instrs, fixups, symtable, span.lhs, false)?;
    let rhs_type = compile_expr(instrs, fixups, symtable, span.rhs, false)?;
    match (lhs_type, rhs_type) {
        (ExprType::Boolean, ExprType::Boolean) => {
            instrs.push(logical_make_inst(span.pos));
            Ok(ExprType::Boolean)
        }
        (ExprType::Integer, ExprType::Integer) => {
            instrs.push(bitwise_make_inst(span.pos));
            Ok(ExprType::Integer)
        }
        (_, _) => Err(Error::BinaryOpTypeError(span.pos, op_name, lhs_type, rhs_type)),
    }
}

/// Compiles an equality binary operator and appends its instructions to `instrs`.
#[allow(clippy::too_many_arguments)]
fn compile_equality_binary_op<
    F1: Fn(LineCol) -> Instruction,
    F2: Fn(LineCol) -> Instruction,
    F3: Fn(LineCol) -> Instruction,
    F4: Fn(LineCol) -> Instruction,
>(
    instrs: &mut Vec<Instruction>,
    fixups: &mut HashMap<Address, Fixup>,
    symtable: &SymbolsTable,
    boolean_make_inst: F1,
    double_make_inst: F2,
    integer_make_inst: F3,
    text_make_inst: F4,
    span: BinaryOpSpan,
    op_name: &'static str,
) -> Result<ExprType> {
    let lhs_type = compile_expr(instrs, fixups, symtable, span.lhs, false)?;
    let pc = instrs.len();
    instrs.push(Instruction::Nop);

    let mut keep_nop = false;
    let mut extra_fixups = HashMap::default();
    let rhs_type = compile_expr(instrs, &mut extra_fixups, symtable, span.rhs, false)?;
    let result = match (lhs_type, rhs_type) {
        (lhs_type, rhs_type) if lhs_type == rhs_type => lhs_type,

        (ExprType::Double, ExprType::Integer) => {
            instrs.push(Instruction::IntegerToDouble);
            ExprType::Double
        }

        (ExprType::Integer, ExprType::Double) => {
            instrs[pc] = Instruction::IntegerToDouble;
            keep_nop = true;
            ExprType::Double
        }

        (_, _) => {
            return Err(Error::BinaryOpTypeError(span.pos, op_name, lhs_type, rhs_type));
        }
    };

    if !keep_nop {
        let nop = instrs.remove(pc);
        debug_assert_eq!(std::mem::discriminant(&Instruction::Nop), std::mem::discriminant(&nop));
    }
    merge_fixups(fixups, extra_fixups, !keep_nop);

    match result {
        ExprType::Boolean => instrs.push(boolean_make_inst(span.pos)),
        ExprType::Double => instrs.push(double_make_inst(span.pos)),
        ExprType::Integer => instrs.push(integer_make_inst(span.pos)),
        ExprType::Text => instrs.push(text_make_inst(span.pos)),
    };

    Ok(ExprType::Boolean)
}

/// Compiles a relational binary operator and appends its instructions to `instrs`.
#[allow(clippy::too_many_arguments)]
fn compile_relational_binary_op<
    F1: Fn(LineCol) -> Instruction,
    F2: Fn(LineCol) -> Instruction,
    F3: Fn(LineCol) -> Instruction,
>(
    instrs: &mut Vec<Instruction>,
    fixups: &mut HashMap<Address, Fixup>,
    symtable: &SymbolsTable,
    double_make_inst: F1,
    integer_make_inst: F2,
    text_make_inst: F3,
    span: BinaryOpSpan,
    op_name: &'static str,
) -> Result<ExprType> {
    let lhs_type = compile_expr(instrs, fixups, symtable, span.lhs, false)?;
    let pc = instrs.len();
    instrs.push(Instruction::Nop);

    let mut keep_nop = false;
    let mut extra_fixups = HashMap::default();
    let rhs_type = compile_expr(instrs, &mut extra_fixups, symtable, span.rhs, false)?;
    let result = match (lhs_type, rhs_type) {
        // Boolean is explicitly excluded here.
        (ExprType::Double, ExprType::Double) => ExprType::Double,
        (ExprType::Integer, ExprType::Integer) => ExprType::Integer,
        (ExprType::Text, ExprType::Text) => ExprType::Text,

        (ExprType::Double, ExprType::Integer) => {
            instrs.push(Instruction::IntegerToDouble);
            ExprType::Double
        }

        (ExprType::Integer, ExprType::Double) => {
            instrs[pc] = Instruction::IntegerToDouble;
            keep_nop = true;
            ExprType::Double
        }

        (_, _) => {
            return Err(Error::BinaryOpTypeError(span.pos, op_name, lhs_type, rhs_type));
        }
    };

    if !keep_nop {
        let nop = instrs.remove(pc);
        debug_assert_eq!(std::mem::discriminant(&Instruction::Nop), std::mem::discriminant(&nop));
    }
    merge_fixups(fixups, extra_fixups, !keep_nop);

    match result {
        ExprType::Boolean => unreachable!("Filtered out above"),
        ExprType::Double => instrs.push(double_make_inst(span.pos)),
        ExprType::Integer => instrs.push(integer_make_inst(span.pos)),
        ExprType::Text => instrs.push(text_make_inst(span.pos)),
    };

    Ok(ExprType::Boolean)
}

/// Compiles a binary shift operator and appends its instructions to `instrs`.
fn compile_shift_binary_op<F: Fn(LineCol) -> Instruction>(
    instrs: &mut Vec<Instruction>,
    fixups: &mut HashMap<Address, Fixup>,
    symtable: &SymbolsTable,
    make_inst: F,
    span: BinaryOpSpan,
    op_name: &'static str,
) -> Result<ExprType> {
    let lhs_type = compile_expr(instrs, fixups, symtable, span.lhs, false)?;
    match lhs_type {
        ExprType::Integer => (),
        _ => {
            return Err(Error::UnaryOpTypeError(span.pos, op_name, lhs_type));
        }
    };

    let rhs_type = compile_expr(instrs, fixups, symtable, span.rhs, false)?;
    match rhs_type {
        ExprType::Integer => (),
        _ => {
            return Err(Error::TypeMismatch(span.pos, rhs_type, ExprType::Integer));
        }
    };

    instrs.push(make_inst(span.pos));

    Ok(ExprType::Integer)
}

/// Compiles the evaluation of an expression, appends its instructions to the
/// Compiles a binary operator and appends its instructions to `instrs`.
fn compile_arithmetic_binary_op<F1: Fn(LineCol) -> Instruction, F2: Fn(LineCol) -> Instruction>(
    instrs: &mut Vec<Instruction>,
    fixups: &mut HashMap<Address, Fixup>,
    symtable: &SymbolsTable,
    double_make_inst: F1,
    integer_make_inst: F2,
    span: BinaryOpSpan,
    op_name: &'static str,
) -> Result<ExprType> {
    let lhs_type = compile_expr(instrs, fixups, symtable, span.lhs, false)?;
    let pc = instrs.len();
    instrs.push(Instruction::Nop);

    let mut keep_nop = false;
    let mut extra_fixups = HashMap::default();
    let rhs_type = compile_expr(instrs, &mut extra_fixups, symtable, span.rhs, false)?;
    let result = match (lhs_type, rhs_type) {
        (ExprType::Double, ExprType::Double) => ExprType::Double,
        (ExprType::Integer, ExprType::Integer) => ExprType::Integer,
        (ExprType::Text, ExprType::Text) if op_name == "+" => ExprType::Text,

        (ExprType::Double, ExprType::Integer) => {
            instrs.push(Instruction::IntegerToDouble);
            ExprType::Double
        }

        (ExprType::Integer, ExprType::Double) => {
            instrs[pc] = Instruction::IntegerToDouble;
            keep_nop = true;
            ExprType::Double
        }

        (_, _) => {
            return Err(Error::BinaryOpTypeError(span.pos, op_name, lhs_type, rhs_type));
        }
    };

    if !keep_nop {
        let nop = instrs.remove(pc);
        debug_assert_eq!(std::mem::discriminant(&Instruction::Nop), std::mem::discriminant(&nop));
    }
    merge_fixups(fixups, extra_fixups, !keep_nop);

    match result {
        ExprType::Boolean => unreachable!("Filtered out above"),
        ExprType::Double => instrs.push(double_make_inst(span.pos)),
        ExprType::Integer => instrs.push(integer_make_inst(span.pos)),
        ExprType::Text => {
            debug_assert_eq!("+", op_name, "Filtered out above");
            instrs.push(Instruction::ConcatStrings(span.pos))
        }
    };

    Ok(result)
}

/// Compiles the load of a symbol in the context of an expression.
fn compile_expr_symbol(
    instrs: &mut Vec<Instruction>,
    fixups: &mut HashMap<Address, Fixup>,
    symtable: &SymbolsTable,
    span: SymbolSpan,
    allow_varrefs: bool,
) -> Result<ExprType> {
    let key = SymbolKey::from(span.vref.name());
    let (instr, vtype) = match symtable.get_with_index(&key) {
        None => return Err(Error::UndefinedSymbol(span.pos, key)),

        Some((SymbolPrototype::Array(atype, _dims), _index)) => {
            if allow_varrefs {
                (Instruction::LoadRef(LoadISpan { name: key, pos: span.pos }, *atype), *atype)
            } else {
                return Err(Error::NotAVariable(span.pos, span.vref));
            }
        }

        Some((SymbolPrototype::Variable(vtype), _index)) => {
            if allow_varrefs {
                (Instruction::LoadRef(LoadISpan { name: key, pos: span.pos }, *vtype), *vtype)
            } else {
                let instr = match vtype {
                    ExprType::Boolean => Instruction::LoadBoolean,
                    ExprType::Double => Instruction::LoadDouble,
                    ExprType::Integer => Instruction::LoadInteger,
                    ExprType::Text => Instruction::LoadString,
                };
                (instr(LoadISpan { name: key, pos: span.pos }), *vtype)
            }
        }

        Some((SymbolPrototype::BuiltinCallable(md), upcall_index)) => {
            let etype = match md.return_type() {
                Some(etype) => etype,
                None => {
                    return Err(Error::NotArrayOrFunction(span.pos, key));
                }
            };

            if !md.is_argless() {
                return Err(Error::CallableSyntaxError(span.pos, md.clone()));
            }

            let nargs = compile_function_args(md, instrs, fixups, symtable, span.pos, vec![])?;
            debug_assert_eq!(0, nargs, "Argless compiler must have returned zero arguments");
            (
                Instruction::FunctionCall(FunctionCallISpan {
                    name: key,
                    name_pos: span.pos,
                    upcall_index,
                    return_type: etype,
                    nargs: 0,
                }),
                etype,
            )
        }

        Some((SymbolPrototype::Callable(md), _index)) => {
            let etype = match md.return_type() {
                Some(etype) => etype,
                None => {
                    return Err(Error::NotArrayOrFunction(span.pos, key));
                }
            };

            if !md.is_argless() {
                return Err(Error::CallableSyntaxError(span.pos, md.clone()));
            }

            let nargs = compile_function_args(md, instrs, fixups, symtable, span.pos, vec![])?;
            debug_assert_eq!(0, nargs, "Argless compiler must have returned zero arguments");
            fixups.insert(instrs.len(), Fixup::Call(key, span.pos));
            (Instruction::Nop, etype)
        }
    };
    if !span.vref.accepts(vtype) {
        return Err(Error::IncompatibleTypeAnnotationInReference(span.pos, span.vref));
    }
    instrs.push(instr);
    Ok(vtype)
}

/// Compiles an array access.
fn compile_array_ref(
    instrs: &mut Vec<Instruction>,
    fixups: &mut HashMap<Address, Fixup>,
    symtable: &SymbolsTable,
    span: CallSpan,
    key: SymbolKey,
    vtype: ExprType,
    dimensions: usize,
) -> Result<ExprType> {
    let exprs = argspans_to_exprs(span.args);
    let nargs = exprs.len();
    compile_array_indices(instrs, fixups, symtable, dimensions, exprs, span.vref_pos)?;

    if !span.vref.accepts(vtype) {
        return Err(Error::IncompatibleTypeAnnotationInReference(span.vref_pos, span.vref));
    }
    instrs.push(Instruction::ArrayLoad(ArrayIndexISpan {
        name: key,
        name_pos: span.vref_pos,
        nargs,
    }));
    Ok(vtype)
}

/// Compiles the evaluation of an expression, appends its instructions to `instrs`, and returns
/// the type of the compiled expression.
///
/// `allow_varrefs` should be true for top-level expression compilations within function arguments.
/// In that specific case, we must leave bare variable and array references unevaluated because we
/// don't know if the function wants to take the reference or the value.
pub(super) fn compile_expr(
    instrs: &mut Vec<Instruction>,
    fixups: &mut HashMap<Address, Fixup>,
    symtable: &SymbolsTable,
    expr: Expr,
    allow_varrefs: bool,
) -> Result<ExprType> {
    match expr {
        Expr::Boolean(span) => {
            instrs.push(Instruction::PushBoolean(span.value, span.pos));
            Ok(ExprType::Boolean)
        }

        Expr::Double(span) => {
            instrs.push(Instruction::PushDouble(span.value, span.pos));
            Ok(ExprType::Double)
        }

        Expr::Integer(span) => {
            instrs.push(Instruction::PushInteger(span.value, span.pos));
            Ok(ExprType::Integer)
        }

        Expr::Text(span) => {
            instrs.push(Instruction::PushString(span.value, span.pos));
            Ok(ExprType::Text)
        }

        Expr::Symbol(span) => compile_expr_symbol(instrs, fixups, symtable, span, allow_varrefs),

        Expr::And(span) => compile_logical_binary_op(
            instrs,
            fixups,
            symtable,
            Instruction::LogicalAnd,
            Instruction::BitwiseAnd,
            *span,
            "AND",
        ),

        Expr::Or(span) => compile_logical_binary_op(
            instrs,
            fixups,
            symtable,
            Instruction::LogicalOr,
            Instruction::BitwiseOr,
            *span,
            "OR",
        ),

        Expr::Xor(span) => compile_logical_binary_op(
            instrs,
            fixups,
            symtable,
            Instruction::LogicalXor,
            Instruction::BitwiseXor,
            *span,
            "XOR",
        ),

        Expr::Not(span) => compile_not_op(instrs, fixups, symtable, *span),

        Expr::ShiftLeft(span) => {
            let result = compile_shift_binary_op(
                instrs,
                fixups,
                symtable,
                Instruction::ShiftLeft,
                *span,
                "<<",
            )?;
            debug_assert_eq!(ExprType::Integer, result);
            Ok(result)
        }

        Expr::ShiftRight(span) => {
            let result = compile_shift_binary_op(
                instrs,
                fixups,
                symtable,
                Instruction::ShiftRight,
                *span,
                ">>",
            )?;
            debug_assert_eq!(ExprType::Integer, result);
            Ok(result)
        }

        Expr::Equal(span) => {
            let result = compile_equality_binary_op(
                instrs,
                fixups,
                symtable,
                Instruction::EqualBooleans,
                Instruction::EqualDoubles,
                Instruction::EqualIntegers,
                Instruction::EqualStrings,
                *span,
                "=",
            )?;
            debug_assert_eq!(ExprType::Boolean, result);
            Ok(result)
        }

        Expr::NotEqual(span) => {
            let result = compile_equality_binary_op(
                instrs,
                fixups,
                symtable,
                Instruction::NotEqualBooleans,
                Instruction::NotEqualDoubles,
                Instruction::NotEqualIntegers,
                Instruction::NotEqualStrings,
                *span,
                "<>",
            )?;
            debug_assert_eq!(ExprType::Boolean, result);
            Ok(result)
        }

        Expr::Less(span) => {
            let result = compile_relational_binary_op(
                instrs,
                fixups,
                symtable,
                Instruction::LessDoubles,
                Instruction::LessIntegers,
                Instruction::LessStrings,
                *span,
                "<",
            )?;
            debug_assert_eq!(ExprType::Boolean, result);
            Ok(result)
        }

        Expr::LessEqual(span) => {
            let result = compile_relational_binary_op(
                instrs,
                fixups,
                symtable,
                Instruction::LessEqualDoubles,
                Instruction::LessEqualIntegers,
                Instruction::LessEqualStrings,
                *span,
                "<=",
            )?;
            debug_assert_eq!(ExprType::Boolean, result);
            Ok(result)
        }

        Expr::Greater(span) => {
            let result = compile_relational_binary_op(
                instrs,
                fixups,
                symtable,
                Instruction::GreaterDoubles,
                Instruction::GreaterIntegers,
                Instruction::GreaterStrings,
                *span,
                ">",
            )?;
            debug_assert_eq!(ExprType::Boolean, result);
            Ok(result)
        }

        Expr::GreaterEqual(span) => {
            let result = compile_relational_binary_op(
                instrs,
                fixups,
                symtable,
                Instruction::GreaterEqualDoubles,
                Instruction::GreaterEqualIntegers,
                Instruction::GreaterEqualStrings,
                *span,
                ">=",
            )?;
            debug_assert_eq!(ExprType::Boolean, result);
            Ok(result)
        }

        Expr::Add(span) => Ok(compile_arithmetic_binary_op(
            instrs,
            fixups,
            symtable,
            Instruction::AddDoubles,
            Instruction::AddIntegers,
            *span,
            "+",
        )?),

        Expr::Subtract(span) => Ok(compile_arithmetic_binary_op(
            instrs,
            fixups,
            symtable,
            Instruction::SubtractDoubles,
            Instruction::SubtractIntegers,
            *span,
            "-",
        )?),

        Expr::Multiply(span) => Ok(compile_arithmetic_binary_op(
            instrs,
            fixups,
            symtable,
            Instruction::MultiplyDoubles,
            Instruction::MultiplyIntegers,
            *span,
            "*",
        )?),

        Expr::Divide(span) => Ok(compile_arithmetic_binary_op(
            instrs,
            fixups,
            symtable,
            Instruction::DivideDoubles,
            Instruction::DivideIntegers,
            *span,
            "/",
        )?),

        Expr::Modulo(span) => Ok(compile_arithmetic_binary_op(
            instrs,
            fixups,
            symtable,
            Instruction::ModuloDoubles,
            Instruction::ModuloIntegers,
            *span,
            "MOD",
        )?),

        Expr::Power(span) => Ok(compile_arithmetic_binary_op(
            instrs,
            fixups,
            symtable,
            Instruction::PowerDoubles,
            Instruction::PowerIntegers,
            *span,
            "^",
        )?),

        Expr::Negate(span) => Ok(compile_neg_op(instrs, fixups, symtable, *span)?),

        Expr::Call(span) => {
            let key = SymbolKey::from(span.vref.name());
            match symtable.get_with_index(&key) {
                Some((SymbolPrototype::Array(vtype, dims), _index)) => {
                    compile_array_ref(instrs, fixups, symtable, span, key, *vtype, *dims)
                }

                Some((SymbolPrototype::BuiltinCallable(md), upcall_index)) => {
                    if !span.vref.accepts_callable(md.return_type()) {
                        return Err(Error::IncompatibleTypeAnnotationInReference(
                            span.vref_pos,
                            span.vref,
                        ));
                    }

                    let vtype = match md.return_type() {
                        Some(vtype) => vtype,
                        None => {
                            return Err(Error::NotArrayOrFunction(span.vref_pos, key));
                        }
                    };

                    let span_pos = span.vref_pos;
                    let nargs =
                        compile_function_args(md, instrs, fixups, symtable, span_pos, span.args)?;
                    if md.is_argless() && nargs == 0 {
                        return Err(Error::CallableSyntaxError(span.vref_pos, md.clone()));
                    }
                    instrs.push(Instruction::FunctionCall(FunctionCallISpan {
                        name: key,
                        name_pos: span_pos,
                        upcall_index,
                        return_type: vtype,
                        nargs,
                    }));
                    Ok(vtype)
                }

                Some((SymbolPrototype::Callable(md), _index)) => {
                    if !span.vref.accepts_callable(md.return_type()) {
                        return Err(Error::IncompatibleTypeAnnotationInReference(
                            span.vref_pos,
                            span.vref,
                        ));
                    }

                    let vtype = match md.return_type() {
                        Some(vtype) => vtype,
                        None => {
                            return Err(Error::NotArrayOrFunction(span.vref_pos, key));
                        }
                    };

                    let span_pos = span.vref_pos;
                    let nargs =
                        compile_function_args(md, instrs, fixups, symtable, span_pos, span.args)?;
                    if md.is_argless() && nargs == 0 {
                        return Err(Error::CallableSyntaxError(span.vref_pos, md.clone()));
                    }
                    instrs.push(Instruction::Nop);
                    fixups.insert(instrs.len() - 1, Fixup::Call(key, span_pos));
                    Ok(vtype)
                }

                Some((SymbolPrototype::Variable(_), _index)) => {
                    Err(Error::NotArrayOrFunction(span.vref_pos, key))
                }

                None => Err(Error::UndefinedSymbol(span.vref_pos, key)),
            }
        }
    }
}

/// Compiles a single expression, expecting it to be of a `target` type.  Applies casts if
/// possible.
pub(super) fn compile_expr_as_type(
    instrs: &mut Vec<Instruction>,
    fixups: &mut HashMap<Address, Fixup>,
    symtable: &SymbolsTable,
    expr: Expr,
    target: ExprType,
) -> Result<()> {
    let epos = expr.start_pos();
    let etype = compile_expr(instrs, fixups, symtable, expr, false)?;
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
            Err(Error::NotANumber(epos, etype))
        } else {
            Err(Error::TypeMismatch(epos, etype, target))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::{BuiltinCallISpan, FunctionCallISpan};
    use crate::compiler::{
        testutils::*, ArgSepSyntax, RepeatedSyntax, RepeatedTypeSyntax, RequiredRefSyntax,
        RequiredValueSyntax, SingularArgSyntax,
    };
    use crate::syms::CallableMetadataBuilder;
    use std::borrow::Cow;

    #[test]
    fn test_compile_expr_literals() {
        Tester::default()
            .parse("b = TRUE\nd = 2.3\ni = 5\nt = \"foo\"")
            .compile()
            .expect_instr(0, Instruction::PushBoolean(true, lc(1, 5)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("b")))
            .expect_instr(2, Instruction::PushDouble(2.3, lc(2, 5)))
            .expect_instr(3, Instruction::Assign(SymbolKey::from("d")))
            .expect_instr(4, Instruction::PushInteger(5, lc(3, 5)))
            .expect_instr(5, Instruction::Assign(SymbolKey::from("i")))
            .expect_instr(6, Instruction::PushString("foo".to_owned(), lc(4, 5)))
            .expect_instr(7, Instruction::Assign(SymbolKey::from("t")))
            .check();
    }

    #[test]
    fn test_compile_expr_varrefs_are_evaluated() {
        Tester::default()
            .define("j", SymbolPrototype::Variable(ExprType::Integer))
            .parse("i = j")
            .compile()
            .expect_instr(
                0,
                Instruction::LoadInteger(LoadISpan { name: SymbolKey::from("j"), pos: lc(1, 5) }),
            )
            .expect_instr(1, Instruction::Assign(SymbolKey::from("i")))
            .check();
    }

    #[test]
    fn test_compile_expr_argless_call_ok() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("F").with_return_type(ExprType::Integer))
            .parse("i = f")
            .compile()
            .expect_instr(
                0,
                Instruction::FunctionCall(FunctionCallISpan {
                    name: SymbolKey::from("f"),
                    name_pos: lc(1, 5),
                    upcall_index: 0,
                    return_type: ExprType::Integer,
                    nargs: 0,
                }),
            )
            .expect_instr(1, Instruction::Assign(SymbolKey::from("i")))
            .check();
    }

    #[test]
    fn test_compile_expr_argless_and_not_argless_ok() {
        Tester::default()
            .define_callable(
                CallableMetadataBuilder::new("F").with_return_type(ExprType::Integer).with_syntax(
                    &[
                        (&[], None),
                        (
                            &[SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax {
                                    name: Cow::Borrowed("i"),
                                    vtype: ExprType::Integer,
                                },
                                ArgSepSyntax::End,
                            )],
                            None,
                        ),
                    ],
                ),
            )
            .parse("i = f")
            .parse("j = f(3)")
            .compile()
            .expect_instr(
                0,
                Instruction::FunctionCall(FunctionCallISpan {
                    name: SymbolKey::from("f"),
                    name_pos: lc(1, 5),
                    upcall_index: 0,
                    return_type: ExprType::Integer,
                    nargs: 0,
                }),
            )
            .expect_instr(1, Instruction::Assign(SymbolKey::from("i")))
            .expect_instr(2, Instruction::PushInteger(3, lc(2, 7)))
            .expect_instr(
                3,
                Instruction::FunctionCall(FunctionCallISpan {
                    name: SymbolKey::from("f"),
                    name_pos: lc(2, 5),
                    upcall_index: 0,
                    return_type: ExprType::Integer,
                    nargs: 1,
                }),
            )
            .expect_instr(4, Instruction::Assign(SymbolKey::from("j")))
            .check();
    }

    #[test]
    fn test_compile_expr_argless_call_not_argless() {
        Tester::default()
            .define_callable(
                CallableMetadataBuilder::new("F").with_return_type(ExprType::Integer).with_syntax(
                    &[(
                        &[SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("i"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::End,
                        )],
                        None,
                    )],
                ),
            )
            .parse("i = f")
            .compile()
            .expect_err("1:5: F expected (i%)")
            .check();
    }

    #[test]
    fn test_compile_expr_ref_argless_not_allowed() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("C").with_syntax(&[(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax {
                        name: Cow::Borrowed("x"),
                        require_array: false,
                        define_undefined: false,
                    },
                    ArgSepSyntax::End,
                )],
                None,
            )]))
            .define_callable(CallableMetadataBuilder::new("F").with_return_type(ExprType::Integer))
            .parse("c f")
            .compile()
            .expect_err("1:3: F is not an array nor a function")
            .check();
    }

    #[test]
    fn test_compile_expr_bad_annotation_in_varref() {
        Tester::default()
            .parse("a = 3: b = a$ + 1")
            .compile()
            .expect_err("1:12: Incompatible type annotation in a$ reference")
            .check();
    }

    #[test]
    fn test_compile_expr_bad_annotation_in_argless_call() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("F").with_return_type(ExprType::Integer))
            .parse("a = f$ + 1")
            .compile()
            .expect_err("1:5: Incompatible type annotation in f$ reference")
            .check();
    }

    #[test]
    fn test_compile_expr_ref_bad_annotation_in_varref() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("C").with_syntax(&[(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax {
                        name: Cow::Borrowed("x"),
                        require_array: false,
                        define_undefined: false,
                    },
                    ArgSepSyntax::End,
                )],
                None,
            )]))
            .parse("a = 3: c a$")
            .compile()
            .expect_err("1:10: Incompatible type annotation in a$ reference")
            .check();
    }

    #[test]
    fn test_compile_expr_ref_bad_annotation_in_argless_call() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("C").with_syntax(&[(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax {
                        name: Cow::Borrowed("x"),
                        require_array: false,
                        define_undefined: false,
                    },
                    ArgSepSyntax::End,
                )],
                None,
            )]))
            .define_callable(CallableMetadataBuilder::new("F").with_return_type(ExprType::Integer))
            .parse("c f$")
            .compile()
            .expect_err("1:3: Incompatible type annotation in f$ reference")
            .check();
    }

    #[test]
    fn test_compile_expr_try_load_array_as_var() {
        Tester::default()
            .define(SymbolKey::from("a"), SymbolPrototype::Array(ExprType::Integer, 2))
            .parse("b = a")
            .compile()
            .expect_err("1:5: a is not a variable")
            .check();
    }

    #[test]
    fn test_compile_expr_ref_try_load_array_as_var() {
        Tester::default()
            .define(SymbolKey::from("a"), SymbolPrototype::Array(ExprType::Integer, 1))
            .define_callable(CallableMetadataBuilder::new("C").with_syntax(&[(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax {
                        name: Cow::Borrowed("x"),
                        require_array: true,
                        define_undefined: false,
                    },
                    ArgSepSyntax::End,
                )],
                None,
            )]))
            .parse("c a")
            .compile()
            .expect_instr(
                0,
                Instruction::LoadRef(
                    LoadISpan { name: SymbolKey::from("a"), pos: lc(1, 3) },
                    ExprType::Integer,
                ),
            )
            .expect_instr(
                1,
                Instruction::BuiltinCall(BuiltinCallISpan {
                    name: SymbolKey::from("C"),
                    name_pos: lc(1, 1),
                    upcall_index: 0,
                    nargs: 1,
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_expr_try_load_command_as_var() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("C"))
            .parse("b = c")
            .compile()
            .expect_err("1:5: C is not an array nor a function")
            .check();
    }

    #[test]
    fn test_compile_expr_ref_try_load_command_as_var() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("C").with_syntax(&[(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax {
                        name: Cow::Borrowed("x"),
                        require_array: false,
                        define_undefined: false,
                    },
                    ArgSepSyntax::End,
                )],
                None,
            )]))
            .parse("c c")
            .compile()
            .expect_err("1:3: C is not an array nor a function")
            .check();
    }

    #[test]
    fn test_compile_expr_logical_ops() {
        Tester::default()
            .define("x", SymbolPrototype::Variable(ExprType::Boolean))
            .define("y", SymbolPrototype::Variable(ExprType::Boolean))
            .define("z", SymbolPrototype::Variable(ExprType::Boolean))
            .parse("b = true OR x AND y XOR NOT z")
            .compile()
            .expect_instr(0, Instruction::PushBoolean(true, lc(1, 5)))
            .expect_instr(
                1,
                Instruction::LoadBoolean(LoadISpan { name: SymbolKey::from("x"), pos: lc(1, 13) }),
            )
            .expect_instr(2, Instruction::LogicalOr(lc(1, 10)))
            .expect_instr(
                3,
                Instruction::LoadBoolean(LoadISpan { name: SymbolKey::from("y"), pos: lc(1, 19) }),
            )
            .expect_instr(4, Instruction::LogicalAnd(lc(1, 15)))
            .expect_instr(
                5,
                Instruction::LoadBoolean(LoadISpan { name: SymbolKey::from("z"), pos: lc(1, 29) }),
            )
            .expect_instr(6, Instruction::LogicalNot(lc(1, 25)))
            .expect_instr(7, Instruction::LogicalXor(lc(1, 21)))
            .expect_instr(8, Instruction::Assign(SymbolKey::from("b")))
            .check();
    }

    #[test]
    fn test_compile_expr_bitwise_ops() {
        Tester::default()
            .define("a", SymbolPrototype::Variable(ExprType::Integer))
            .define("b", SymbolPrototype::Variable(ExprType::Integer))
            .parse("i = a >> 5 << b")
            .compile()
            .expect_instr(
                0,
                Instruction::LoadInteger(LoadISpan { name: SymbolKey::from("a"), pos: lc(1, 5) }),
            )
            .expect_instr(1, Instruction::PushInteger(5, lc(1, 10)))
            .expect_instr(2, Instruction::ShiftRight(lc(1, 7)))
            .expect_instr(
                3,
                Instruction::LoadInteger(LoadISpan { name: SymbolKey::from("b"), pos: lc(1, 15) }),
            )
            .expect_instr(4, Instruction::ShiftLeft(lc(1, 12)))
            .expect_instr(5, Instruction::Assign(SymbolKey::from("i")))
            .check();
    }

    /// Tests the behavior of one binary operator.
    ///
    /// `op_inst` is the instruction to expect for the operator and `op_name` is the literal name
    /// of the operator as it appears in EndBASIC code.
    ///
    /// `load_inst` and `push_inst` are generators to construct the necessary load and push
    /// operations for the given type.
    ///
    /// `test_value` is a value of the right type to use with the operator call, `test_value_str`
    /// is the same value as represented in EndBASIC code, and `test_value_type` is the
    /// corresponding type definition.
    fn do_op_test<
        L: Fn(LoadISpan) -> Instruction,
        M: Fn(LineCol) -> Instruction,
        P: Fn(V, LineCol) -> Instruction,
        V,
    >(
        load_inst: L,
        op_inst: M,
        op_name: &str,
        push_inst: P,
        test_value: V,
        test_value_str: &str,
        test_value_type: ExprType,
    ) {
        Tester::default()
            .define("a", SymbolPrototype::Variable(test_value_type))
            .parse(&format!("b = a {} {}", op_name, test_value_str))
            .compile()
            .expect_instr(0, load_inst(LoadISpan { name: SymbolKey::from("a"), pos: lc(1, 5) }))
            .expect_instr(1, push_inst(test_value, lc(1, 8 + op_name.len())))
            .expect_instr(2, op_inst(lc(1, 7)))
            .expect_instr(3, Instruction::Assign(SymbolKey::from("b")))
            .check();
    }

    #[test]
    fn test_compile_expr_equality_ops() {
        use ExprType::*;
        use Instruction::*;

        do_op_test(LoadBoolean, EqualBooleans, "=", PushBoolean, true, "TRUE", Boolean);
        do_op_test(LoadBoolean, NotEqualBooleans, "<>", PushBoolean, true, "TRUE", Boolean);

        do_op_test(LoadDouble, EqualDoubles, "=", PushDouble, 10.2, "10.2", Double);
        do_op_test(LoadDouble, NotEqualDoubles, "<>", PushDouble, 10.2, "10.2", Double);

        do_op_test(LoadInteger, EqualIntegers, "=", PushInteger, 10, "10", Integer);
        do_op_test(LoadInteger, NotEqualIntegers, "<>", PushInteger, 10, "10", Integer);

        do_op_test(LoadString, EqualStrings, "=", PushString, "foo".to_owned(), "\"foo\"", Text);
        do_op_test(
            LoadString,
            NotEqualStrings,
            "<>",
            PushString,
            "foo".to_owned(),
            "\"foo\"",
            Text,
        );
    }

    #[test]
    fn test_compile_expr_relational_ops() {
        use ExprType::*;
        use Instruction::*;

        do_op_test(LoadDouble, LessDoubles, "<", PushDouble, 10.2, "10.2", Double);
        do_op_test(LoadDouble, LessEqualDoubles, "<=", PushDouble, 10.2, "10.2", Double);
        do_op_test(LoadDouble, GreaterDoubles, ">", PushDouble, 10.2, "10.2", Double);
        do_op_test(LoadDouble, GreaterEqualDoubles, ">=", PushDouble, 10.2, "10.2", Double);

        do_op_test(LoadInteger, LessIntegers, "<", PushInteger, 10, "10", Integer);
        do_op_test(LoadInteger, LessEqualIntegers, "<=", PushInteger, 10, "10", Integer);
        do_op_test(LoadInteger, GreaterIntegers, ">", PushInteger, 10, "10", Integer);
        do_op_test(LoadInteger, GreaterEqualIntegers, ">=", PushInteger, 10, "10", Integer);

        do_op_test(LoadString, LessStrings, "<", PushString, "foo".to_owned(), "\"foo\"", Text);
        do_op_test(
            LoadString,
            LessEqualStrings,
            "<=",
            PushString,
            "foo".to_owned(),
            "\"foo\"",
            Text,
        );
        do_op_test(LoadString, GreaterStrings, ">", PushString, "foo".to_owned(), "\"foo\"", Text);
        do_op_test(
            LoadString,
            GreaterEqualStrings,
            ">=",
            PushString,
            "foo".to_owned(),
            "\"foo\"",
            Text,
        );
    }

    #[test]
    fn test_compile_expr_arithmetic_ops() {
        use ExprType::*;
        use Instruction::*;

        do_op_test(LoadDouble, AddDoubles, "+", PushDouble, 10.2, "10.2", Double);
        do_op_test(LoadDouble, SubtractDoubles, "-", PushDouble, 10.2, "10.2", Double);
        do_op_test(LoadDouble, MultiplyDoubles, "*", PushDouble, 10.2, "10.2", Double);
        do_op_test(LoadDouble, DivideDoubles, "/", PushDouble, 10.2, "10.2", Double);
        do_op_test(LoadDouble, ModuloDoubles, "MOD", PushDouble, 10.2, "10.2", Double);
        do_op_test(LoadDouble, PowerDoubles, "^", PushDouble, 10.2, "10.2", Double);
        Tester::default()
            .define("a", SymbolPrototype::Variable(Integer))
            .parse("i = -60.2")
            .compile()
            .expect_instr(0, PushDouble(60.2, lc(1, 6)))
            .expect_instr(1, NegateDouble(lc(1, 5)))
            .expect_instr(2, Assign(SymbolKey::from("i")))
            .check();

        do_op_test(LoadInteger, AddIntegers, "+", PushInteger, 10, "10", Integer);
        do_op_test(LoadInteger, SubtractIntegers, "-", PushInteger, 10, "10", Integer);
        do_op_test(LoadInteger, MultiplyIntegers, "*", PushInteger, 10, "10", Integer);
        do_op_test(LoadInteger, DivideIntegers, "/", PushInteger, 10, "10", Integer);
        do_op_test(LoadInteger, ModuloIntegers, "MOD", PushInteger, 10, "10", Integer);
        do_op_test(LoadInteger, PowerIntegers, "^", PushInteger, 10, "10", Integer);
        Tester::default()
            .define("a", SymbolPrototype::Variable(Integer))
            .parse("i = -60")
            .compile()
            .expect_instr(0, PushInteger(60, lc(1, 6)))
            .expect_instr(1, NegateInteger(lc(1, 5)))
            .expect_instr(2, Assign(SymbolKey::from("i")))
            .check();

        do_op_test(LoadString, ConcatStrings, "+", PushString, "foo".to_owned(), "\"foo\"", Text);
    }

    #[test]
    fn test_compile_expr_array_ref_exprs() {
        Tester::default()
            .define("FOO", SymbolPrototype::Array(ExprType::Integer, 3))
            .define("j", SymbolPrototype::Variable(ExprType::Integer))
            .define("k", SymbolPrototype::Variable(ExprType::Integer))
            .parse("i = FOO(3, j, k + 1)")
            .compile()
            .expect_instr(
                0,
                Instruction::LoadInteger(LoadISpan { name: SymbolKey::from("k"), pos: lc(1, 15) }),
            )
            .expect_instr(1, Instruction::PushInteger(1, lc(1, 19)))
            .expect_instr(2, Instruction::AddIntegers(lc(1, 17)))
            .expect_instr(
                3,
                Instruction::LoadInteger(LoadISpan { name: SymbolKey::from("j"), pos: lc(1, 12) }),
            )
            .expect_instr(4, Instruction::PushInteger(3, lc(1, 9)))
            .expect_instr(
                5,
                Instruction::ArrayLoad(ArrayIndexISpan {
                    name: SymbolKey::from("foo"),
                    name_pos: lc(1, 5),
                    nargs: 3,
                }),
            )
            .expect_instr(6, Instruction::Assign(SymbolKey::from("i")))
            .check();
    }

    #[test]
    fn test_compile_expr_array_ref_ok_annotation() {
        Tester::default()
            .define("FOO", SymbolPrototype::Array(ExprType::Integer, 1))
            .parse("i = FOO%(3)")
            .compile()
            .expect_instr(0, Instruction::PushInteger(3, lc(1, 10)))
            .expect_instr(
                1,
                Instruction::ArrayLoad(ArrayIndexISpan {
                    name: SymbolKey::from("foo"),
                    name_pos: lc(1, 5),
                    nargs: 1,
                }),
            )
            .expect_instr(2, Instruction::Assign(SymbolKey::from("i")))
            .check();
    }

    #[test]
    fn test_compile_expr_array_ref_bad_annotation() {
        Tester::default()
            .define("FOO", SymbolPrototype::Array(ExprType::Integer, 1))
            .parse("i = FOO#(3)")
            .compile()
            .expect_err("1:5: Incompatible type annotation in FOO# reference")
            .check();
    }

    #[test]
    fn test_compile_expr_array_ref_index_double() {
        Tester::default()
            .define("FOO", SymbolPrototype::Array(ExprType::Integer, 1))
            .parse("i = FOO(3.8)")
            .compile()
            .expect_instr(0, Instruction::PushDouble(3.8, lc(1, 9)))
            .expect_instr(1, Instruction::DoubleToInteger)
            .expect_instr(
                2,
                Instruction::ArrayLoad(ArrayIndexISpan {
                    name: SymbolKey::from("foo"),
                    name_pos: lc(1, 5),
                    nargs: 1,
                }),
            )
            .expect_instr(3, Instruction::Assign(SymbolKey::from("i")))
            .check();
    }

    #[test]
    fn test_compile_expr_array_ref_index_bad_type() {
        Tester::default()
            .define("FOO", SymbolPrototype::Array(ExprType::Integer, 1))
            .parse("i = FOO(FALSE)")
            .compile()
            .expect_err("1:9: BOOLEAN is not a number")
            .check();
    }

    #[test]
    fn test_compile_expr_array_ref_bad_dimensions() {
        Tester::default()
            .define("FOO", SymbolPrototype::Array(ExprType::Integer, 3))
            .parse("i = FOO#(3, 4)")
            .compile()
            .expect_err("1:5: Cannot index array with 2 subscripts; need 3")
            .check();
    }

    #[test]
    fn test_compile_expr_array_ref_not_defined() {
        Tester::default().parse("i = a(4)").compile().expect_err("1:5: Undefined symbol A").check();
    }

    #[test]
    fn test_compile_expr_array_ref_not_an_array() {
        Tester::default()
            .define("a", SymbolPrototype::Variable(ExprType::Integer))
            .parse("i = a(3)")
            .compile()
            .expect_err("1:5: A is not an array nor a function")
            .check();
    }

    #[test]
    fn test_compile_expr_function_call() {
        Tester::default()
            .define_callable(
                CallableMetadataBuilder::new("FOO")
                    .with_return_type(ExprType::Integer)
                    .with_syntax(&[(
                        &[],
                        Some(&RepeatedSyntax {
                            name: Cow::Borrowed("expr"),
                            type_syn: RepeatedTypeSyntax::TypedValue(ExprType::Integer),
                            sep: ArgSepSyntax::Exactly(ArgSep::Long),
                            require_one: true,
                            allow_missing: false,
                        }),
                    )]),
            )
            .define("j", SymbolPrototype::Variable(ExprType::Integer))
            .define("k", SymbolPrototype::Variable(ExprType::Double))
            .parse("i = FOO(3, j, k + 1)")
            .compile()
            .expect_instr(
                0,
                Instruction::LoadDouble(LoadISpan { name: SymbolKey::from("k"), pos: lc(1, 15) }),
            )
            .expect_instr(1, Instruction::PushInteger(1, lc(1, 19)))
            .expect_instr(2, Instruction::IntegerToDouble)
            .expect_instr(3, Instruction::AddDoubles(lc(1, 17)))
            .expect_instr(4, Instruction::DoubleToInteger)
            .expect_instr(
                5,
                Instruction::LoadInteger(LoadISpan { name: SymbolKey::from("j"), pos: lc(1, 12) }),
            )
            .expect_instr(6, Instruction::PushInteger(3, lc(1, 9)))
            .expect_instr(
                7,
                Instruction::FunctionCall(FunctionCallISpan {
                    name: SymbolKey::from("FOO"),
                    name_pos: lc(1, 5),
                    upcall_index: 0,
                    return_type: ExprType::Integer,
                    nargs: 3,
                }),
            )
            .expect_instr(8, Instruction::Assign(SymbolKey::from("i")))
            .check();
    }

    #[test]
    fn test_compile_expr_array_or_function_not_defined() {
        Tester::default()
            .define("j", SymbolPrototype::Variable(ExprType::Integer))
            .define("k", SymbolPrototype::Variable(ExprType::Integer))
            .parse("i = FOO(3, j, k + 1)")
            .compile()
            .expect_err("1:5: Undefined symbol FOO")
            .check();
    }

    #[test]
    fn test_compile_expr_array_or_function_references_variable() {
        Tester::default()
            .parse("i = 3: j = i()")
            .compile()
            .expect_err("1:12: I is not an array nor a function")
            .check();
    }
}
