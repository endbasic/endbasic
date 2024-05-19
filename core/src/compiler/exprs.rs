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

use super::{Error, ExprType, Result, SymbolPrototype, SymbolsTable};
use crate::ast::*;
use crate::bytecode::*;
use crate::reader::LineCol;
use crate::syms::SymbolKey;

/// Compiles the indices used to address an array.
pub(crate) fn compile_array_indices(
    instrs: &mut Vec<Instruction>,
    symtable: &SymbolsTable,
    exp_nargs: usize,
    args: Vec<Expr>,
    name_pos: LineCol,
) -> Result<()> {
    if exp_nargs != args.len() {
        return Err(Error::new(
            name_pos,
            format!("Cannot index array with {} subscripts; need {}", args.len(), exp_nargs),
        ));
    }

    for arg in args.into_iter().rev() {
        let arg_pos = arg.start_pos();
        match compile_expr(instrs, symtable, arg, false)? {
            ExprType::Integer => (),
            ExprType::Double => {
                instrs.push(Instruction::DoubleToInteger);
            }
            itype => {
                return Err(Error::new(
                    arg_pos,
                    format!("Array index must be INTEGER, not {}", itype),
                ));
            }
        }
    }

    Ok(())
}

/// Compiles a logical or bitwise unary operator and appends its instructions to `instrs`.
fn compile_not_op(
    instrs: &mut Vec<Instruction>,
    symtable: &SymbolsTable,
    span: UnaryOpSpan,
) -> Result<ExprType> {
    let expr_type = compile_expr(instrs, symtable, span.expr, false)?;
    match expr_type {
        ExprType::Boolean => {
            instrs.push(Instruction::LogicalNot(span.pos));
            Ok(ExprType::Boolean)
        }
        ExprType::Integer => {
            instrs.push(Instruction::BitwiseNot(span.pos));
            Ok(ExprType::Integer)
        }
        _ => Err(Error::new(span.pos, format!("Cannot apply NOT to {}", expr_type))),
    }
}

/// Compiles a negate operator and appends its instructions to `instrs`.
fn compile_neg_op(
    instrs: &mut Vec<Instruction>,
    symtable: &SymbolsTable,
    span: UnaryOpSpan,
) -> Result<ExprType> {
    let expr_type = compile_expr(instrs, symtable, span.expr, false)?;
    match expr_type {
        ExprType::Double => {
            instrs.push(Instruction::NegateDouble(span.pos));
            Ok(ExprType::Double)
        }
        ExprType::Integer => {
            instrs.push(Instruction::NegateInteger(span.pos));
            Ok(ExprType::Integer)
        }
        _ => Err(Error::new(span.pos, format!("Cannot negate {}", expr_type))),
    }
}

/// Compiles a logical binary operator and appends its instructions to `instrs`.
fn compile_logical_binary_op<F1: Fn(LineCol) -> Instruction, F2: Fn(LineCol) -> Instruction>(
    instrs: &mut Vec<Instruction>,
    symtable: &SymbolsTable,
    logical_make_inst: F1,
    bitwise_make_inst: F2,
    span: BinaryOpSpan,
    op_name: &str,
) -> Result<ExprType> {
    let lhs_type = compile_expr(instrs, symtable, span.lhs, false)?;
    let rhs_type = compile_expr(instrs, symtable, span.rhs, false)?;
    match (lhs_type, rhs_type) {
        (ExprType::Boolean, ExprType::Boolean) => {
            instrs.push(logical_make_inst(span.pos));
            Ok(ExprType::Boolean)
        }
        (ExprType::Integer, ExprType::Integer) => {
            instrs.push(bitwise_make_inst(span.pos));
            Ok(ExprType::Integer)
        }
        (_, _) => {
            Err(Error::new(span.pos, format!("Cannot {} {} and {}", op_name, lhs_type, rhs_type)))
        }
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
    symtable: &SymbolsTable,
    boolean_make_inst: F1,
    double_make_inst: F2,
    integer_make_inst: F3,
    text_make_inst: F4,
    span: BinaryOpSpan,
    op_name: &str,
) -> Result<ExprType> {
    let lhs_type = compile_expr(instrs, symtable, span.lhs, false)?;
    let pc = instrs.len();
    instrs.push(Instruction::Nop);

    let mut keep_nop = false;
    let rhs_type = compile_expr(instrs, symtable, span.rhs, false)?;
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
            return Err(Error::new(
                span.pos,
                format!("Cannot compare {} and {} with {}", lhs_type, rhs_type, op_name),
            ));
        }
    };

    if !keep_nop {
        let nop = instrs.remove(pc);
        debug_assert_eq!(std::mem::discriminant(&Instruction::Nop), std::mem::discriminant(&nop));
    }

    match result {
        ExprType::Boolean => instrs.push(boolean_make_inst(span.pos)),
        ExprType::Double => instrs.push(double_make_inst(span.pos)),
        ExprType::Integer => instrs.push(integer_make_inst(span.pos)),
        ExprType::Text => instrs.push(text_make_inst(span.pos)),
    };

    Ok(ExprType::Boolean)
}

/// Compiles a relational binary operator and appends its instructions to `instrs`.
fn compile_relational_binary_op<
    F1: Fn(LineCol) -> Instruction,
    F2: Fn(LineCol) -> Instruction,
    F3: Fn(LineCol) -> Instruction,
>(
    instrs: &mut Vec<Instruction>,
    symtable: &SymbolsTable,
    double_make_inst: F1,
    integer_make_inst: F2,
    text_make_inst: F3,
    span: BinaryOpSpan,
    op_name: &str,
) -> Result<ExprType> {
    let lhs_type = compile_expr(instrs, symtable, span.lhs, false)?;
    let pc = instrs.len();
    instrs.push(Instruction::Nop);

    let mut keep_nop = false;
    let rhs_type = compile_expr(instrs, symtable, span.rhs, false)?;
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
            return Err(Error::new(
                span.pos,
                format!("Cannot compare {} and {} with {}", lhs_type, rhs_type, op_name),
            ));
        }
    };

    if !keep_nop {
        let nop = instrs.remove(pc);
        debug_assert_eq!(std::mem::discriminant(&Instruction::Nop), std::mem::discriminant(&nop));
    }

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
    symtable: &SymbolsTable,
    make_inst: F,
    span: BinaryOpSpan,
    op_name: &str,
) -> Result<ExprType> {
    let lhs_type = compile_expr(instrs, symtable, span.lhs, false)?;
    match lhs_type {
        ExprType::Integer => (),
        _ => {
            return Err(Error::new(span.pos, format!("Cannot apply {} to {}", op_name, lhs_type)));
        }
    };

    let rhs_type = compile_expr(instrs, symtable, span.rhs, false)?;
    match rhs_type {
        ExprType::Integer => (),
        _ => {
            return Err(Error::new(
                span.pos,
                format!(
                    "Number of bits to {} must be an {}, not a {}",
                    op_name,
                    ExprType::Integer,
                    rhs_type
                ),
            ));
        }
    };

    instrs.push(make_inst(span.pos));

    Ok(ExprType::Integer)
}

/// Compiles the evaluation of an expression, appends its instructions to the
/// Compiles a binary operator and appends its instructions to `instrs`.
fn compile_arithmetic_binary_op<F1: Fn(LineCol) -> Instruction, F2: Fn(LineCol) -> Instruction>(
    instrs: &mut Vec<Instruction>,
    symtable: &SymbolsTable,
    double_make_inst: F1,
    integer_make_inst: F2,
    span: BinaryOpSpan,
    op_name: &str,
) -> Result<ExprType> {
    let lhs_type = compile_expr(instrs, symtable, span.lhs, false)?;
    let pc = instrs.len();
    instrs.push(Instruction::Nop);

    let mut keep_nop = false;
    let rhs_type = compile_expr(instrs, symtable, span.rhs, false)?;
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
            return Err(Error::new(
                span.pos,
                format!("Cannot {} {} and {}", op_name, lhs_type, rhs_type),
            ));
        }
    };

    if !keep_nop {
        let nop = instrs.remove(pc);
        debug_assert_eq!(std::mem::discriminant(&Instruction::Nop), std::mem::discriminant(&nop));
    }

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
    symtable: &SymbolsTable,
    span: SymbolSpan,
    allow_varrefs: bool,
) -> Result<ExprType> {
    let key = SymbolKey::from(span.vref.name());
    let (instr, vtype) = match symtable.get(&key) {
        None => {
            return Err(Error::new(span.pos, format!("Undefined variable {}", span.vref.name())))
        }

        Some(SymbolPrototype::Array(atype, _dims)) => {
            if allow_varrefs {
                (Instruction::LoadRef(span.vref.clone(), span.pos), atype)
            } else {
                return Err(Error::new(
                    span.pos,
                    format!("{} is not a variable", span.vref.name()),
                ));
            }
        }

        Some(SymbolPrototype::Variable(vtype)) => {
            if allow_varrefs {
                (Instruction::LoadRef(span.vref.clone(), span.pos), vtype)
            } else {
                (Instruction::Load(key, span.pos), vtype)
            }
        }

        Some(SymbolPrototype::Callable(ctype, is_argless)) => {
            if !is_argless {
                return Err(Error::new(
                    span.pos,
                    format!("In call to {}: function requires arguments", span.vref.name()),
                ));
            }

            match ctype.as_expr_type() {
                Some(etype) => (Instruction::FunctionCall(key, ctype.into(), span.pos, 0), etype),
                None => {
                    return Err(Error::new(
                        span.pos,
                        format!("{} is not an array nor a function", span.vref.name()),
                    ));
                }
            }
        }
    };
    if !span.vref.accepts(vtype.into()) {
        return Err(Error::new(
            span.pos,
            format!("Incompatible type annotation in {} reference", span.vref),
        ));
    }
    instrs.push(instr);
    Ok(vtype)
}

/// Compiles the load of a symbol in the context of a command argument.
fn compile_expr_symbol_ref(
    instrs: &mut Vec<Instruction>,
    symtable: &mut SymbolsTable,
    span: SymbolSpan,
) -> Result<ExprType> {
    let key = SymbolKey::from(span.vref.name());
    let result = match symtable.get(&key) {
        None => {
            let vtype = if span.vref.ref_type() == VarType::Auto {
                ExprType::Integer
            } else {
                span.vref.ref_type().into()
            };

            if !span.vref.accepts(vtype.into()) {
                return Err(Error::new(
                    span.pos,
                    format!("Incompatible type annotation in {} reference", span.vref),
                ));
            }

            symtable.insert(key, SymbolPrototype::Variable(vtype));
            vtype
        }

        Some(SymbolPrototype::Array(vtype, _)) | Some(SymbolPrototype::Variable(vtype)) => {
            if !span.vref.accepts(vtype.into()) {
                return Err(Error::new(
                    span.pos,
                    format!("Incompatible type annotation in {} reference", span.vref),
                ));
            }

            vtype
        }

        Some(SymbolPrototype::Callable(ctype, is_argless)) => match ctype.as_expr_type() {
            Some(etype) => {
                if !span.vref.accepts(etype.into()) {
                    return Err(Error::new(
                        span.pos,
                        format!("Incompatible type annotation in {} reference", span.vref),
                    ));
                }

                if !is_argless {
                    return Err(Error::new(
                        span.pos,
                        format!("In call to {}: function requires arguments", span.vref.name()),
                    ));
                }

                // TODO(jmmv): This is wrong.  We should not be trying to load a reference to a
                // callable.

                etype
            }
            None => {
                return Err(Error::new(
                    span.pos,
                    format!("{} is not an array nor a function", span.vref.name()),
                ));
            }
        },
    };
    instrs.push(Instruction::LoadRef(span.vref, span.pos));
    Ok(result)
}

/// Compiles an array access.
fn compile_array_ref(
    instrs: &mut Vec<Instruction>,
    symtable: &SymbolsTable,
    span: FunctionCallSpan,
    key: SymbolKey,
    vtype: ExprType,
    dimensions: usize,
) -> Result<ExprType> {
    let nargs = span.args.len();
    compile_array_indices(instrs, symtable, dimensions, span.args, span.pos)?;

    if !span.fref.accepts(vtype.into()) {
        return Err(Error::new(
            span.pos,
            format!("Incompatible type annotation in {} reference", span.fref),
        ));
    }
    instrs.push(Instruction::ArrayLoad(key, span.pos, nargs));
    Ok(vtype)
}

/// Compiles the evaluation of an expression, appends its instructions to `instrs`, and returns
/// the type of the compiled expression.
///
/// `allow_varrefs` should be true for top-level expression compilations within function arguments.
/// In that specific case, we must leave bare variable and array references unevaluated because we
/// don't know if the function wants to take the reference or the value.
pub(crate) fn compile_expr(
    instrs: &mut Vec<Instruction>,
    symtable: &SymbolsTable,
    expr: Expr,
    allow_varrefs: bool,
) -> Result<ExprType> {
    match expr {
        Expr::Boolean(span) => {
            instrs.push(Instruction::Push(Value::Boolean(span.value), span.pos));
            Ok(ExprType::Boolean)
        }

        Expr::Double(span) => {
            instrs.push(Instruction::Push(Value::Double(span.value), span.pos));
            Ok(ExprType::Double)
        }

        Expr::Integer(span) => {
            instrs.push(Instruction::Push(Value::Integer(span.value), span.pos));
            Ok(ExprType::Integer)
        }

        Expr::Text(span) => {
            instrs.push(Instruction::Push(Value::Text(span.value), span.pos));
            Ok(ExprType::Text)
        }

        Expr::Symbol(span) => compile_expr_symbol(instrs, symtable, span, allow_varrefs),

        Expr::And(span) => compile_logical_binary_op(
            instrs,
            symtable,
            Instruction::LogicalAnd,
            Instruction::BitwiseAnd,
            *span,
            "AND",
        ),

        Expr::Or(span) => compile_logical_binary_op(
            instrs,
            symtable,
            Instruction::LogicalOr,
            Instruction::BitwiseOr,
            *span,
            "OR",
        ),

        Expr::Xor(span) => compile_logical_binary_op(
            instrs,
            symtable,
            Instruction::LogicalXor,
            Instruction::BitwiseXor,
            *span,
            "XOR",
        ),

        Expr::Not(span) => compile_not_op(instrs, symtable, *span),

        Expr::ShiftLeft(span) => {
            let result =
                compile_shift_binary_op(instrs, symtable, Instruction::ShiftLeft, *span, "<<")?;
            debug_assert_eq!(ExprType::Integer, result);
            Ok(result)
        }

        Expr::ShiftRight(span) => {
            let result =
                compile_shift_binary_op(instrs, symtable, Instruction::ShiftRight, *span, ">>")?;
            debug_assert_eq!(ExprType::Integer, result);
            Ok(result)
        }

        Expr::Equal(span) => {
            let result = compile_equality_binary_op(
                instrs,
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
            symtable,
            Instruction::AddDoubles,
            Instruction::AddIntegers,
            *span,
            "+",
        )?),

        Expr::Subtract(span) => Ok(compile_arithmetic_binary_op(
            instrs,
            symtable,
            Instruction::SubtractDoubles,
            Instruction::SubtractIntegers,
            *span,
            "-",
        )?),

        Expr::Multiply(span) => Ok(compile_arithmetic_binary_op(
            instrs,
            symtable,
            Instruction::MultiplyDoubles,
            Instruction::MultiplyIntegers,
            *span,
            "*",
        )?),

        Expr::Divide(span) => Ok(compile_arithmetic_binary_op(
            instrs,
            symtable,
            Instruction::DivideDoubles,
            Instruction::DivideIntegers,
            *span,
            "/",
        )?),

        Expr::Modulo(span) => Ok(compile_arithmetic_binary_op(
            instrs,
            symtable,
            Instruction::ModuloDoubles,
            Instruction::ModuloIntegers,
            *span,
            "MOD",
        )?),

        Expr::Power(span) => Ok(compile_arithmetic_binary_op(
            instrs,
            symtable,
            Instruction::PowerDoubles,
            Instruction::PowerIntegers,
            *span,
            "^",
        )?),

        Expr::Negate(span) => Ok(compile_neg_op(instrs, symtable, *span)?),

        Expr::Call(span) => {
            let key = SymbolKey::from(span.fref.name());
            match symtable.get(&key) {
                Some(SymbolPrototype::Array(vtype, dims)) => {
                    compile_array_ref(instrs, symtable, span, key, vtype, dims)
                }

                Some(SymbolPrototype::Callable(ctype, is_argless)) => {
                    let nargs = span.args.len();
                    for arg in span.args.into_iter().rev() {
                        compile_expr(instrs, symtable, arg, true)?;
                    }

                    if !span.fref.accepts((ctype).into()) {
                        return Err(Error::new(
                            span.pos,
                            format!("Incompatible type annotation in {} reference", span.fref),
                        ));
                    }

                    let vtype = match ctype.as_expr_type() {
                        Some(vtype) => vtype,
                        None => {
                            return Err(Error::new(
                                span.pos,
                                format!("{} is not an array nor a function", span.fref.name()),
                            ));
                        }
                    };

                    if is_argless {
                        return Err(Error::new(
                            span.pos,
                            format!(
                                "In call to {}: expected no arguments nor parenthesis",
                                span.fref.name()
                            ),
                        ));
                    }

                    instrs.push(Instruction::FunctionCall(key, ctype.into(), span.pos, nargs));
                    Ok(vtype)
                }

                Some(SymbolPrototype::Variable(_)) => Err(Error::new(
                    span.pos,
                    format!("{} is not an array nor a function", span.fref.name()),
                )),

                None => Err(Error::new(
                    span.pos,
                    format!("Unknown function or array {}", span.fref.name()),
                )),
            }
        }
    }
}

/// Compiles the evaluation of an expression, appends its instructions to `instrs`, and returns
/// the type of the compiled expression.
///
/// This function should be used only when compiling the arguments to a builtin command, because
/// in that context, we need mutable access to the `symtable`in order to define output variables
/// (if any).
pub(crate) fn compile_expr_in_command(
    instrs: &mut Vec<Instruction>,
    symtable: &mut SymbolsTable,
    expr: Expr,
) -> Result<ExprType> {
    match expr {
        Expr::Symbol(span) => compile_expr_symbol_ref(instrs, symtable, span),
        expr => compile_expr(instrs, symtable, expr, false),
    }
}
