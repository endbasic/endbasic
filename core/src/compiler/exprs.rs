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
use crate::compiler::compile_function_args;
use crate::parser::argspans_to_exprs;
use crate::reader::LineCol;
use crate::syms::SymbolKey;

/// Compiles the indices used to address an array.
pub(super) fn compile_array_indices(
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
                (Instruction::LoadRef(key, *atype, span.pos), *atype)
            } else {
                return Err(Error::new(
                    span.pos,
                    format!("{} is not a variable", span.vref.name()),
                ));
            }
        }

        Some(SymbolPrototype::Variable(vtype)) => {
            if allow_varrefs {
                (Instruction::LoadRef(key, *vtype, span.pos), *vtype)
            } else {
                let instr = match vtype {
                    ExprType::Boolean => Instruction::LoadBoolean,
                    ExprType::Double => Instruction::LoadDouble,
                    ExprType::Integer => Instruction::LoadInteger,
                    ExprType::Text => Instruction::LoadString,
                };
                (instr(key, span.pos), *vtype)
            }
        }

        Some(SymbolPrototype::Callable(md)) => {
            let etype = match md.return_type() {
                Some(etype) => etype,
                None => {
                    return Err(Error::new(
                        span.pos,
                        format!("{} is not an array nor a function", span.vref.name()),
                    ));
                }
            };

            if !md.is_argless() {
                return Err(Error::new(
                    span.pos,
                    format!("In call to {}: function requires arguments", span.vref.name()),
                ));
            }

            let nargs = compile_function_args(md.syntaxes(), instrs, symtable, span.pos, vec![])
                .map_err(|e| Error::from_call_error(md, e, span.pos))?;
            debug_assert_eq!(0, nargs, "Argless compiler must have returned zero arguments");
            (Instruction::FunctionCall(key, etype, span.pos, 0), etype)
        }
    };
    if !span.vref.accepts(vtype) {
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
    match symtable.get(&key) {
        None => {
            let vtype = span.vref.ref_type().unwrap_or(ExprType::Integer);

            if !span.vref.accepts(vtype) {
                return Err(Error::new(
                    span.pos,
                    format!("Incompatible type annotation in {} reference", span.vref),
                ));
            }

            symtable.insert(key.clone(), SymbolPrototype::Variable(vtype));
            instrs.push(Instruction::LoadRef(key, vtype, span.pos));
            Ok(vtype)
        }

        Some(SymbolPrototype::Array(vtype, _)) | Some(SymbolPrototype::Variable(vtype)) => {
            let vtype = *vtype;

            if !span.vref.accepts(vtype) {
                return Err(Error::new(
                    span.pos,
                    format!("Incompatible type annotation in {} reference", span.vref),
                ));
            }

            instrs.push(Instruction::LoadRef(key, vtype, span.pos));
            Ok(vtype)
        }

        Some(SymbolPrototype::Callable(md)) => {
            if !span.vref.accepts_callable(md.return_type()) {
                return Err(Error::new(
                    span.pos,
                    format!("Incompatible type annotation in {} reference", span.vref),
                ));
            }

            Err(Error::new(
                span.pos,
                format!("{} is not an array nor a function", span.vref.name()),
            ))
        }
    }
}

/// Compiles an array access.
fn compile_array_ref(
    instrs: &mut Vec<Instruction>,
    symtable: &SymbolsTable,
    span: CallSpan,
    key: SymbolKey,
    vtype: ExprType,
    dimensions: usize,
) -> Result<ExprType> {
    let exprs = argspans_to_exprs(span.args);
    let nargs = exprs.len();
    compile_array_indices(instrs, symtable, dimensions, exprs, span.vref_pos)?;

    if !span.vref.accepts(vtype) {
        return Err(Error::new(
            span.vref_pos,
            format!("Incompatible type annotation in {} reference", span.vref),
        ));
    }
    instrs.push(Instruction::ArrayLoad(key, span.vref_pos, nargs));
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
            let key = SymbolKey::from(span.vref.name());
            match symtable.get(&key) {
                Some(SymbolPrototype::Array(vtype, dims)) => {
                    compile_array_ref(instrs, symtable, span, key, *vtype, *dims)
                }

                Some(SymbolPrototype::Callable(md)) => {
                    if !span.vref.accepts_callable(md.return_type()) {
                        return Err(Error::new(
                            span.vref_pos,
                            format!("Incompatible type annotation in {} reference", span.vref),
                        ));
                    }

                    let vtype = match md.return_type() {
                        Some(vtype) => vtype,
                        None => {
                            return Err(Error::new(
                                span.vref_pos,
                                format!("{} is not an array nor a function", span.vref.name()),
                            ));
                        }
                    };

                    if md.is_argless() {
                        return Err(Error::new(
                            span.vref_pos,
                            format!(
                                "In call to {}: expected no arguments nor parenthesis",
                                span.vref.name()
                            ),
                        ));
                    }

                    let span_pos = span.vref_pos;
                    let nargs =
                        compile_function_args(md.syntaxes(), instrs, symtable, span_pos, span.args)
                            .map_err(|e| Error::from_call_error(md, e, span_pos))?;
                    instrs.push(Instruction::FunctionCall(key, vtype, span_pos, nargs));
                    Ok(vtype)
                }

                Some(SymbolPrototype::Variable(_)) => Err(Error::new(
                    span.vref_pos,
                    format!("{} is not an array nor a function", span.vref.name()),
                )),

                None => Err(Error::new(
                    span.vref_pos,
                    format!("Unknown function or array {}", span.vref.name()),
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
pub(super) fn compile_expr_in_command(
    instrs: &mut Vec<Instruction>,
    symtable: &mut SymbolsTable,
    expr: Expr,
) -> Result<ExprType> {
    match expr {
        Expr::Symbol(span) => compile_expr_symbol_ref(instrs, symtable, span),
        expr => compile_expr(instrs, symtable, expr, false),
    }
}

/// Compiles a single expression, expecting it to be of a `target` type.  Applies casts if
/// possible.
pub(super) fn compile_expr_as_type(
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
            Err(Error::new(epos, format!("{} is not a number", etype)))
        } else {
            Err(Error::new(epos, format!("{} is not a {}", etype, target)))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
            .expect_instr(0, Instruction::LoadInteger(SymbolKey::from("j"), lc(1, 5)))
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
                Instruction::FunctionCall(SymbolKey::from("f"), ExprType::Integer, lc(1, 5), 0),
            )
            .expect_instr(1, Instruction::Assign(SymbolKey::from("i")))
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
            .expect_err("1:5: In call to f: function requires arguments")
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
            .expect_err("1:1: In call to C: 1:3: f is not an array nor a function")
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
            .expect_err("1:8: In call to C: 1:10: Incompatible type annotation in a$ reference")
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
            .expect_err("1:1: In call to C: 1:3: Incompatible type annotation in f$ reference")
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
                Instruction::LoadRef(SymbolKey::from("a"), ExprType::Integer, lc(1, 3)),
            )
            .expect_instr(1, Instruction::BuiltinCall(SymbolKey::from("C"), lc(1, 1), 1))
            .check();
    }

    #[test]
    fn test_compile_expr_try_load_command_as_var() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("C"))
            .parse("b = c")
            .compile()
            .expect_err("1:5: c is not an array nor a function")
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
            .expect_err("1:1: In call to C: 1:3: c is not an array nor a function")
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
            .expect_instr(1, Instruction::LoadBoolean(SymbolKey::from("x"), lc(1, 13)))
            .expect_instr(2, Instruction::LogicalOr(lc(1, 10)))
            .expect_instr(3, Instruction::LoadBoolean(SymbolKey::from("y"), lc(1, 19)))
            .expect_instr(4, Instruction::LogicalAnd(lc(1, 15)))
            .expect_instr(5, Instruction::LoadBoolean(SymbolKey::from("z"), lc(1, 29)))
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
            .expect_instr(0, Instruction::LoadInteger(SymbolKey::from("a"), lc(1, 5)))
            .expect_instr(1, Instruction::PushInteger(5, lc(1, 10)))
            .expect_instr(2, Instruction::ShiftRight(lc(1, 7)))
            .expect_instr(3, Instruction::LoadInteger(SymbolKey::from("b"), lc(1, 15)))
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
        L: Fn(SymbolKey, LineCol) -> Instruction,
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
            .expect_instr(0, load_inst(SymbolKey::from("a"), lc(1, 5)))
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
            .expect_instr(0, Instruction::LoadInteger(SymbolKey::from("k"), lc(1, 15)))
            .expect_instr(1, Instruction::PushInteger(1, lc(1, 19)))
            .expect_instr(2, Instruction::AddIntegers(lc(1, 17)))
            .expect_instr(3, Instruction::LoadInteger(SymbolKey::from("j"), lc(1, 12)))
            .expect_instr(4, Instruction::PushInteger(3, lc(1, 9)))
            .expect_instr(5, Instruction::ArrayLoad(SymbolKey::from("foo"), lc(1, 5), 3))
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
            .expect_instr(1, Instruction::ArrayLoad(SymbolKey::from("foo"), lc(1, 5), 1))
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
            .expect_instr(2, Instruction::ArrayLoad(SymbolKey::from("foo"), lc(1, 5), 1))
            .expect_instr(3, Instruction::Assign(SymbolKey::from("i")))
            .check();
    }

    #[test]
    fn test_compile_expr_array_ref_index_bad_type() {
        Tester::default()
            .define("FOO", SymbolPrototype::Array(ExprType::Integer, 1))
            .parse("i = FOO(FALSE)")
            .compile()
            .expect_err("1:9: Array index must be INTEGER, not BOOLEAN")
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
        Tester::default()
            .parse("i = a(4)")
            .compile()
            .expect_err("1:5: Unknown function or array a")
            .check();
    }

    #[test]
    fn test_compile_expr_array_ref_not_an_array() {
        Tester::default()
            .define("a", SymbolPrototype::Variable(ExprType::Integer))
            .parse("i = a(3)")
            .compile()
            .expect_err("1:5: a is not an array nor a function")
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
            .expect_instr(0, Instruction::LoadDouble(SymbolKey::from("k"), lc(1, 15)))
            .expect_instr(1, Instruction::PushInteger(1, lc(1, 19)))
            .expect_instr(2, Instruction::IntegerToDouble)
            .expect_instr(3, Instruction::AddDoubles(lc(1, 17)))
            .expect_instr(4, Instruction::DoubleToInteger)
            .expect_instr(5, Instruction::LoadInteger(SymbolKey::from("j"), lc(1, 12)))
            .expect_instr(6, Instruction::PushInteger(3, lc(1, 9)))
            .expect_instr(
                7,
                Instruction::FunctionCall(SymbolKey::from("FOO"), ExprType::Integer, lc(1, 5), 3),
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
            .expect_err("1:5: Unknown function or array FOO")
            .check();
    }

    #[test]
    fn test_compile_expr_array_or_function_references_variable() {
        Tester::default()
            .parse("i = 3: j = i()")
            .compile()
            .expect_err("1:12: i is not an array nor a function")
            .check();
    }
}
