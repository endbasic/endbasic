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
                (Instruction::LoadRef(span.vref.clone(), span.pos), *atype)
            } else {
                return Err(Error::new(
                    span.pos,
                    format!("{} is not a variable", span.vref.name()),
                ));
            }
        }

        Some(SymbolPrototype::Variable(vtype)) => {
            if allow_varrefs {
                (Instruction::LoadRef(span.vref.clone(), span.pos), *vtype)
            } else {
                (Instruction::Load(key, span.pos), *vtype)
            }
        }

        Some(SymbolPrototype::Callable(md)) => {
            if md.return_type() == VarType::Void {
                return Err(Error::new(
                    span.pos,
                    format!("{} is not an array nor a function", span.vref.name()),
                ));
            }

            if !md.is_argless() {
                return Err(Error::new(
                    span.pos,
                    format!("In call to {}: function requires arguments", span.vref.name()),
                ));
            }

            let nargs = md
                .args_compiler()
                .compile_simple(instrs, symtable, span.pos, vec![])
                .map_err(|e| Error::from_call_error(md, e, span.pos))?;
            debug_assert_eq!(0, nargs, "Argless compiler must have returned zero arguments");
            (Instruction::FunctionCall(key, md.return_type(), span.pos, 0), md.return_type().into())
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
pub fn compile_expr_symbol_ref(
    instrs: &mut Vec<Instruction>,
    symtable: &mut SymbolsTable,
    span: SymbolSpan,
) -> Result<ExprType> {
    let key = SymbolKey::from(span.vref.name());
    match symtable.get(&key) {
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
            instrs.push(Instruction::LoadRef(span.vref, span.pos));
            Ok(vtype)
        }

        Some(SymbolPrototype::Array(vtype, _)) | Some(SymbolPrototype::Variable(vtype)) => {
            let vtype = *vtype;

            if !span.vref.accepts(vtype.into()) {
                return Err(Error::new(
                    span.pos,
                    format!("Incompatible type annotation in {} reference", span.vref),
                ));
            }

            instrs.push(Instruction::LoadRef(span.vref, span.pos));
            Ok(vtype)
        }

        Some(SymbolPrototype::Callable(md)) => {
            if !span.vref.accepts(md.return_type()) {
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
pub fn compile_expr(
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
                    compile_array_ref(instrs, symtable, span, key, *vtype, *dims)
                }

                Some(SymbolPrototype::Callable(md)) => {
                    if !span.fref.accepts(md.return_type()) {
                        return Err(Error::new(
                            span.pos,
                            format!("Incompatible type annotation in {} reference", span.fref),
                        ));
                    }

                    if md.return_type() == VarType::Void {
                        return Err(Error::new(
                            span.pos,
                            format!("{} is not an array nor a function", span.fref.name()),
                        ));
                    }
                    let vtype = md.return_type().into();

                    if md.is_argless() {
                        return Err(Error::new(
                            span.pos,
                            format!(
                                "In call to {}: expected no arguments nor parenthesis",
                                span.fref.name()
                            ),
                        ));
                    }

                    let span_pos = span.pos;
                    let nargs = md
                        .args_compiler()
                        .compile_simple(instrs, symtable, span_pos, span.args)
                        .map_err(|e| Error::from_call_error(md, e, span_pos))?;
                    instrs.push(Instruction::FunctionCall(key, md.return_type(), span_pos, nargs));
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
pub fn compile_expr_in_command(
    instrs: &mut Vec<Instruction>,
    symtable: &mut SymbolsTable,
    expr: Expr,
) -> Result<ExprType> {
    match expr {
        Expr::Symbol(span) => compile_expr_symbol_ref(instrs, symtable, span),
        expr => compile_expr(instrs, symtable, expr, false),
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

    #[test]
    fn test_compile_expr_literals() {
        Tester::default()
            .parse("b = TRUE\nd = 2.3\ni = 5\nt = \"foo\"")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Boolean(true), lc(1, 5)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("b")))
            .expect_instr(2, Instruction::Push(Value::Double(2.3), lc(2, 5)))
            .expect_instr(3, Instruction::Assign(SymbolKey::from("d")))
            .expect_instr(4, Instruction::Push(Value::Integer(5), lc(3, 5)))
            .expect_instr(5, Instruction::Assign(SymbolKey::from("i")))
            .expect_instr(6, Instruction::Push(Value::Text("foo".to_owned()), lc(4, 5)))
            .expect_instr(7, Instruction::Assign(SymbolKey::from("t")))
            .check();
    }

    #[test]
    fn test_compile_expr_varrefs_are_evaluated() {
        Tester::default()
            .define("j", SymbolPrototype::Variable(ExprType::Integer))
            .parse("i = j")
            .compile()
            .expect_instr(0, Instruction::Load(SymbolKey::from("j"), lc(1, 5)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("i")))
            .check();
    }

    #[test]
    fn test_compile_expr_argless_call_ok() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("F", VarType::Integer))
            .parse("i = f")
            .compile()
            .expect_instr(
                0,
                Instruction::FunctionCall(SymbolKey::from("f"), VarType::Integer, lc(1, 5), 0),
            )
            .expect_instr(1, Instruction::Assign(SymbolKey::from("i")))
            .check();
    }

    #[test]
    fn test_compile_expr_argless_call_not_argless() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("F", VarType::Integer).with_typed_syntax(
                &[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax { name: "i", vtype: ExprType::Integer },
                        ArgSepSyntax::End,
                    )],
                    None,
                )],
            ))
            .parse("i = f")
            .compile()
            .expect_err("1:5: In call to f: function requires arguments")
            .check();
    }

    #[test]
    fn test_compile_expr_ref_argless_not_allowed() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("C", VarType::Void).with_typed_syntax(&[
                (
                    &[SingularArgSyntax::RequiredRef(
                        RequiredRefSyntax {
                            name: "x",
                            require_array: false,
                            define_undefined: false,
                        },
                        ArgSepSyntax::End,
                    )],
                    None,
                ),
            ]))
            .define_callable(CallableMetadataBuilder::new("F", VarType::Integer))
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
            .define_callable(CallableMetadataBuilder::new("F", VarType::Integer))
            .parse("a = f$ + 1")
            .compile()
            .expect_err("1:5: Incompatible type annotation in f$ reference")
            .check();
    }

    #[test]
    fn test_compile_expr_ref_bad_annotation_in_varref() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("C", VarType::Void).with_typed_syntax(&[
                (
                    &[SingularArgSyntax::RequiredRef(
                        RequiredRefSyntax {
                            name: "x",
                            require_array: false,
                            define_undefined: false,
                        },
                        ArgSepSyntax::End,
                    )],
                    None,
                ),
            ]))
            .parse("a = 3: c a$")
            .compile()
            .expect_err("1:8: In call to C: 1:10: Incompatible type annotation in a$ reference")
            .check();
    }

    #[test]
    fn test_compile_expr_ref_bad_annotation_in_argless_call() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("C", VarType::Void).with_typed_syntax(&[
                (
                    &[SingularArgSyntax::RequiredRef(
                        RequiredRefSyntax {
                            name: "x",
                            require_array: false,
                            define_undefined: false,
                        },
                        ArgSepSyntax::End,
                    )],
                    None,
                ),
            ]))
            .define_callable(CallableMetadataBuilder::new("F", VarType::Integer))
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
            .define_callable(CallableMetadataBuilder::new("C", VarType::Void).with_typed_syntax(&[
                (
                    &[SingularArgSyntax::RequiredRef(
                        RequiredRefSyntax {
                            name: "x",
                            require_array: true,
                            define_undefined: false,
                        },
                        ArgSepSyntax::End,
                    )],
                    None,
                ),
            ]))
            .parse("c a")
            .compile()
            .expect_instr(0, Instruction::LoadRef(VarRef::new("a", VarType::Auto), lc(1, 3)))
            .expect_instr(1, Instruction::BuiltinCall(SymbolKey::from("C"), lc(1, 1), 1))
            .check();
    }

    #[test]
    fn test_compile_expr_try_load_command_as_var() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("C", VarType::Void))
            .parse("b = c")
            .compile()
            .expect_err("1:5: c is not an array nor a function")
            .check();
    }

    #[test]
    fn test_compile_expr_ref_try_load_command_as_var() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("C", VarType::Void).with_typed_syntax(&[
                (
                    &[SingularArgSyntax::RequiredRef(
                        RequiredRefSyntax {
                            name: "x",
                            require_array: false,
                            define_undefined: false,
                        },
                        ArgSepSyntax::End,
                    )],
                    None,
                ),
            ]))
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
            .expect_instr(0, Instruction::Push(Value::Boolean(true), lc(1, 5)))
            .expect_instr(1, Instruction::Load(SymbolKey::from("x"), lc(1, 13)))
            .expect_instr(2, Instruction::LogicalOr(lc(1, 10)))
            .expect_instr(3, Instruction::Load(SymbolKey::from("y"), lc(1, 19)))
            .expect_instr(4, Instruction::LogicalAnd(lc(1, 15)))
            .expect_instr(5, Instruction::Load(SymbolKey::from("z"), lc(1, 29)))
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
            .expect_instr(0, Instruction::Load(SymbolKey::from("a"), lc(1, 5)))
            .expect_instr(1, Instruction::Push(Value::Integer(5), lc(1, 10)))
            .expect_instr(2, Instruction::ShiftRight(lc(1, 7)))
            .expect_instr(3, Instruction::Load(SymbolKey::from("b"), lc(1, 15)))
            .expect_instr(4, Instruction::ShiftLeft(lc(1, 12)))
            .expect_instr(5, Instruction::Assign(SymbolKey::from("i")))
            .check();
    }

    /// Tests the behavior of one binary operator.
    ///
    /// `make_inst` is the instruction to expect.  `op_name` is the literal name of the operator as
    /// it appears in EndBASIC code.  `test_value` is a value of the right type to use with the
    /// operator call and `test_value_str` is the same value as represented in EndBASIC code.
    fn do_op_test<F: Fn(LineCol) -> Instruction>(
        make_inst: F,
        op_name: &str,
        test_value: Value,
        test_value_str: &str,
    ) {
        Tester::default()
            .define("a", SymbolPrototype::Variable(test_value.as_vartype().into()))
            .parse(&format!("b = a {} {}", op_name, test_value_str))
            .compile()
            .expect_instr(0, Instruction::Load(SymbolKey::from("a"), lc(1, 5)))
            .expect_instr(1, Instruction::Push(test_value, lc(1, 8 + op_name.len())))
            .expect_instr(2, make_inst(lc(1, 7)))
            .expect_instr(3, Instruction::Assign(SymbolKey::from("b")))
            .check();
    }

    #[test]
    fn test_compile_expr_equality_ops() {
        do_op_test(Instruction::EqualBooleans, "=", Value::Boolean(true), "TRUE");
        do_op_test(Instruction::NotEqualBooleans, "<>", Value::Boolean(true), "TRUE");

        do_op_test(Instruction::EqualDoubles, "=", Value::Double(10.2), "10.2");
        do_op_test(Instruction::NotEqualDoubles, "<>", Value::Double(10.2), "10.2");

        do_op_test(Instruction::EqualIntegers, "=", Value::Integer(10), "10");
        do_op_test(Instruction::NotEqualIntegers, "<>", Value::Integer(10), "10");

        do_op_test(Instruction::EqualStrings, "=", Value::Text("foo".to_owned()), "\"foo\"");
        do_op_test(Instruction::NotEqualStrings, "<>", Value::Text("foo".to_owned()), "\"foo\"");
    }

    #[test]
    fn test_compile_expr_relational_ops() {
        do_op_test(Instruction::LessDoubles, "<", Value::Double(10.2), "10.2");
        do_op_test(Instruction::LessEqualDoubles, "<=", Value::Double(10.2), "10.2");
        do_op_test(Instruction::GreaterDoubles, ">", Value::Double(10.2), "10.2");
        do_op_test(Instruction::GreaterEqualDoubles, ">=", Value::Double(10.2), "10.2");

        do_op_test(Instruction::LessIntegers, "<", Value::Integer(10), "10");
        do_op_test(Instruction::LessEqualIntegers, "<=", Value::Integer(10), "10");
        do_op_test(Instruction::GreaterIntegers, ">", Value::Integer(10), "10");
        do_op_test(Instruction::GreaterEqualIntegers, ">=", Value::Integer(10), "10");

        do_op_test(Instruction::LessStrings, "<", Value::Text("foo".to_owned()), "\"foo\"");
        do_op_test(Instruction::LessEqualStrings, "<=", Value::Text("foo".to_owned()), "\"foo\"");
        do_op_test(Instruction::GreaterStrings, ">", Value::Text("foo".to_owned()), "\"foo\"");
        do_op_test(
            Instruction::GreaterEqualStrings,
            ">=",
            Value::Text("foo".to_owned()),
            "\"foo\"",
        );
    }

    #[test]
    fn test_compile_expr_arithmetic_ops() {
        do_op_test(Instruction::AddDoubles, "+", Value::Double(10.2), "10.2");
        do_op_test(Instruction::SubtractDoubles, "-", Value::Double(10.2), "10.2");
        do_op_test(Instruction::MultiplyDoubles, "*", Value::Double(10.2), "10.2");
        do_op_test(Instruction::DivideDoubles, "/", Value::Double(10.2), "10.2");
        do_op_test(Instruction::ModuloDoubles, "MOD", Value::Double(10.2), "10.2");
        do_op_test(Instruction::PowerDoubles, "^", Value::Double(10.2), "10.2");
        Tester::default()
            .define("a", SymbolPrototype::Variable(ExprType::Integer))
            .parse("i = -60.2")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Double(60.2), lc(1, 6)))
            .expect_instr(1, Instruction::NegateDouble(lc(1, 5)))
            .expect_instr(2, Instruction::Assign(SymbolKey::from("i")))
            .check();

        do_op_test(Instruction::AddIntegers, "+", Value::Integer(10), "10");
        do_op_test(Instruction::SubtractIntegers, "-", Value::Integer(10), "10");
        do_op_test(Instruction::MultiplyIntegers, "*", Value::Integer(10), "10");
        do_op_test(Instruction::DivideIntegers, "/", Value::Integer(10), "10");
        do_op_test(Instruction::ModuloIntegers, "MOD", Value::Integer(10), "10");
        do_op_test(Instruction::PowerIntegers, "^", Value::Integer(10), "10");
        Tester::default()
            .define("a", SymbolPrototype::Variable(ExprType::Integer))
            .parse("i = -60")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Integer(60), lc(1, 6)))
            .expect_instr(1, Instruction::NegateInteger(lc(1, 5)))
            .expect_instr(2, Instruction::Assign(SymbolKey::from("i")))
            .check();

        do_op_test(Instruction::ConcatStrings, "+", Value::Text("foo".to_owned()), "\"foo\"");
    }

    #[test]
    fn test_compile_expr_array_ref_exprs() {
        Tester::default()
            .define("FOO", SymbolPrototype::Array(ExprType::Integer, 3))
            .define("j", SymbolPrototype::Variable(ExprType::Integer))
            .define("k", SymbolPrototype::Variable(ExprType::Integer))
            .parse("i = FOO(3, j, k + 1)")
            .compile()
            .expect_instr(0, Instruction::Load(SymbolKey::from("k"), lc(1, 15)))
            .expect_instr(1, Instruction::Push(Value::Integer(1), lc(1, 19)))
            .expect_instr(2, Instruction::AddIntegers(lc(1, 17)))
            .expect_instr(3, Instruction::Load(SymbolKey::from("j"), lc(1, 12)))
            .expect_instr(4, Instruction::Push(Value::Integer(3), lc(1, 9)))
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
            .expect_instr(0, Instruction::Push(Value::Integer(3), lc(1, 10)))
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
            .expect_instr(0, Instruction::Push(Value::Double(3.8), lc(1, 9)))
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
                CallableMetadataBuilder::new("FOO", VarType::Integer).with_typed_syntax(&[(
                    &[],
                    Some(&RepeatedSyntax {
                        name: "expr",
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
            .expect_instr(0, Instruction::Load(SymbolKey::from("k"), lc(1, 15)))
            .expect_instr(1, Instruction::Push(Value::Integer(1), lc(1, 19)))
            .expect_instr(2, Instruction::IntegerToDouble)
            .expect_instr(3, Instruction::AddDoubles(lc(1, 17)))
            .expect_instr(4, Instruction::DoubleToInteger)
            .expect_instr(5, Instruction::Load(SymbolKey::from("j"), lc(1, 12)))
            .expect_instr(6, Instruction::Push(Value::Integer(3), lc(1, 9)))
            .expect_instr(
                7,
                Instruction::FunctionCall(SymbolKey::from("FOO"), VarType::Integer, lc(1, 5), 3),
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
