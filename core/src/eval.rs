// EndBASIC
// Copyright 2020 Julio Merino
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

//! Evaluator for EndBASIC expressions.

use crate::ast::*;
use crate::reader::LineCol;
use crate::syms::{CallError, CallableMetadata, Function, Symbol, Symbols};
use crate::value;
use async_recursion::async_recursion;
use std::rc::Rc;

/// Evaluation errors.
#[derive(Debug, thiserror::Error)]
#[error("{}:{}: {}", pos.line, pos.col, message)]
pub struct Error {
    pos: LineCol,
    message: String,
}

impl Error {
    /// Constructs a new evaluation error from a textual `message` that happened at `pos`.
    pub(crate) fn new<S: Into<String>>(pos: LineCol, message: S) -> Self {
        Self { pos, message: message.into() }
    }

    /// Annotates a call evaluation error with the function's metadata.
    fn from_call_error(md: &CallableMetadata, e: CallError, pos: LineCol) -> Self {
        let message = match e {
            CallError::ArgumentError(pos, e) => {
                format!("In call to {}: {}:{}: {}", md.name(), pos.line, pos.col, e)
            }
            CallError::EvalError(e) => format!("In call to {}: {}", md.name(), e),
            CallError::InternalError(pos, e) => {
                format!("In call to {}: {}:{}: {}", md.name(), pos.line, pos.col, e)
            }
            CallError::IoError(e) => format!("In call to {}: {}", md.name(), e),
            CallError::NestedError(e) => e,
            CallError::SyntaxError if md.syntax().is_empty() => {
                format!("In call to {}: expected no arguments", md.name())
            }
            CallError::SyntaxError => {
                format!("In call to {}: expected {}", md.name(), md.syntax())
            }
        };
        Self { pos, message }
    }

    /// Annotates a value error with a position.
    pub fn from_value_error(e: value::Error, pos: LineCol) -> Self {
        Self { pos, message: e.message }
    }
}

/// Result for evaluation return values.
pub type Result<T> = std::result::Result<T, Error>;

/// Evaluates all arguments given to a function.
///
/// This is a convenience function to simplify the processing of arguments because most functions
/// do not care about unevaluated expressions.  However, using this function is inefficient in many
/// occasions because we are allocating a vector that we don't need.
// TODO(jmmv): Per the efficiency comment above, consider eliminating this function.
#[async_recursion(?Send)]
pub async fn eval_all(exprs: &[Expr], syms: &mut Symbols) -> Result<Vec<Value>> {
    let mut values = Vec::with_capacity(exprs.len());
    for expr in exprs {
        values.push(expr.eval(syms).await?);
    }
    Ok(values)
}

impl Expr {
    /// Returns the start position of the expression.
    pub fn start_pos(&self) -> LineCol {
        match self {
            Expr::Boolean(span) => span.pos,
            Expr::Double(span) => span.pos,
            Expr::Integer(span) => span.pos,
            Expr::Text(span) => span.pos,

            Expr::Symbol(span) => span.pos,

            Expr::And(span) => span.lhs.start_pos(),
            Expr::Or(span) => span.lhs.start_pos(),
            Expr::Xor(span) => span.lhs.start_pos(),
            Expr::Not(span) => span.pos,

            Expr::ShiftLeft(span) => span.lhs.start_pos(),
            Expr::ShiftRight(span) => span.lhs.start_pos(),

            Expr::Equal(span) => span.lhs.start_pos(),
            Expr::NotEqual(span) => span.lhs.start_pos(),
            Expr::Less(span) => span.lhs.start_pos(),
            Expr::LessEqual(span) => span.lhs.start_pos(),
            Expr::Greater(span) => span.lhs.start_pos(),
            Expr::GreaterEqual(span) => span.lhs.start_pos(),

            Expr::Add(span) => span.lhs.start_pos(),
            Expr::Subtract(span) => span.lhs.start_pos(),
            Expr::Multiply(span) => span.lhs.start_pos(),
            Expr::Divide(span) => span.lhs.start_pos(),
            Expr::Modulo(span) => span.lhs.start_pos(),
            Expr::Power(span) => span.lhs.start_pos(),
            Expr::Negate(span) => span.pos,

            Expr::Call(span) => span.pos,
        }
    }

    /// Evaluates the subscripts of an array reference.
    async fn eval_array_args(
        &self,
        syms: &mut Symbols,
        span: &FunctionCallSpan,
    ) -> Result<Vec<i32>> {
        let values = eval_all(&span.args, syms).await?;
        let mut subscripts = Vec::with_capacity(span.args.len());
        for (e, v) in span.args.iter().zip(values) {
            match v {
                Value::Integer(i) => subscripts.push(i),
                _ => return Err(Error::new(e.start_pos(), "Array subscripts must be integers")),
            }
        }
        Ok(subscripts)
    }

    /// Evaluates a function call specified by `fref` and arguments `args` on the function `f`.
    #[async_recursion(?Send)]
    async fn eval_function_call(
        &self,
        syms: &mut Symbols,
        span: &FunctionCallSpan,
        f: Rc<dyn Function>,
    ) -> Result<Value> {
        let metadata = f.metadata();
        if !span.fref.accepts(metadata.return_type()) {
            return Err(Error::new(span.pos, "Incompatible type annotation for function call"));
        }

        let result = f.exec(span, syms).await;
        match result {
            Ok(value) => {
                debug_assert!(metadata.return_type() != VarType::Auto);
                let fref = VarRef::new(span.fref.name(), metadata.return_type());
                // Given that we only support built-in functions at the moment, this
                // could well be an assertion.  Doing so could turn into a time bomb
                // when/if we add user-defined functions, so handle the problem as an
                // error.
                if !fref.accepts(value.as_vartype()) {
                    return Err(Error::new(
                        span.pos,
                        format!(
                            "Value returned by {} is incompatible with its type definition",
                            fref.name(),
                        ),
                    ));
                }
                Ok(value)
            }
            Err(e) => Err(Error::from_call_error(metadata, e, span.pos)),
        }
    }

    /// Evaluates the expression to a value.
    ///
    /// Symbols are resolved by querying `syms`.  Errors in the computation are returned via the
    /// special `Value::Bad` type.
    #[async_recursion(?Send)]
    pub async fn eval(&self, syms: &mut Symbols) -> Result<Value> {
        match self {
            Expr::Boolean(span) => Ok(Value::Boolean(span.value)),
            Expr::Double(span) => Ok(Value::Double(span.value)),
            Expr::Integer(span) => Ok(Value::Integer(span.value)),
            Expr::Text(span) => Ok(Value::Text(span.value.clone())),

            Expr::Symbol(span) => {
                match syms.get(&span.vref).map_err(|e| Error::from_value_error(e, span.pos))? {
                    Some(Symbol::Variable(v)) => Ok(v.clone()),
                    Some(Symbol::Function(f)) => {
                        if !f.metadata().is_argless() {
                            return Err(Error::new(
                                span.pos,
                                format!("{} requires one or more arguments", span.vref.name()),
                            ));
                        }
                        let f = f.clone();
                        let span = FunctionCallSpan {
                            fref: span.vref.clone(),
                            args: vec![],
                            pos: span.pos,
                        };
                        Ok(self.eval_function_call(syms, &span, f).await?)
                    }
                    Some(_) => {
                        Err(Error::new(span.pos, format!("{} is not a variable", span.vref.name())))
                    }
                    None => Err(Error::new(
                        span.pos,
                        format!("Undefined variable {}", span.vref.name()),
                    )),
                }
            }

            Expr::And(span) => {
                Ok(Value::and(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)
                    .map_err(|e| Error::from_value_error(e, span.pos))?)
            }
            Expr::Or(span) => {
                Ok(Value::or(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)
                    .map_err(|e| Error::from_value_error(e, span.pos))?)
            }
            Expr::Xor(span) => {
                Ok(Value::xor(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)
                    .map_err(|e| Error::from_value_error(e, span.pos))?)
            }
            Expr::Not(span) => Ok(Value::not(&span.expr.eval(syms).await?)
                .map_err(|e| Error::from_value_error(e, span.pos))?),

            Expr::ShiftLeft(span) => {
                Ok(Value::shl(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)
                    .map_err(|e| Error::from_value_error(e, span.pos))?)
            }
            Expr::ShiftRight(span) => {
                Ok(Value::shr(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)
                    .map_err(|e| Error::from_value_error(e, span.pos))?)
            }

            Expr::Equal(span) => {
                Ok(Value::eq(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)
                    .map_err(|e| Error::from_value_error(e, span.pos))?)
            }
            Expr::NotEqual(span) => {
                Ok(Value::ne(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)
                    .map_err(|e| Error::from_value_error(e, span.pos))?)
            }
            Expr::Less(span) => {
                Ok(Value::lt(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)
                    .map_err(|e| Error::from_value_error(e, span.pos))?)
            }
            Expr::LessEqual(span) => {
                Ok(Value::le(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)
                    .map_err(|e| Error::from_value_error(e, span.pos))?)
            }
            Expr::Greater(span) => {
                Ok(Value::gt(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)
                    .map_err(|e| Error::from_value_error(e, span.pos))?)
            }
            Expr::GreaterEqual(span) => {
                Ok(Value::ge(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)
                    .map_err(|e| Error::from_value_error(e, span.pos))?)
            }

            Expr::Add(span) => {
                Ok(Value::add(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)
                    .map_err(|e| Error::from_value_error(e, span.pos))?)
            }
            Expr::Subtract(span) => {
                Ok(Value::sub(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)
                    .map_err(|e| Error::from_value_error(e, span.pos))?)
            }
            Expr::Multiply(span) => {
                Ok(Value::mul(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)
                    .map_err(|e| Error::from_value_error(e, span.pos))?)
            }
            Expr::Divide(span) => {
                Ok(Value::div(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)
                    .map_err(|e| Error::from_value_error(e, span.pos))?)
            }
            Expr::Modulo(span) => {
                Ok(Value::modulo(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)
                    .map_err(|e| Error::from_value_error(e, span.pos))?)
            }
            Expr::Power(span) => {
                Ok(Value::pow(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)
                    .map_err(|e| Error::from_value_error(e, span.pos))?)
            }
            Expr::Negate(span) => Ok(Value::neg(&span.expr.eval(syms).await?)
                .map_err(|e| Error::from_value_error(e, span.pos))?),

            Expr::Call(span) => {
                match syms.get(&span.fref).map_err(|e| Error::from_value_error(e, span.pos))? {
                    Some(Symbol::Array(_)) => (), // Fallthrough.
                    Some(Symbol::Function(f)) => {
                        if f.metadata().is_argless() {
                            return Err(Error::new(
                                span.pos,
                                format!(
                                    "In call to {}: expected no arguments nor parenthesis",
                                    f.metadata().name()
                                ),
                            ));
                        }
                        let f = f.clone();
                        return self.eval_function_call(syms, span, f).await;
                    }

                    Some(_) => {
                        return Err(Error::new(
                            span.pos,
                            format!("{} is not an array or a function", span.fref),
                        ))
                    }
                    None => {
                        return Err(Error::new(
                            span.pos,
                            format!("Unknown function or array {}", span.fref),
                        ))
                    }
                }

                // We have to handle arrays outside of the match above because we cannot hold a
                // reference to the array while we evaluate subscripts.  This implies that we have
                // to do a second lookup of the array right below, which isn't great...
                let subscripts = self.eval_array_args(syms, span).await?;
                match syms.get(&span.fref).map_err(|e| Error::from_value_error(e, span.pos))? {
                    Some(Symbol::Array(array)) => Ok(array
                        .index(&subscripts)
                        .cloned()
                        .map_err(|e| Error::from_value_error(e, span.pos))?),
                    _ => unreachable!(),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::VarRef;
    use crate::reader::LineCol;
    use crate::testutils::*;
    use futures_lite::future::block_on;
    use std::cell::RefCell;

    /// Syntactic sugar to instantiate a `LineCol` for testing.
    fn lc(line: usize, col: usize) -> LineCol {
        LineCol { line, col }
    }

    /// Syntactic sugar to instantiate an `Expr::Boolean` for testing.
    fn expr_boolean(value: bool) -> Expr {
        // The position is currently irrelevant in the tests below as we never query it.
        let pos = LineCol { line: 1234, col: 5768 };

        Expr::Boolean(BooleanSpan { value, pos })
    }

    /// Syntactic sugar to instantiate an `Expr::Double` for testing.
    fn expr_double(value: f64) -> Expr {
        // The position is currently irrelevant in the tests below as we never query it.
        let pos = LineCol { line: 1234, col: 5768 };

        Expr::Double(DoubleSpan { value, pos })
    }

    /// Syntactic sugar to instantiate an `Expr::Integer` for testing.
    fn expr_integer(value: i32) -> Expr {
        // The position is currently irrelevant in the tests below as we never query it.
        let pos = LineCol { line: 1234, col: 5768 };

        Expr::Integer(IntegerSpan { value, pos })
    }

    /// Syntactic sugar to instantiate an `Expr::Text` for testing.
    fn expr_text<S: Into<String>>(value: S) -> Expr {
        // The position is currently irrelevant in the tests below as we never query it.
        let pos = LineCol { line: 1234, col: 5768 };

        Expr::Text(TextSpan { value: value.into(), pos })
    }

    /// Syntactic sugar to instantiate an `Expr::Symbol` for testing.
    fn expr_symbol(vref: VarRef) -> Expr {
        // The position is currently irrelevant in the tests below as we never query it.
        let pos = LineCol { line: 1234, col: 5768 };

        Expr::Symbol(SymbolSpan { vref, pos })
    }

    #[test]
    fn test_expr_literals() {
        let mut syms = Symbols::default();
        assert_eq!(Value::Boolean(true), block_on(expr_boolean(true).eval(&mut syms)).unwrap());
        assert_eq!(Value::Double(0.0), block_on(expr_double(0.0).eval(&mut syms)).unwrap());
        assert_eq!(Value::Integer(0), block_on(expr_integer(0).eval(&mut syms)).unwrap());
        assert_eq!(Value::Text("z".to_owned()), block_on(expr_text("z").eval(&mut syms)).unwrap());
    }

    #[test]
    fn test_expr_symbol() {
        let bool_ref = VarRef::new("a_boolean", VarType::Auto);
        let bool_val = Value::Boolean(true);
        let double_ref = VarRef::new("a_double", VarType::Auto);
        let double_val = Value::Double(0.0);
        let int_ref = VarRef::new("an_integer", VarType::Auto);
        let int_val = Value::Integer(0);
        let text_ref = VarRef::new("a_string", VarType::Auto);
        let text_val = Value::Text("x".to_owned());

        let mut syms = Symbols::default();
        syms.set_var(&bool_ref, bool_val.clone()).unwrap();
        syms.set_var(&double_ref, double_val.clone()).unwrap();
        syms.set_var(&int_ref, int_val.clone()).unwrap();
        syms.set_var(&text_ref, text_val.clone()).unwrap();

        assert_eq!(bool_val, block_on(expr_symbol(bool_ref).eval(&mut syms)).unwrap());
        assert_eq!(double_val, block_on(expr_symbol(double_ref).eval(&mut syms)).unwrap());
        assert_eq!(int_val, block_on(expr_symbol(int_ref).eval(&mut syms)).unwrap());
        assert_eq!(text_val, block_on(expr_symbol(text_ref).eval(&mut syms)).unwrap());

        assert_eq!(
            "7:6: Undefined variable x",
            format!(
                "{}",
                block_on(
                    Expr::Symbol(SymbolSpan {
                        vref: VarRef::new("x", VarType::Auto),
                        pos: lc(7, 6)
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );
    }

    #[test]
    fn test_expr_logical_ops() {
        let binary_args = Box::from(BinaryOpSpan {
            lhs: expr_boolean(false),
            rhs: expr_integer(0),
            pos: lc(3, 2),
        });
        let unary_args = Box::from(UnaryOpSpan { expr: expr_double(0.0), pos: lc(7, 4) });

        // These tests just make sure that we delegate to the `Value` operations for each
        // expression operator to essentially avoid duplicating all those tests.  We do this by
        // triggering errors and rely on the fact that their messages are different for every
        // operation.
        let mut syms = Symbols::default();
        assert_eq!(
            "3:2: Cannot AND FALSE and 0",
            format!("{}", block_on(Expr::And(binary_args.clone()).eval(&mut syms)).unwrap_err())
        );
        assert_eq!(
            "3:2: Cannot OR FALSE and 0",
            format!("{}", block_on(Expr::Or(binary_args.clone()).eval(&mut syms)).unwrap_err())
        );
        assert_eq!(
            "3:2: Cannot XOR FALSE and 0",
            format!("{}", block_on(Expr::Xor(binary_args).eval(&mut syms)).unwrap_err())
        );
        assert_eq!(
            "7:4: Cannot apply NOT to 0.0",
            format!("{}", block_on(Expr::Not(unary_args).eval(&mut syms)).unwrap_err())
        );
    }

    #[test]
    fn test_expr_relational_ops() {
        let binary_args = Box::from(BinaryOpSpan {
            lhs: expr_boolean(false),
            rhs: expr_integer(0),
            pos: lc(5, 8),
        });

        // These tests just make sure that we delegate to the `Value` operations for each
        // expression operator to essentially avoid duplicating all those tests.  We do this by
        // triggering errors and rely on the fact that their messages are different for every
        // operation.
        let mut syms = Symbols::default();
        assert_eq!(
            "5:8: Cannot compare FALSE and 0 with =",
            format!("{}", block_on(Expr::Equal(binary_args.clone()).eval(&mut syms)).unwrap_err())
        );
        assert_eq!(
            "5:8: Cannot compare FALSE and 0 with <>",
            format!(
                "{}",
                block_on(Expr::NotEqual(binary_args.clone()).eval(&mut syms)).unwrap_err()
            )
        );
        assert_eq!(
            "5:8: Cannot compare FALSE and 0 with <",
            format!("{}", block_on(Expr::Less(binary_args.clone()).eval(&mut syms)).unwrap_err())
        );
        assert_eq!(
            "5:8: Cannot compare FALSE and 0 with <=",
            format!(
                "{}",
                block_on(Expr::LessEqual(binary_args.clone()).eval(&mut syms)).unwrap_err()
            )
        );
        assert_eq!(
            "5:8: Cannot compare FALSE and 0 with >",
            format!(
                "{}",
                block_on(Expr::Greater(binary_args.clone()).eval(&mut syms)).unwrap_err()
            )
        );
        assert_eq!(
            "5:8: Cannot compare FALSE and 0 with >=",
            format!("{}", block_on(Expr::GreaterEqual(binary_args).eval(&mut syms)).unwrap_err())
        );
    }

    #[test]
    fn test_expr_arithmetic_ops() {
        let binary_args = Box::from(BinaryOpSpan {
            lhs: expr_boolean(false),
            rhs: expr_integer(0),
            pos: lc(5, 8),
        });
        let unary_args = Box::from(UnaryOpSpan { expr: expr_boolean(false), pos: lc(2, 1) });

        // These tests just make sure that we delegate to the `Value` operations for each
        // expression operator to essentially avoid duplicating all those tests.  We do this by
        // triggering errors and rely on the fact that their messages are different for every
        // operation.
        let mut syms = Symbols::default();
        assert_eq!(
            "5:8: Cannot add FALSE and 0",
            format!("{}", block_on(Expr::Add(binary_args.clone()).eval(&mut syms)).unwrap_err())
        );
        assert_eq!(
            "5:8: Cannot subtract 0 from FALSE",
            format!(
                "{}",
                block_on(Expr::Subtract(binary_args.clone()).eval(&mut syms)).unwrap_err()
            )
        );
        assert_eq!(
            "5:8: Cannot multiply FALSE by 0",
            format!(
                "{}",
                block_on(Expr::Multiply(binary_args.clone()).eval(&mut syms)).unwrap_err()
            )
        );
        assert_eq!(
            "5:8: Cannot divide FALSE by 0",
            format!("{}", block_on(Expr::Divide(binary_args.clone()).eval(&mut syms)).unwrap_err())
        );
        assert_eq!(
            "5:8: Cannot modulo FALSE by 0",
            format!("{}", block_on(Expr::Modulo(binary_args.clone()).eval(&mut syms)).unwrap_err())
        );
        assert_eq!(
            "5:8: Cannot raise FALSE to the power of 0",
            format!("{}", block_on(Expr::Power(binary_args).eval(&mut syms)).unwrap_err())
        );
        assert_eq!(
            "2:1: Cannot negate FALSE",
            format!("{}", block_on(Expr::Negate(unary_args).eval(&mut syms)).unwrap_err())
        );
    }

    #[test]
    fn test_expr_various_ops_and_vars() {
        let xref = VarRef::new("x", VarType::Integer);
        let yref = VarRef::new("y", VarType::Integer);

        let mut syms = Symbols::default();
        syms.set_var(&xref, Value::Integer(10)).unwrap();
        syms.set_var(&yref, Value::Integer(3)).unwrap();

        assert_eq!(
            Value::Integer(36),
            block_on(
                Expr::Multiply(Box::from(BinaryOpSpan {
                    lhs: Expr::Add(Box::from(BinaryOpSpan {
                        lhs: expr_symbol(xref.clone()),
                        rhs: expr_integer(2),
                        pos: lc(0, 0),
                    })),
                    rhs: expr_symbol(yref.clone()),
                    pos: lc(0, 0),
                }))
                .eval(&mut syms)
            )
            .unwrap()
        );

        assert_eq!(
            Value::Boolean(true),
            block_on(
                Expr::Equal(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(xref),
                    rhs: Expr::Add(Box::from(BinaryOpSpan {
                        lhs: expr_integer(7),
                        rhs: expr_symbol(yref),
                        pos: lc(0, 0),
                    })),
                    pos: lc(0, 0),
                }))
                .eval(&mut syms)
            )
            .unwrap()
        );

        assert_eq!(
            "3:4: Cannot add 7 and TRUE",
            format!(
                "{}",
                block_on(
                    Expr::Equal(Box::from(BinaryOpSpan {
                        lhs: expr_integer(3),
                        rhs: Expr::Add(Box::from(BinaryOpSpan {
                            lhs: expr_integer(7),
                            rhs: expr_boolean(true),
                            pos: lc(3, 4),
                        })),
                        pos: lc(1, 2),
                    }))
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );
    }

    #[test]
    fn test_expr_array_simple() {
        let xref = VarRef::new("x", VarType::Integer);

        let mut syms = Symbols::default();
        syms.dim_array("x", VarType::Integer, vec![2, 4]).unwrap();
        match syms.get_mut(&xref).unwrap().unwrap() {
            Symbol::Array(array) => array.assign(&[1, 3], Value::Integer(8)).unwrap(),
            _ => panic!("Got something that is not the array we asked for"),
        }

        assert_eq!(
            Value::Integer(0),
            block_on(
                Expr::Call(FunctionCallSpan {
                    fref: VarRef::new("X", VarType::Auto),
                    args: vec![expr_integer(0), expr_integer(3)],
                    pos: lc(0, 0),
                })
                .eval(&mut syms)
            )
            .unwrap()
        );

        assert_eq!(
            Value::Integer(8),
            block_on(
                Expr::Call(FunctionCallSpan {
                    fref: VarRef::new("X", VarType::Auto),
                    args: vec![expr_integer(1), expr_integer(3)],
                    pos: lc(0, 0),
                })
                .eval(&mut syms)
            )
            .unwrap()
        );

        assert_eq!(
            Value::Integer(8),
            block_on(
                Expr::Call(FunctionCallSpan {
                    fref: VarRef::new("X", VarType::Integer),
                    args: vec![expr_integer(1), expr_integer(3)],
                    pos: lc(0, 0),
                })
                .eval(&mut syms)
            )
            .unwrap()
        );

        assert_eq!(
            "3:4: Incompatible types in X# reference",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("X", VarType::Double),
                        args: vec![expr_integer(1), expr_integer(3)],
                        pos: lc(3, 4),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "3:4: Cannot index array with 1 subscripts; need 2",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("X", VarType::Integer),
                        args: vec![expr_integer(1)],
                        pos: lc(3, 4),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "3:4: Subscript -1 cannot be negative",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("X", VarType::Integer),
                        args: vec![expr_integer(0), expr_integer(-1)],
                        pos: lc(3, 4),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "3:4: Subscript 10 exceeds limit of 2",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("X", VarType::Integer),
                        args: vec![expr_integer(10), expr_integer(0)],
                        pos: lc(3, 4),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "3:4: Unknown function or array y$",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("y".to_owned(), VarType::Text),
                        args: vec![],
                        pos: lc(3, 4),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );
    }

    #[test]
    fn test_expr_function_call_simple() {
        let xref = VarRef::new("x", VarType::Integer);
        let mut syms = SymbolsBuilder::default().add_function(SumFunction::new()).build();
        syms.set_var(&xref, Value::Integer(5)).unwrap();

        assert_eq!(
            Value::Integer(0),
            block_on(
                Expr::Call(FunctionCallSpan {
                    fref: VarRef::new("SUM".to_owned(), VarType::Auto),
                    args: vec![],
                    pos: lc(0, 0),
                })
                .eval(&mut syms)
            )
            .unwrap()
        );

        assert_eq!(
            Value::Integer(5),
            block_on(
                Expr::Call(FunctionCallSpan {
                    fref: VarRef::new("sum".to_owned(), VarType::Auto),
                    args: vec![expr_integer(5)],
                    pos: lc(0, 0),
                })
                .eval(&mut syms)
            )
            .unwrap()
        );

        assert_eq!(
            Value::Integer(7),
            block_on(
                Expr::Call(FunctionCallSpan {
                    fref: VarRef::new("SUM".to_owned(), VarType::Auto),
                    args: vec![expr_integer(5), expr_integer(2)],
                    pos: lc(0, 0),
                })
                .eval(&mut syms)
            )
            .unwrap()
        );

        assert_eq!(
            Value::Integer(23),
            block_on(
                Expr::Call(FunctionCallSpan {
                    fref: VarRef::new("SUM".to_owned(), VarType::Integer),
                    args: vec![
                        expr_symbol(xref),
                        expr_integer(8),
                        Expr::Subtract(Box::from(BinaryOpSpan {
                            lhs: expr_integer(100),
                            rhs: expr_integer(90),
                            pos: lc(0, 0),
                        }))
                    ],
                    pos: lc(0, 0),
                })
                .eval(&mut syms)
            )
            .unwrap()
        );

        assert_eq!(
            "8:7: Incompatible types in SUM$ reference",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("SUM".to_owned(), VarType::Text),
                        args: vec![],
                        pos: lc(8, 7),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "4:6: Unknown function or array SUMA$",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("SUMA".to_owned(), VarType::Text),
                        args: vec![],
                        pos: lc(4, 6),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );
    }

    #[test]
    fn test_expr_function_call_type_check() {
        {
            let mut syms = SymbolsBuilder::default()
                .add_function(TypeCheckFunction::new(Value::Boolean(true)))
                .build();
            assert_eq!(
                Value::Boolean(true),
                block_on(
                    Expr::Symbol(SymbolSpan {
                        vref: VarRef::new("TYPE_CHECK".to_owned(), VarType::Auto),
                        pos: lc(0, 0),
                    })
                    .eval(&mut syms)
                )
                .unwrap()
            );
        }

        {
            let mut syms = SymbolsBuilder::default()
                .add_function(TypeCheckFunction::new(Value::Integer(5)))
                .build();
            assert_eq!(
                "9:2: Value returned by TYPE_CHECK is incompatible with its type definition",
                format!(
                    "{}",
                    block_on(
                        Expr::Symbol(SymbolSpan {
                            vref: VarRef::new("TYPE_CHECK".to_owned(), VarType::Auto),
                            pos: lc(9, 2),
                        })
                        .eval(&mut syms)
                    )
                    .unwrap_err()
                )
            );
        }
    }

    #[test]
    fn test_expr_function_error_check() {
        let mut syms = SymbolsBuilder::default().add_function(RaiseFunction::new()).build();

        assert_eq!(
            "1:1: In call to RAISE: 4:5: Bad argument",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("RAISE".to_owned(), VarType::Auto),
                        args: vec![Expr::Text(TextSpan {
                            value: "argument".to_owned(),
                            pos: lc(4, 5)
                        })],
                        pos: lc(1, 1),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "3:2: In call to RAISE: 4:5: Some eval error",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("RAISE".to_owned(), VarType::Auto),
                        args: vec![Expr::Text(TextSpan {
                            value: "eval".to_owned(),
                            pos: lc(4, 5)
                        })],
                        pos: lc(3, 2),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "5:1: In call to RAISE: 4:5: Some internal error",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("RAISE".to_owned(), VarType::Auto),
                        args: vec![Expr::Text(TextSpan {
                            value: "internal".to_owned(),
                            pos: lc(4, 5)
                        })],
                        pos: lc(5, 1),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "5:1: In call to RAISE: Some I/O error",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("RAISE".to_owned(), VarType::Auto),
                        args: vec![Expr::Text(TextSpan { value: "io".to_owned(), pos: lc(4, 5) })],
                        pos: lc(5, 1),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "7:4: In call to RAISE: expected arg1$",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("RAISE".to_owned(), VarType::Auto),
                        args: vec![expr_text("syntax")],
                        pos: lc(7, 4),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );
    }

    #[test]
    fn test_expr_call_non_function() {
        let mut syms = SymbolsBuilder::default()
            .add_var("SOMEVAR", Value::Integer(0))
            .add_command(OutCommand::new(Rc::from(RefCell::from(vec![]))))
            .build();

        assert_eq!(
            "3:9: SOMEVAR is not an array or a function",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("SOMEVAR".to_owned(), VarType::Auto),
                        args: vec![],
                        pos: lc(3, 9),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "3:7: OUT is not an array or a function",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("OUT".to_owned(), VarType::Auto),
                        args: vec![],
                        pos: lc(3, 7),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );
    }
}
