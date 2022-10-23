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
use crate::syms::{CallError, CallableMetadata, Function, Symbol, Symbols};
use crate::value;
use async_recursion::async_recursion;
use std::rc::Rc;

/// Evaluation errors.
#[derive(Debug, thiserror::Error)]
#[error("{message}")]
pub struct Error {
    message: String,
}

impl Error {
    /// Constructs a new evaluation error from a textual `message`.
    pub(crate) fn new<S: Into<String>>(message: S) -> Self {
        Self { message: message.into() }
    }

    /// Annotates a call evaluation error with the function's metadata.
    pub(crate) fn from_call_error(md: &CallableMetadata, e: CallError) -> Self {
        let message = match e {
            CallError::ArgumentError(e) => {
                format!("Syntax error in call to {}: {}", md.name(), e)
            }
            CallError::EvalError(e) => format!("Error in call to {}: {}", md.name(), e),
            CallError::InternalError(e) => format!("Error in call to {}: {}", md.name(), e),
            CallError::IoError(e) => format!("Error in call to {}: {}", md.name(), e),
            CallError::SyntaxError => {
                format!("Syntax error in call to {}: expected {}", md.name(), md.syntax())
            }
        };
        Self { message }
    }
}

impl From<value::Error> for Error {
    fn from(e: value::Error) -> Self {
        Error { message: format!("{}", e) }
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
    /// Evaluates the subscripts of an array reference.
    async fn eval_array_args(
        &self,
        syms: &mut Symbols,
        span: &FunctionCallSpan,
    ) -> Result<Vec<i32>> {
        let values = eval_all(&span.args, syms).await?;
        let mut subscripts = Vec::with_capacity(span.args.len());
        for v in values {
            match v {
                Value::Integer(i) => subscripts.push(i),
                _ => return Err(Error::new("Array subscripts must be integers")),
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
            return Err(Error::new("Incompatible type annotation for function call"));
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
                    return Err(Error::new(format!(
                        "Value returned by {} is incompatible with its type definition",
                        fref.name(),
                    )));
                }
                Ok(value)
            }
            Err(e) => Err(Error::from_call_error(metadata, e)),
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

            Expr::Symbol(span) => Ok(syms.get_var(&span.vref)?.clone()),

            Expr::And(span) => {
                Ok(Value::and(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)?)
            }
            Expr::Or(span) => {
                Ok(Value::or(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)?)
            }
            Expr::Xor(span) => {
                Ok(Value::xor(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)?)
            }
            Expr::Not(span) => Ok(Value::not(&span.expr.eval(syms).await?)?),

            Expr::Equal(span) => {
                Ok(Value::eq(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)?)
            }
            Expr::NotEqual(span) => {
                Ok(Value::ne(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)?)
            }
            Expr::Less(span) => {
                Ok(Value::lt(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)?)
            }
            Expr::LessEqual(span) => {
                Ok(Value::le(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)?)
            }
            Expr::Greater(span) => {
                Ok(Value::gt(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)?)
            }
            Expr::GreaterEqual(span) => {
                Ok(Value::ge(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)?)
            }

            Expr::Add(span) => {
                Ok(Value::add(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)?)
            }
            Expr::Subtract(span) => {
                Ok(Value::sub(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)?)
            }
            Expr::Multiply(span) => {
                Ok(Value::mul(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)?)
            }
            Expr::Divide(span) => {
                Ok(Value::div(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)?)
            }
            Expr::Modulo(span) => {
                Ok(Value::modulo(&span.lhs.eval(syms).await?, &span.rhs.eval(syms).await?)?)
            }
            Expr::Negate(span) => Ok(Value::neg(&span.expr.eval(syms).await?)?),

            Expr::Call(span) => {
                match syms.get(&span.fref)? {
                    Some(Symbol::Array(_)) => (), // Fallthrough.
                    Some(Symbol::Function(f)) => {
                        let f = f.clone();
                        return self.eval_function_call(syms, span, f).await;
                    }
                    Some(_) => {
                        return Err(Error::new(format!(
                            "{} is not an array or a function",
                            span.fref
                        )))
                    }
                    None => {
                        return Err(Error::new(format!("Unknown function or array {}", span.fref)))
                    }
                }

                // We have to handle arrays outside of the match above because we cannot hold a
                // reference to the array while we evaluate subscripts.  This implies that we have
                // to do a second lookup of the array right below, which isn't great...
                let subscripts = self.eval_array_args(syms, span).await?;
                let v = match syms.get(&span.fref)? {
                    Some(Symbol::Array(array)) => array.index(&subscripts).map(|v| v.clone())?,
                    _ => unreachable!(),
                };
                Ok(v)
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
            "Undefined variable x",
            format!(
                "{}",
                block_on(expr_symbol(VarRef::new("x", VarType::Auto)).eval(&mut syms)).unwrap_err()
            )
        );
    }

    #[test]
    fn test_expr_logical_ops() {
        let binary_args = Box::from(BinaryOpSpan {
            lhs: expr_boolean(false),
            rhs: expr_integer(0),
            pos: lc(0, 0),
        });
        let unary_args = Box::from(UnaryOpSpan { expr: expr_integer(0), pos: lc(0, 0) });

        // These tests just make sure that we delegate to the `Value` operations for each
        // expression operator to essentially avoid duplicating all those tests.  We do this by
        // triggering errors and rely on the fact that their messages are different for every
        // operation.
        let mut syms = Symbols::default();
        assert_eq!(
            "Cannot AND FALSE and 0",
            format!("{}", block_on(Expr::And(binary_args.clone()).eval(&mut syms)).unwrap_err())
        );
        assert_eq!(
            "Cannot OR FALSE and 0",
            format!("{}", block_on(Expr::Or(binary_args.clone()).eval(&mut syms)).unwrap_err())
        );
        assert_eq!(
            "Cannot XOR FALSE and 0",
            format!("{}", block_on(Expr::Xor(binary_args).eval(&mut syms)).unwrap_err())
        );
        assert_eq!(
            "Cannot apply NOT to 0",
            format!("{}", block_on(Expr::Not(unary_args).eval(&mut syms)).unwrap_err())
        );
    }

    #[test]
    fn test_expr_relational_ops() {
        let binary_args = Box::from(BinaryOpSpan {
            lhs: expr_boolean(false),
            rhs: expr_integer(0),
            pos: lc(0, 0),
        });

        // These tests just make sure that we delegate to the `Value` operations for each
        // expression operator to essentially avoid duplicating all those tests.  We do this by
        // triggering errors and rely on the fact that their messages are different for every
        // operation.
        let mut syms = Symbols::default();
        assert_eq!(
            "Cannot compare FALSE and 0 with =",
            format!("{}", block_on(Expr::Equal(binary_args.clone()).eval(&mut syms)).unwrap_err())
        );
        assert_eq!(
            "Cannot compare FALSE and 0 with <>",
            format!(
                "{}",
                block_on(Expr::NotEqual(binary_args.clone()).eval(&mut syms)).unwrap_err()
            )
        );
        assert_eq!(
            "Cannot compare FALSE and 0 with <",
            format!("{}", block_on(Expr::Less(binary_args.clone()).eval(&mut syms)).unwrap_err())
        );
        assert_eq!(
            "Cannot compare FALSE and 0 with <=",
            format!(
                "{}",
                block_on(Expr::LessEqual(binary_args.clone()).eval(&mut syms)).unwrap_err()
            )
        );
        assert_eq!(
            "Cannot compare FALSE and 0 with >",
            format!(
                "{}",
                block_on(Expr::Greater(binary_args.clone()).eval(&mut syms)).unwrap_err()
            )
        );
        assert_eq!(
            "Cannot compare FALSE and 0 with >=",
            format!("{}", block_on(Expr::GreaterEqual(binary_args).eval(&mut syms)).unwrap_err())
        );
    }

    #[test]
    fn test_expr_arithmetic_ops() {
        let binary_args = Box::from(BinaryOpSpan {
            lhs: expr_boolean(false),
            rhs: expr_integer(0),
            pos: lc(0, 0),
        });
        let unary_args = Box::from(UnaryOpSpan { expr: expr_boolean(false), pos: lc(0, 0) });

        // These tests just make sure that we delegate to the `Value` operations for each
        // expression operator to essentially avoid duplicating all those tests.  We do this by
        // triggering errors and rely on the fact that their messages are different for every
        // operation.
        let mut syms = Symbols::default();
        assert_eq!(
            "Cannot add FALSE and 0",
            format!("{}", block_on(Expr::Add(binary_args.clone()).eval(&mut syms)).unwrap_err())
        );
        assert_eq!(
            "Cannot subtract 0 from FALSE",
            format!(
                "{}",
                block_on(Expr::Subtract(binary_args.clone()).eval(&mut syms)).unwrap_err()
            )
        );
        assert_eq!(
            "Cannot multiply FALSE by 0",
            format!(
                "{}",
                block_on(Expr::Multiply(binary_args.clone()).eval(&mut syms)).unwrap_err()
            )
        );
        assert_eq!(
            "Cannot divide FALSE by 0",
            format!("{}", block_on(Expr::Divide(binary_args).eval(&mut syms)).unwrap_err())
        );
        assert_eq!(
            "Cannot negate FALSE",
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
            "Cannot add 7 and TRUE",
            format!(
                "{}",
                block_on(
                    Expr::Equal(Box::from(BinaryOpSpan {
                        lhs: expr_integer(3),
                        rhs: Expr::Add(Box::from(BinaryOpSpan {
                            lhs: expr_integer(7),
                            rhs: expr_boolean(true),
                            pos: lc(0, 0),
                        })),
                        pos: lc(0, 0),
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
            "Incompatible types in X# reference",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("X", VarType::Double),
                        args: vec![expr_integer(1), expr_integer(3)],
                        pos: lc(0, 0),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "Cannot index array with 1 subscripts; need 2",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("X", VarType::Integer),
                        args: vec![expr_integer(1)],
                        pos: lc(0, 0),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "Subscript -1 cannot be negative",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("X", VarType::Integer),
                        args: vec![expr_integer(0), expr_integer(-1)],
                        pos: lc(0, 0),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "Subscript 10 exceeds limit of 2",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("X", VarType::Integer),
                        args: vec![expr_integer(10), expr_integer(0)],
                        pos: lc(0, 0),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "Unknown function or array y$",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("y".to_owned(), VarType::Text),
                        args: vec![],
                        pos: lc(0, 0),
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
            "Incompatible types in SUM$ reference",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("SUM".to_owned(), VarType::Text),
                        args: vec![],
                        pos: lc(0, 0),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "Unknown function or array SUMA$",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("SUMA".to_owned(), VarType::Text),
                        args: vec![],
                        pos: lc(0, 0),
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
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("TYPE_CHECK".to_owned(), VarType::Auto),
                        args: vec![],
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
                "Value returned by TYPE_CHECK is incompatible with its type definition",
                format!(
                    "{}",
                    block_on(
                        Expr::Call(FunctionCallSpan {
                            fref: VarRef::new("TYPE_CHECK".to_owned(), VarType::Auto),
                            args: vec![],
                            pos: lc(0, 0),
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
        let mut syms = SymbolsBuilder::default().add_function(ErrorFunction::new()).build();

        assert_eq!(
            "Syntax error in call to ERROR: Bad argument",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("ERROR".to_owned(), VarType::Auto),
                        args: vec![expr_text("argument")],
                        pos: lc(0, 0),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "Error in call to ERROR: Some eval error",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("ERROR".to_owned(), VarType::Auto),
                        args: vec![expr_text("eval")],
                        pos: lc(0, 0),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "Error in call to ERROR: Some internal error",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("ERROR".to_owned(), VarType::Auto),
                        args: vec![expr_text("internal")],
                        pos: lc(0, 0),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "Syntax error in call to ERROR: expected arg1$",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("ERROR".to_owned(), VarType::Auto),
                        args: vec![expr_text("syntax")],
                        pos: lc(0, 0),
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
            .add_command(ExitCommand::new())
            .build();

        assert_eq!(
            "SOMEVAR is not an array or a function",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("SOMEVAR".to_owned(), VarType::Auto),
                        args: vec![],
                        pos: lc(0, 0),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );

        assert_eq!(
            "EXIT is not an array or a function",
            format!(
                "{}",
                block_on(
                    Expr::Call(FunctionCallSpan {
                        fref: VarRef::new("EXIT".to_owned(), VarType::Auto),
                        args: vec![],
                        pos: lc(0, 0),
                    })
                    .eval(&mut syms)
                )
                .unwrap_err()
            )
        );
    }
}
