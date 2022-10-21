// EndBASIC
// Copyright 2021 Julio Merino
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

//! Array-related functions for EndBASIC.

use async_trait::async_trait;
use endbasic_core::ast::{Expr, Value, VarType};
use endbasic_core::exec::Machine;
use endbasic_core::syms::{
    Array, CallError, CallableMetadata, CallableMetadataBuilder, Function, FunctionResult, Symbol,
    Symbols,
};
use std::rc::Rc;

/// Category description for all symbols provided by this module.
const CATEGORY: &str = "Array functions";

/// Extracts the array reference and the dimension number from the list of arguments passed to
/// either `LBOUND` or `UBOUND`.
#[allow(clippy::needless_lifetimes)]
async fn parse_bound_args<'a>(
    args: &[Expr],
    symbols: &'a mut Symbols,
) -> Result<(&'a Array, usize), CallError> {
    let mut iter = args.iter();

    let arrayref = match iter.next() {
        Some(Expr::Symbol(span)) => &span.vref,
        _ => return Err(CallError::ArgumentError("Takes one or two arguments".to_owned())),
    };

    let dim = match iter.next() {
        Some(expr) => match expr.eval(symbols).await? {
            Value::Integer(i) => {
                if i < 0 {
                    return Err(CallError::ArgumentError(format!(
                        "Dimension {} must be positive",
                        i
                    )));
                }
                Some(i as usize)
            }
            _ => return Err(CallError::ArgumentError("Dimension must be an integer".to_owned())),
        },
        None => None,
    };

    if iter.next().is_some() {
        return Err(CallError::ArgumentError("Takes one or two arguments".to_owned()));
    }

    let array = match symbols.get(arrayref)? {
        Some(Symbol::Array(array)) => array,
        Some(_) => {
            return Err(CallError::ArgumentError(format!(
                "{} must be an array reference",
                arrayref
            )))
        }
        _ => return Err(CallError::ArgumentError(format!("{} is not defined", arrayref))),
    };

    match dim {
        Some(dim) => {
            if dim > array.dimensions().len() {
                return Err(CallError::ArgumentError(format!(
                    "Array {} has only {} dimensions but asked for {}",
                    arrayref,
                    array.dimensions().len(),
                    dim
                )));
            }
        }
        None => {
            if array.dimensions().len() != 1 {
                return Err(CallError::ArgumentError(
                    "Requires a dimension for multidimensional arrays".to_owned(),
                ));
            }
        }
    }

    Ok((array, dim.unwrap_or(1)))
}

/// The `LBOUND` function.
pub struct LboundFunction {
    metadata: CallableMetadata,
}

impl LboundFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("LBOUND", VarType::Integer)
                .with_syntax("array[, dimension%]")
                .with_category(CATEGORY)
                .with_description(
                    "Returns the lower bound for the given dimension of the array.
The lower bound is the smallest available subscript that can be provided to array indexing \
operations.
For one-dimensional arrays, the dimension% is optional.  For multi-dimensional arrays, the \
dimension% is a 1-indexed integer.",
                )
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for LboundFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[Expr], symbols: &mut Symbols) -> FunctionResult {
        let (_array, _dim) = parse_bound_args(args, symbols).await?;
        Ok(Value::Integer(0))
    }
}

/// The `UBOUND` function.
pub struct UboundFunction {
    metadata: CallableMetadata,
}

impl UboundFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("UBOUND", VarType::Integer)
                .with_syntax("array[, dimension%]")
                .with_category(CATEGORY)
                .with_description(
                    "Returns the upper bound for the given dimension of the array.
The upper bound is the largest available subscript that can be provided to array indexing \
operations.
For one-dimensional arrays, the dimension% is optional.  For multi-dimensional arrays, the \
dimension% is a 1-indexed integer.",
                )
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for UboundFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[Expr], symbols: &mut Symbols) -> FunctionResult {
        let (array, dim) = parse_bound_args(args, symbols).await?;
        Ok(Value::Integer((array.dimensions()[dim - 1] - 1) as i32))
    }
}

/// Adds all symbols provided by this module to the given `machine`.
pub fn add_all(machine: &mut Machine) {
    machine.add_function(LboundFunction::new());
    machine.add_function(UboundFunction::new());
}

#[cfg(test)]
mod tests {
    use crate::testutils::*;
    use endbasic_core::ast::{Value, VarType};

    /// Validates error handling of `LBOUND` and `UBOUND` as given in `func`.
    fn do_bound_errors_test(func: &str) {
        Tester::default()
            .run(&format!("DIM x(2): result = {}()", func))
            .expect_err(format!("Syntax error in call to {}: Takes one or two arguments", func))
            .expect_array("x", VarType::Integer, &[2], vec![])
            .check();

        Tester::default()
            .run(&format!("DIM x(2): result = {}(x, 1, 2)", func))
            .expect_err(format!("Syntax error in call to {}: Takes one or two arguments", func))
            .expect_array("x", VarType::Integer, &[2], vec![])
            .check();

        Tester::default()
            .run(&format!("DIM x(2): result = {}(x, -1)", func))
            .expect_err(format!("Syntax error in call to {}: Dimension -1 must be positive", func))
            .expect_array("x", VarType::Integer, &[2], vec![])
            .check();

        Tester::default()
            .run(&format!("DIM x(2): result = {}(x, 1.0)", func))
            .expect_err(format!("Syntax error in call to {}: Dimension must be an integer", func))
            .expect_array("x", VarType::Integer, &[2], vec![])
            .check();

        Tester::default()
            .run(&format!("i = 0: result = {}(i)", func))
            .expect_err(format!("Syntax error in call to {}: i must be an array reference", func))
            .expect_var("i", Value::Integer(0))
            .check();

        Tester::default()
            .run(&format!("i = 0: result = {}(i$)", func))
            .expect_err(format!("Error in call to {}: Incompatible types in i$ reference", func))
            .expect_var("i", Value::Integer(0))
            .check();

        Tester::default()
            .run(&format!("result = {}(x)", func))
            .expect_err(format!("Syntax error in call to {}: x is not defined", func))
            .check();

        Tester::default()
            .run(&format!("DIM x(2, 3, 4): result = {}(x)", func))
            .expect_err(format!(
                "Syntax error in call to {}: Requires a dimension for multidimensional arrays",
                func
            ))
            .expect_array("x", VarType::Integer, &[2, 3, 4], vec![])
            .check();

        Tester::default()
            .run(&format!("DIM x(2, 3, 4): result = {}(x, 5)", func))
            .expect_err(format!(
                "Syntax error in call to {}: Array x has only 3 dimensions but asked for 5",
                func
            ))
            .expect_array("x", VarType::Integer, &[2, 3, 4], vec![])
            .check();
    }

    #[test]
    fn test_lbound_ok() {
        Tester::default()
            .run("DIM x(10): result = LBOUND(x)")
            .expect_var("result", 0i32)
            .expect_array("x", VarType::Integer, &[10], vec![])
            .check();

        Tester::default()
            .run("DIM x(10, 20): result = LBOUND(x, 1)")
            .expect_var("result", 0i32)
            .expect_array("x", VarType::Integer, &[10, 20], vec![])
            .check();

        Tester::default()
            .run("DIM x(10, 20): result = LBOUND(x, 2)")
            .expect_var("result", 0i32)
            .expect_array("x", VarType::Integer, &[10, 20], vec![])
            .check();
    }

    #[test]
    fn test_lbound_errors() {
        do_bound_errors_test("LBOUND");
    }

    #[test]
    fn test_ubound_ok() {
        Tester::default()
            .run("DIM x(10): result = UBOUND(x)")
            .expect_var("result", 9i32)
            .expect_array("x", VarType::Integer, &[10], vec![])
            .check();

        Tester::default()
            .run("DIM x(10, 20): result = UBOUND(x, 1)")
            .expect_var("result", 9i32)
            .expect_array("x", VarType::Integer, &[10, 20], vec![])
            .check();

        Tester::default()
            .run("DIM x(10, 20): result = UBOUND(x, 2)")
            .expect_var("result", 19i32)
            .expect_array("x", VarType::Integer, &[10, 20], vec![])
            .check();
    }

    #[test]
    fn test_ubound_errors() {
        do_bound_errors_test("UBOUND");
    }

    #[test]
    fn test_bound_integration() {
        Tester::default()
            .run("DIM x(5): FOR i = LBOUND(x) TO UBOUND(x): x(i) = i * 2: NEXT")
            .expect_var("i", 5i32)
            .expect_array_simple(
                "x",
                VarType::Integer,
                vec![0i32.into(), 2i32.into(), 4i32.into(), 6i32.into(), 8i32.into()],
            )
            .check();
    }
}
