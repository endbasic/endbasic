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
use endbasic_core::ast::{ArgSep, ExprType, Value};
use endbasic_core::compiler::{
    ArgSepSyntax, RequiredRefSyntax, RequiredValueSyntax, SingularArgSyntax,
};
use endbasic_core::exec::{Machine, Scope};
use endbasic_core::syms::{
    Array, CallError, CallResult, Callable, CallableMetadata, CallableMetadataBuilder, Symbol,
    Symbols,
};
use std::rc::Rc;

/// Category description for all symbols provided by this module.
const CATEGORY: &str = "Array functions";

/// Extracts the array reference and the dimension number from the list of arguments passed to
/// either `LBOUND` or `UBOUND`.
#[allow(clippy::needless_lifetimes)]
fn parse_bound_args<'a>(
    mut scope: Scope<'_>,
    symbols: &'a Symbols,
) -> Result<(&'a Array, usize), CallError> {
    let (arrayref, arraypos) = scope.pop_varref_with_pos();

    let array = match symbols
        .get(&arrayref)
        .map_err(|e| CallError::ArgumentError(arraypos, format!("{}", e)))?
    {
        Some(Symbol::Array(array)) => array,
        _ => unreachable!(),
    };

    if scope.nargs() == 1 {
        let (i, pos) = scope.pop_integer_with_pos();

        if i < 0 {
            return Err(CallError::ArgumentError(pos, format!("Dimension {} must be positive", i)));
        }
        let i = i as usize;

        if i > array.dimensions().len() {
            return Err(CallError::ArgumentError(
                pos,
                format!(
                    "Array {} has only {} dimensions but asked for {}",
                    arrayref,
                    array.dimensions().len(),
                    i,
                ),
            ));
        }
        Ok((array, i))
    } else {
        debug_assert_eq!(0, scope.nargs());

        if array.dimensions().len() > 1 {
            return Err(CallError::ArgumentError(
                arraypos,
                "Requires a dimension for multidimensional arrays".to_owned(),
            ));
        }

        Ok((array, 1))
    }
}

/// The `LBOUND` function.
pub struct LboundFunction {
    metadata: CallableMetadata,
}

impl LboundFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("LBOUND")
                .with_return_type(ExprType::Integer)
                .with_syntax(&[
                    (
                        &[SingularArgSyntax::RequiredRef(
                            RequiredRefSyntax {
                                name: "array",
                                require_array: true,
                                define_undefined: false,
                            },
                            ArgSepSyntax::End,
                        )],
                        None,
                    ),
                    (
                        &[
                            SingularArgSyntax::RequiredRef(
                                RequiredRefSyntax {
                                    name: "array",
                                    require_array: true,
                                    define_undefined: false,
                                },
                                ArgSepSyntax::Exactly(ArgSep::Long),
                            ),
                            SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax { name: "dimension", vtype: ExprType::Integer },
                                ArgSepSyntax::End,
                            ),
                        ],
                        None,
                    ),
                ])
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
impl Callable for LboundFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, scope: Scope<'_>, machine: &mut Machine) -> CallResult {
        let (_array, _dim) = parse_bound_args(scope, machine.get_symbols())?;
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
            metadata: CallableMetadataBuilder::new("UBOUND")
                .with_return_type(ExprType::Integer)
                .with_syntax(&[
                    (
                        &[SingularArgSyntax::RequiredRef(
                            RequiredRefSyntax {
                                name: "array",
                                require_array: true,
                                define_undefined: false,
                            },
                            ArgSepSyntax::End,
                        )],
                        None,
                    ),
                    (
                        &[
                            SingularArgSyntax::RequiredRef(
                                RequiredRefSyntax {
                                    name: "array",
                                    require_array: true,
                                    define_undefined: false,
                                },
                                ArgSepSyntax::Exactly(ArgSep::Long),
                            ),
                            SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax { name: "dimension", vtype: ExprType::Integer },
                                ArgSepSyntax::End,
                            ),
                        ],
                        None,
                    ),
                ])
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
impl Callable for UboundFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, scope: Scope<'_>, machine: &mut Machine) -> CallResult {
        let (array, dim) = parse_bound_args(scope, machine.get_symbols())?;
        Ok(Value::Integer((array.dimensions()[dim - 1] - 1) as i32))
    }
}

/// Adds all symbols provided by this module to the given `machine`.
pub fn add_all(machine: &mut Machine) {
    machine.add_callable(LboundFunction::new());
    machine.add_callable(UboundFunction::new());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;

    /// Validates error handling of `LBOUND` and `UBOUND` as given in `func`.
    fn do_bound_errors_test(func: &str) {
        Tester::default()
            .run(&format!("DIM x(2): result = {}()", func))
            .expect_compilation_err(format!(
                "1:20: In call to {}: expected <array> | <array, dimension%>",
                func
            ))
            .check();

        Tester::default()
            .run(&format!("DIM x(2): result = {}(x, 1, 2)", func))
            .expect_compilation_err(format!(
                "1:20: In call to {}: expected <array> | <array, dimension%>",
                func
            ))
            .check();

        Tester::default()
            .run(&format!("DIM x(2): result = {}(x, -1)", func))
            .expect_err(format!("1:20: In call to {}: 1:30: Dimension -1 must be positive", func))
            .expect_array("x", ExprType::Integer, &[2], vec![])
            .check();

        Tester::default()
            .run(&format!("DIM x(2): result = {}(x, TRUE)", func))
            .expect_compilation_err(format!(
                "1:20: In call to {}: 1:30: BOOLEAN is not a number",
                func
            ))
            .check();

        Tester::default()
            .run(&format!("i = 0: result = {}(i)", func))
            .expect_compilation_err(format!(
                "1:17: In call to {}: 1:24: i is not an array reference",
                func
            ))
            .check();

        Tester::default()
            .run(&format!("result = {}(3)", func))
            .expect_compilation_err(format!(
                "1:10: In call to {}: 1:17: Requires an array reference, not a value",
                func
            ))
            .check();

        Tester::default()
            .run(&format!("i = 0: result = {}(i)", func))
            .expect_compilation_err(format!(
                "1:17: In call to {}: 1:24: i is not an array reference",
                func
            ))
            .check();

        Tester::default()
            .run(&format!("DIM i(3) AS BOOLEAN: result = {}(i$)", func))
            .expect_compilation_err(format!(
                "1:31: In call to {}: 1:38: Incompatible type annotation in i$ reference",
                func
            ))
            .check();

        Tester::default()
            .run(&format!("result = {}(x)", func))
            .expect_compilation_err(format!("1:10: In call to {}: 1:17: Undefined array x", func))
            .check();

        Tester::default()
            .run(&format!("DIM x(2, 3, 4): result = {}(x)", func))
            .expect_err(format!(
                "1:26: In call to {}: 1:33: Requires a dimension for multidimensional arrays",
                func
            ))
            .expect_array("x", ExprType::Integer, &[2, 3, 4], vec![])
            .check();

        Tester::default()
            .run(&format!("DIM x(2, 3, 4): result = {}(x, 5)", func))
            .expect_err(format!(
                "1:26: In call to {}: 1:36: Array x has only 3 dimensions but asked for 5",
                func
            ))
            .expect_array("x", ExprType::Integer, &[2, 3, 4], vec![])
            .check();
    }

    #[test]
    fn test_lbound_ok() {
        Tester::default()
            .run("DIM x(10): result = LBOUND(x)")
            .expect_var("result", 0i32)
            .expect_array("x", ExprType::Integer, &[10], vec![])
            .check();

        Tester::default()
            .run("DIM x(10, 20): result = LBOUND(x, 1)")
            .expect_var("result", 0i32)
            .expect_array("x", ExprType::Integer, &[10, 20], vec![])
            .check();

        Tester::default()
            .run("DIM x(10, 20): result = LBOUND(x, 2.1)")
            .expect_var("result", 0i32)
            .expect_array("x", ExprType::Integer, &[10, 20], vec![])
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
            .expect_array("x", ExprType::Integer, &[10], vec![])
            .check();

        Tester::default()
            .run("DIM x(10, 20): result = UBOUND(x, 1)")
            .expect_var("result", 9i32)
            .expect_array("x", ExprType::Integer, &[10, 20], vec![])
            .check();

        Tester::default()
            .run("DIM x(10, 20): result = UBOUND(x, 2.1)")
            .expect_var("result", 19i32)
            .expect_array("x", ExprType::Integer, &[10, 20], vec![])
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
                ExprType::Integer,
                vec![0i32.into(), 2i32.into(), 4i32.into(), 6i32.into(), 8i32.into()],
            )
            .check();
    }
}
