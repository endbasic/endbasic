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
use endbasic_core::bytecode::Instruction;
use endbasic_core::compiler::{
    compile_arg, CallableArgsCompiler, ExprType, SymbolPrototype, SymbolsTable,
};
use endbasic_core::exec::{Machine, Scope};
use endbasic_core::syms::{
    Array, CallError, CallResult, Callable, CallableMetadata, CallableMetadataBuilder, Symbol,
    SymbolKey, Symbols,
};
use endbasic_core::LineCol;
use std::rc::Rc;

/// Category description for all symbols provided by this module.
const CATEGORY: &str = "Array functions";

/// An arguments compiler for the `LBOUND` and `UBOUND` functions.
#[derive(Debug, Default)]
struct BoundsArgsCompiler {}

impl CallableArgsCompiler for BoundsArgsCompiler {
    fn compile_simple(
        &self,
        instrs: &mut Vec<Instruction>,
        symtable: &SymbolsTable,
        _pos: LineCol,
        args: Vec<Expr>,
    ) -> Result<usize, CallError> {
        let nargs = args.len();
        if !(1..=2).contains(&nargs) {
            return Err(CallError::SyntaxError);
        }

        let mut iter = args.into_iter().rev();

        if nargs == 2 {
            compile_arg(instrs, symtable, &mut iter, ExprType::Integer)?;
        }

        let expr = iter.next().unwrap();
        match expr {
            Expr::Symbol(span) => {
                let key = SymbolKey::from(span.vref.name());
                match symtable.get(&key) {
                    Some(SymbolPrototype::Array(vtype, dims)) => {
                        if !span.vref.accepts((*vtype).into()) {
                            return Err(CallError::ArgumentError(
                                span.pos,
                                format!("Incompatible type annotation in {} reference", span.vref),
                            ));
                        }

                        if *dims > 1 && nargs == 1 {
                            return Err(CallError::ArgumentError(
                                span.pos,
                                "Requires a dimension for multidimensional arrays".to_owned(),
                            ));
                        }

                        instrs.push(Instruction::LoadRef(span.vref, span.pos));
                    }
                    None => {
                        return Err(CallError::ArgumentError(
                            span.pos,
                            format!("Undefined variable {}", span.vref.name()),
                        ))
                    }
                    _ => {
                        // TODO(jmmv): For consistency with other argument compilation, this should
                        // check type annotations first, but doing so here is not very interesting.
                        // Keep this in mind when trying to unify all arguments compilers.
                        return Err(CallError::ArgumentError(
                            span.pos,
                            format!("{} must be an array reference", span.vref),
                        ));
                    }
                }
            }
            _ => {
                return Err(CallError::ArgumentError(
                    expr.start_pos(),
                    "First argument must be an array reference".to_owned(),
                ))
            }
        }

        debug_assert!(iter.next().is_none());

        Ok(nargs)
    }
}

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
            metadata: CallableMetadataBuilder::new("LBOUND", VarType::Integer)
                .with_syntax("array[, dimension%]")
                .with_args_compiler(BoundsArgsCompiler::default())
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
            metadata: CallableMetadataBuilder::new("UBOUND", VarType::Integer)
                .with_syntax("array[, dimension%]")
                .with_args_compiler(BoundsArgsCompiler::default())
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
    use crate::testutils::*;
    use endbasic_core::ast::VarType;

    /// Validates error handling of `LBOUND` and `UBOUND` as given in `func`.
    fn do_bound_errors_test(func: &str) {
        Tester::default()
            .run(&format!("DIM x(2): result = {}()", func))
            .expect_compilation_err(format!(
                "1:20: In call to {}: expected array[, dimension%]",
                func
            ))
            .check();

        Tester::default()
            .run(&format!("DIM x(2): result = {}(x, 1, 2)", func))
            .expect_compilation_err(format!(
                "1:20: In call to {}: expected array[, dimension%]",
                func
            ))
            .check();

        Tester::default()
            .run(&format!("DIM x(2): result = {}(x, -1)", func))
            .expect_err(format!("1:20: In call to {}: 1:30: Dimension -1 must be positive", func))
            .expect_array("x", VarType::Integer, &[2], vec![])
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
                "1:17: In call to {}: 1:24: i must be an array reference",
                func
            ))
            .check();

        Tester::default()
            .run(&format!("result = {}(3)", func))
            .expect_compilation_err(format!(
                "1:10: In call to {}: 1:17: First argument must be an array reference",
                func
            ))
            .check();

        Tester::default()
            .run(&format!("i = 0: result = {}(i$)", func))
            .expect_compilation_err(format!(
                "1:17: In call to {}: 1:24: i$ must be an array reference",
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
            .expect_compilation_err(format!(
                "1:10: In call to {}: 1:17: Undefined variable x",
                func
            ))
            .check();

        Tester::default()
            .run(&format!("DIM x(2, 3, 4): result = {}(x)", func))
            .expect_compilation_err(format!(
                "1:26: In call to {}: 1:33: Requires a dimension for multidimensional arrays",
                func
            ))
            .check();

        Tester::default()
            .run(&format!("DIM x(2, 3, 4): result = {}(x, 5)", func))
            .expect_err(format!(
                "1:26: In call to {}: 1:36: Array x has only 3 dimensions but asked for 5",
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
            .run("DIM x(10, 20): result = LBOUND(x, 2.1)")
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
            .run("DIM x(10, 20): result = UBOUND(x, 2.1)")
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
