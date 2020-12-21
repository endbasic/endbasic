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

//! Numerical functions for EndBASIC.

use crate::ast::{Value, VarType};
use crate::eval::{
    BuiltinFunction, CallableMetadata, CallableMetadataBuilder, FunctionError, FunctionResult,
};
use std::rc::Rc;

/// Category string for all functions provided by this module.
const CATEGORY: &str = "Numerical manipulation";

/// The `DTOI` function.
pub struct DtoiFunction {
    metadata: CallableMetadata,
}

impl DtoiFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("DTOI", VarType::Integer)
                .with_syntax("expr#")
                .with_category(CATEGORY)
                .with_description(
                    "Rounds the given double to the closest integer.
If the value is too small or too big to fit in the integer's range, returns the smallest or \
biggest possible integer that fits, respectively.",
                )
                .build(),
        })
    }
}

impl BuiltinFunction for DtoiFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    fn exec(&self, args: Vec<Value>) -> FunctionResult {
        match args.as_slice() {
            [Value::Double(n)] => Ok(Value::Integer(*n as i32)),
            _ => Err(FunctionError::SyntaxError),
        }
    }
}

/// The `ITOD` function.
pub struct ItodFunction {
    metadata: CallableMetadata,
}

impl ItodFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("ITOD", VarType::Double)
                .with_syntax("expr%")
                .with_category(CATEGORY)
                .with_description("Converts the given integer to a double.")
                .build(),
        })
    }
}

impl BuiltinFunction for ItodFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    fn exec(&self, args: Vec<Value>) -> FunctionResult {
        match args.as_slice() {
            [Value::Integer(n)] => Ok(Value::Double(*n as f64)),
            _ => Err(FunctionError::SyntaxError),
        }
    }
}

/// Instantiates all functions provided by this module.
pub fn all_functions() -> Vec<Rc<dyn BuiltinFunction>> {
    vec![DtoiFunction::new(), ItodFunction::new()]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::VarRef;
    use crate::exec::MachineBuilder;
    use futures_lite::future::block_on;

    fn check_ok(exp_value: Value, expr: &str) {
        let mut machine = MachineBuilder::default().add_functions(all_functions()).build();
        block_on(machine.exec(&mut format!("result = {}", expr).as_bytes())).unwrap();
        assert_eq!(
            &exp_value,
            machine.get_vars().get(&VarRef::new("result", VarType::Auto)).unwrap()
        )
    }

    fn check_error(exp_error: &str, expr: &str) {
        let mut machine = MachineBuilder::default().add_functions(all_functions()).build();
        assert_eq!(
            exp_error,
            format!(
                "{}",
                block_on(machine.exec(&mut format!("result = {}", expr).as_bytes())).unwrap_err()
            )
        );
    }

    #[test]
    fn test_dtoi() {
        check_ok(Value::Integer(0), "DTOI( 0.1)");
        check_ok(Value::Integer(0), "DTOI(-0.1)");
        check_ok(Value::Integer(0), "DTOI( 0.9)");
        check_ok(Value::Integer(0), "DTOI(-0.9)");

        check_ok(Value::Integer(100), "DTOI( 100.1)");
        check_ok(Value::Integer(-100), "DTOI(-100.1)");
        check_ok(Value::Integer(100), "DTOI( 100.9)");
        check_ok(Value::Integer(-100), "DTOI(-100.9)");

        check_ok(Value::Integer(i32::MAX), "DTOI(12345678901234567890.0)");
        check_ok(Value::Integer(i32::MIN), "DTOI(-12345678901234567890.0)");

        check_error("Syntax error in call to DTOI: expected expr#", "DTOI()");
        check_error("Syntax error in call to DTOI: expected expr#", "DTOI(3)");
        check_error("Syntax error in call to DTOI: expected expr#", "DTOI(3.0, 4)");
    }

    #[test]
    fn test_itod() {
        check_ok(Value::Double(0.0), "ITOD(0)");
        check_ok(Value::Double(10.0), "ITOD(10)");
        check_ok(Value::Double(-10.0), "ITOD(-10)");

        check_ok(Value::Double(i32::MAX as f64), &format!("ITOD({})", i32::MAX));
        // TODO(jmmv): Due to limitations in the lexer/parser, we cannot represent the minimum
        // value of an i32 in the code as a literal.
        check_ok(Value::Double(i32::MIN as f64), &format!("ITOD({} - 1)", i32::MIN + 1));

        check_error("Syntax error in call to ITOD: expected expr%", "ITOD()");
        check_error("Syntax error in call to ITOD: expected expr%", "ITOD(3.0)");
        check_error("Syntax error in call to ITOD: expected expr%", "ITOD(3, 4)");
    }
}
