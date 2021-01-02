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

//! String functions for EndBASIC.

use crate::ast::{Value, VarType};
use crate::eval::{
    CallableMetadata, CallableMetadataBuilder, Function, FunctionError, FunctionResult,
};
use crate::exec::MachineBuilder;
use std::cmp::min;
use std::rc::Rc;

/// Category string for all functions provided by this module.
const CATEGORY: &str = "String manipulation";

/// The `LEFT` function.
pub struct LeftFunction {
    metadata: CallableMetadata,
}

impl LeftFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("LEFT", VarType::Text)
                .with_syntax("expr$, n%")
                .with_category(CATEGORY)
                .with_description(
                    "Returns a given number of characters from the left side of a string.
If n% is 0, returns an empty string.
If n% is greater than or equal to the number of characters in expr$, returns expr$.",
                )
                .build(),
        })
    }
}

impl Function for LeftFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    fn exec(&self, args: Vec<Value>) -> FunctionResult {
        match args.as_slice() {
            [Value::Text(s), Value::Integer(n)] => {
                if n < &0 {
                    Err(FunctionError::ArgumentError("n% cannot be negative".to_owned()))
                } else {
                    let n = min(s.len(), *n as usize);
                    Ok(Value::Text(s[..n].to_owned()))
                }
            }
            _ => Err(FunctionError::SyntaxError),
        }
    }
}

/// The `LEN` function.
pub struct LenFunction {
    metadata: CallableMetadata,
}

impl LenFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("LEN", VarType::Integer)
                .with_syntax("expr$")
                .with_category(CATEGORY)
                .with_description("Returns the length of the string in expr$.")
                .build(),
        })
    }
}

impl Function for LenFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    fn exec(&self, args: Vec<Value>) -> FunctionResult {
        match args.as_slice() {
            [Value::Text(s)] => {
                if s.len() > i32::MAX as usize {
                    Err(FunctionError::InternalError("String too long".to_owned()))
                } else {
                    Ok(Value::Integer(s.len() as i32))
                }
            }
            _ => Err(FunctionError::SyntaxError),
        }
    }
}

/// The `LTRIM` function.
pub struct LtrimFunction {
    metadata: CallableMetadata,
}

impl LtrimFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("LTRIM", VarType::Text)
                .with_syntax("expr$")
                .with_category(CATEGORY)
                .with_description("Returns a copy of a string with leading whitespace removed.")
                .build(),
        })
    }
}

impl Function for LtrimFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    fn exec(&self, args: Vec<Value>) -> FunctionResult {
        match args.as_slice() {
            [Value::Text(s)] => Ok(Value::Text(s.trim_start().to_owned())),
            _ => Err(FunctionError::SyntaxError),
        }
    }
}

/// The `MID` function.
pub struct MidFunction {
    metadata: CallableMetadata,
}

impl MidFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("MID", VarType::Text)
                .with_syntax("expr$, start%[, length%]")
                .with_category(CATEGORY)
                .with_description(
                    "Returns a portion of a string.
start% indicates the starting position of the substring to extract and it is 1-indexed.
length% indicates the number of characters to extract and, if not specified, defaults to extracting
until the end of the string.",
                )
                .build(),
        })
    }
}

impl Function for MidFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    fn exec(&self, args: Vec<Value>) -> FunctionResult {
        match args.as_slice() {
            [Value::Text(s), Value::Integer(start), Value::Integer(length)] => {
                if *start < 0 {
                    Err(FunctionError::ArgumentError("start% cannot be negative".to_owned()))
                } else if *length < 0 {
                    Err(FunctionError::ArgumentError("length% cannot be negative".to_owned()))
                } else {
                    let start = min(s.len(), *start as usize);
                    let end = min(start + (*length as usize), s.len());
                    Ok(Value::Text(s[start..end].to_owned()))
                }
            }
            _ => Err(FunctionError::SyntaxError),
        }
    }
}

/// The `RIGHT` function.
pub struct RightFunction {
    metadata: CallableMetadata,
}

impl RightFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("RIGHT", VarType::Text)
                .with_syntax("expr$, n%")
                .with_category(CATEGORY)
                .with_description(
                    "Returns a given number of characters from the right side of a string.
If n% is 0, returns an empty string.
If n% is greater than or equal to the number of characters in expr$, returns expr$.",
                )
                .build(),
        })
    }
}

impl Function for RightFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    fn exec(&self, args: Vec<Value>) -> FunctionResult {
        match args.as_slice() {
            [Value::Text(s), Value::Integer(n)] => {
                if n < &0 {
                    Err(FunctionError::ArgumentError("n% cannot be negative".to_owned()))
                } else {
                    let n = min(s.len(), *n as usize);
                    Ok(Value::Text(s[s.len() - n..].to_owned()))
                }
            }
            _ => Err(FunctionError::SyntaxError),
        }
    }
}

/// The `RTRIM` function.
pub struct RtrimFunction {
    metadata: CallableMetadata,
}

impl RtrimFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("RTRIM", VarType::Text)
                .with_syntax("expr$")
                .with_category(CATEGORY)
                .with_description("Returns a copy of a string with trailing whitespace removed.")
                .build(),
        })
    }
}

impl Function for RtrimFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    fn exec(&self, args: Vec<Value>) -> FunctionResult {
        match args.as_slice() {
            [Value::Text(s)] => Ok(Value::Text(s.trim_end().to_owned())),
            _ => Err(FunctionError::SyntaxError),
        }
    }
}

/// Adds all symbols provided by this module to the given machine `builder`.
pub fn add_all(builder: MachineBuilder) -> MachineBuilder {
    builder
        .add_function(LeftFunction::new())
        .add_function(LenFunction::new())
        .add_function(LtrimFunction::new())
        .add_function(MidFunction::new())
        .add_function(RightFunction::new())
        .add_function(RtrimFunction::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::VarRef;
    use crate::exec::MachineBuilder;
    use futures_lite::future::block_on;

    fn check_ok(exp_value: Value, expr: &str) {
        let mut machine = add_all(MachineBuilder::default()).build();
        block_on(machine.exec(&mut format!("result = {}", expr).as_bytes())).unwrap();
        assert_eq!(
            &exp_value,
            machine.get_vars().get(&VarRef::new("result", VarType::Auto)).unwrap()
        )
    }

    fn check_error(exp_error: &str, expr: &str) {
        let mut machine = add_all(MachineBuilder::default()).build();
        assert_eq!(
            exp_error,
            format!(
                "{}",
                block_on(machine.exec(&mut format!("result = {}", expr).as_bytes())).unwrap_err()
            )
        );
    }

    #[test]
    fn test_left() {
        check_ok(Value::Text("".to_owned()), "LEFT(\"\", 0)");
        check_ok(Value::Text("abc".to_owned()), "LEFT(\"abcdef\", 3)");
        check_ok(Value::Text("abcdef".to_owned()), "LEFT(\"abcdef\", 6)");
        check_ok(Value::Text("abcdef".to_owned()), "LEFT(\"abcdef\", 10)");

        check_error("Syntax error in call to LEFT: expected expr$, n%", "LEFT()");
        check_error("Syntax error in call to LEFT: expected expr$, n%", "LEFT(\"\", 1, 2)");
        check_error("Syntax error in call to LEFT: expected expr$, n%", "LEFT(1, 2)");
        check_error("Syntax error in call to LEFT: expected expr$, n%", "LEFT(\"\", \"\")");
        check_error("Syntax error in call to LEFT: n% cannot be negative", "LEFT(\"abcdef\", -5)");
    }

    #[test]
    fn test_len() {
        check_ok(Value::Integer(0), "LEN(\"\")");
        check_ok(Value::Integer(1), "LEN(\" \")");
        check_ok(Value::Integer(5), "LEN(\"abcde\")");

        check_error("Syntax error in call to LEN: expected expr$", "LEN()");
        check_error("Syntax error in call to LEN: expected expr$", "LEN(3)");
        check_error("Syntax error in call to LEN: expected expr$", "LEN(\" \", 1)");
    }

    #[test]
    fn test_ltrim() {
        check_ok(Value::Text("".to_owned()), "LTRIM(\"\")");
        check_ok(Value::Text("".to_owned()), "LTRIM(\"  \")");
        check_ok(Value::Text("".to_owned()), "LTRIM(\"\t\t\")");
        check_ok(Value::Text("foo \t ".to_owned()), "LTRIM(\" \t foo \t \")");

        check_error("Syntax error in call to LTRIM: expected expr$", "LTRIM()");
        check_error("Syntax error in call to LTRIM: expected expr$", "LTRIM(3)");
        check_error("Syntax error in call to LTRIM: expected expr$", "LTRIM(\" \", 1)");
    }

    #[test]
    fn test_mid() {
        check_ok(Value::Text("".to_owned()), "MID(\"\", 0, 0)");
        check_ok(Value::Text("".to_owned()), "MID(\"basic\", 0, 0)");
        check_ok(Value::Text("".to_owned()), "MID(\"basic\", 1, 0)");
        check_ok(Value::Text("a".to_owned()), "MID(\"basic\", 1, 1)");
        check_ok(Value::Text("as".to_owned()), "MID(\"basic\", 1, 2)");
        check_ok(Value::Text("asic".to_owned()), "MID(\"basic\", 1, 4)");
        check_ok(Value::Text("asic".to_owned()), "MID(\"basic\", 1, 10)");
        check_ok(Value::Text("".to_owned()), "MID(\"basic\", 100, 10)");

        check_error("Syntax error in call to MID: expected expr$, start%[, length%]", "MID()");
        check_error("Syntax error in call to MID: expected expr$, start%[, length%]", "MID(3)");
        check_error(
            "Syntax error in call to MID: expected expr$, start%[, length%]",
            "MID(\" \", 1, 1, 10)",
        );
        check_error(
            "Syntax error in call to MID: expected expr$, start%[, length%]",
            "MID(\" \", \"1\", \"2\")",
        );
        check_error(
            "Syntax error in call to MID: start% cannot be negative",
            "MID(\"abcdef\", -5, 10)",
        );
        check_error(
            "Syntax error in call to MID: length% cannot be negative",
            "MID(\"abcdef\", 3, -5)",
        );
    }

    #[test]
    fn test_right() {
        check_ok(Value::Text("".to_owned()), "RIGHT(\"\", 0)");
        check_ok(Value::Text("def".to_owned()), "RIGHT(\"abcdef\", 3)");
        check_ok(Value::Text("abcdef".to_owned()), "RIGHT(\"abcdef\", 6)");
        check_ok(Value::Text("abcdef".to_owned()), "RIGHT(\"abcdef\", 10)");

        check_error("Syntax error in call to RIGHT: expected expr$, n%", "RIGHT()");
        check_error("Syntax error in call to RIGHT: expected expr$, n%", "RIGHT(\"\", 1, 2)");
        check_error("Syntax error in call to RIGHT: expected expr$, n%", "RIGHT(1, 2)");
        check_error("Syntax error in call to RIGHT: expected expr$, n%", "RIGHT(\"\", \"\")");
        check_error(
            "Syntax error in call to RIGHT: n% cannot be negative",
            "RIGHT(\"abcdef\", -5)",
        );
    }

    #[test]
    fn test_rtrim() {
        check_ok(Value::Text("".to_owned()), "RTRIM(\"\")");
        check_ok(Value::Text("".to_owned()), "RTRIM(\"  \")");
        check_ok(Value::Text("".to_owned()), "RTRIM(\"\t\t\")");
        check_ok(Value::Text(" \t foo".to_owned()), "RTRIM(\" \t foo \t \")");

        check_error("Syntax error in call to RTRIM: expected expr$", "RTRIM()");
        check_error("Syntax error in call to RTRIM: expected expr$", "RTRIM(3)");
        check_error("Syntax error in call to RTRIM: expected expr$", "RTRIM(\" \", 1)");
    }
}
