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

use endbasic_core::ast::{Value, VarType};
use endbasic_core::exec::Machine;
use endbasic_core::syms::{
    CallError, CallableMetadata, CallableMetadataBuilder, Function, FunctionResult, Symbols,
};
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

    fn exec(&self, args: Vec<Value>, _symbols: &mut Symbols) -> FunctionResult {
        match args.as_slice() {
            [Value::Text(s), Value::Integer(n)] => {
                if n < &0 {
                    Err(CallError::ArgumentError("n% cannot be negative".to_owned()))
                } else {
                    let n = min(s.len(), *n as usize);
                    Ok(Value::Text(s[..n].to_owned()))
                }
            }
            _ => Err(CallError::SyntaxError),
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

    fn exec(&self, args: Vec<Value>, _symbols: &mut Symbols) -> FunctionResult {
        match args.as_slice() {
            [Value::Text(s)] => {
                if s.len() > std::i32::MAX as usize {
                    Err(CallError::InternalError("String too long".to_owned()))
                } else {
                    Ok(Value::Integer(s.len() as i32))
                }
            }
            _ => Err(CallError::SyntaxError),
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

    fn exec(&self, args: Vec<Value>, _symbols: &mut Symbols) -> FunctionResult {
        match args.as_slice() {
            [Value::Text(s)] => Ok(Value::Text(s.trim_start().to_owned())),
            _ => Err(CallError::SyntaxError),
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

    fn exec(&self, args: Vec<Value>, _symbols: &mut Symbols) -> FunctionResult {
        match args.as_slice() {
            [Value::Text(s), Value::Integer(start), Value::Integer(length)] => {
                if *start < 0 {
                    Err(CallError::ArgumentError("start% cannot be negative".to_owned()))
                } else if *length < 0 {
                    Err(CallError::ArgumentError("length% cannot be negative".to_owned()))
                } else {
                    let start = min(s.len(), *start as usize);
                    let end = min(start + (*length as usize), s.len());
                    Ok(Value::Text(s[start..end].to_owned()))
                }
            }
            _ => Err(CallError::SyntaxError),
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

    fn exec(&self, args: Vec<Value>, _symbols: &mut Symbols) -> FunctionResult {
        match args.as_slice() {
            [Value::Text(s), Value::Integer(n)] => {
                if n < &0 {
                    Err(CallError::ArgumentError("n% cannot be negative".to_owned()))
                } else {
                    let n = min(s.len(), *n as usize);
                    Ok(Value::Text(s[s.len() - n..].to_owned()))
                }
            }
            _ => Err(CallError::SyntaxError),
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

    fn exec(&self, args: Vec<Value>, _symbols: &mut Symbols) -> FunctionResult {
        match args.as_slice() {
            [Value::Text(s)] => Ok(Value::Text(s.trim_end().to_owned())),
            _ => Err(CallError::SyntaxError),
        }
    }
}

/// Adds all symbols provided by this module to the given `machine`.
pub fn add_all(machine: &mut Machine) {
    machine.add_function(LeftFunction::new());
    machine.add_function(LenFunction::new());
    machine.add_function(LtrimFunction::new());
    machine.add_function(MidFunction::new());
    machine.add_function(RightFunction::new());
    machine.add_function(RtrimFunction::new());
}

#[cfg(test)]
mod tests {
    use crate::testutils::*;

    #[test]
    fn test_left() {
        check_expr_ok("", r#"LEFT("", 0)"#);
        check_expr_ok("abc", r#"LEFT("abcdef", 3)"#);
        check_expr_ok("abcdef", r#"LEFT("abcdef", 6)"#);
        check_expr_ok("abcdef", r#"LEFT("abcdef", 10)"#);

        check_expr_error("Syntax error in call to LEFT: expected expr$, n%", r#"LEFT()"#);
        check_expr_error("Syntax error in call to LEFT: expected expr$, n%", r#"LEFT("", 1, 2)"#);
        check_expr_error("Syntax error in call to LEFT: expected expr$, n%", r#"LEFT(1, 2)"#);
        check_expr_error("Syntax error in call to LEFT: expected expr$, n%", r#"LEFT("", "")"#);
        check_expr_error(
            "Syntax error in call to LEFT: n% cannot be negative",
            r#"LEFT("abcdef", -5)"#,
        );
    }

    #[test]
    fn test_len() {
        check_expr_ok(0, r#"LEN("")"#);
        check_expr_ok(1, r#"LEN(" ")"#);
        check_expr_ok(5, r#"LEN("abcde")"#);

        check_expr_error("Syntax error in call to LEN: expected expr$", r#"LEN()"#);
        check_expr_error("Syntax error in call to LEN: expected expr$", r#"LEN(3)"#);
        check_expr_error("Syntax error in call to LEN: expected expr$", r#"LEN(" ", 1)"#);
    }

    #[test]
    fn test_ltrim() {
        check_expr_ok("", r#"LTRIM("")"#);
        check_expr_ok("", r#"LTRIM("  ")"#);
        check_expr_ok("", "LTRIM(\"\t\t\")");
        check_expr_ok("foo \t ", "LTRIM(\" \t foo \t \")");

        check_expr_error("Syntax error in call to LTRIM: expected expr$", r#"LTRIM()"#);
        check_expr_error("Syntax error in call to LTRIM: expected expr$", r#"LTRIM(3)"#);
        check_expr_error("Syntax error in call to LTRIM: expected expr$", r#"LTRIM(" ", 1)"#);
    }

    #[test]
    fn test_mid() {
        check_expr_ok("", r#"MID("", 0, 0)"#);
        check_expr_ok("", r#"MID("basic", 0, 0)"#);
        check_expr_ok("", r#"MID("basic", 1, 0)"#);
        check_expr_ok("a", r#"MID("basic", 1, 1)"#);
        check_expr_ok("as", r#"MID("basic", 1, 2)"#);
        check_expr_ok("asic", r#"MID("basic", 1, 4)"#);
        check_expr_ok("asic", r#"MID("basic", 1, 10)"#);
        check_expr_ok("", r#"MID("basic", 100, 10)"#);

        check_expr_error(
            "Syntax error in call to MID: expected expr$, start%[, length%]",
            r#"MID()"#,
        );
        check_expr_error(
            "Syntax error in call to MID: expected expr$, start%[, length%]",
            r#"MID(3)"#,
        );
        check_expr_error(
            "Syntax error in call to MID: expected expr$, start%[, length%]",
            r#"MID(" ", 1, 1, 10)"#,
        );
        check_expr_error(
            "Syntax error in call to MID: expected expr$, start%[, length%]",
            r#"MID(" ", "1", "2")"#,
        );
        check_expr_error(
            "Syntax error in call to MID: start% cannot be negative",
            r#"MID("abcdef", -5, 10)"#,
        );
        check_expr_error(
            "Syntax error in call to MID: length% cannot be negative",
            r#"MID("abcdef", 3, -5)"#,
        );
    }

    #[test]
    fn test_right() {
        check_expr_ok("", r#"RIGHT("", 0)"#);
        check_expr_ok("def", r#"RIGHT("abcdef", 3)"#);
        check_expr_ok("abcdef", r#"RIGHT("abcdef", 6)"#);
        check_expr_ok("abcdef", r#"RIGHT("abcdef", 10)"#);

        check_expr_error("Syntax error in call to RIGHT: expected expr$, n%", r#"RIGHT()"#);
        check_expr_error("Syntax error in call to RIGHT: expected expr$, n%", r#"RIGHT("", 1, 2)"#);
        check_expr_error("Syntax error in call to RIGHT: expected expr$, n%", r#"RIGHT(1, 2)"#);
        check_expr_error("Syntax error in call to RIGHT: expected expr$, n%", r#"RIGHT("", "")"#);
        check_expr_error(
            "Syntax error in call to RIGHT: n% cannot be negative",
            r#"RIGHT("abcdef", -5)"#,
        );
    }

    #[test]
    fn test_rtrim() {
        check_expr_ok("", r#"RTRIM("")"#);
        check_expr_ok("", r#"RTRIM("  ")"#);
        check_expr_ok("", "RTRIM(\"\t\t\")");
        check_expr_ok(" \t foo", "RTRIM(\" \t foo \t \")");

        check_expr_error("Syntax error in call to RTRIM: expected expr$", r#"RTRIM()"#);
        check_expr_error("Syntax error in call to RTRIM: expected expr$", r#"RTRIM(3)"#);
        check_expr_error("Syntax error in call to RTRIM: expected expr$", r#"RTRIM(" ", 1)"#);
    }
}
