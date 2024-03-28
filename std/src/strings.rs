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

use async_trait::async_trait;
use endbasic_core::ast::{FunctionCallSpan, Value, VarType};
use endbasic_core::eval::eval_all;
use endbasic_core::exec::Machine;
use endbasic_core::syms::{
    CallError, CallableMetadata, CallableMetadataBuilder, Function, FunctionResult, Symbols,
};
use std::cmp::min;
use std::convert::TryFrom;
use std::rc::Rc;

/// Category description for all symbols provided by this module.
const CATEGORY: &str = "String and character functions";

/// The `ASC` function.
pub struct AscFunction {
    metadata: CallableMetadata,
}

impl AscFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("ASC", VarType::Integer)
                .with_syntax("char$")
                .with_category(CATEGORY)
                .with_description(
                    "Returns the UTF character code of the input character.
The input char$ argument is a string that must be 1-character long.
This is called ASC for historical reasons but supports more than just ASCII characters in this \
implementation of BASIC.
See CHR$() for the inverse of this function.",
                )
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for AscFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(&span.args, symbols).await?;
        match args.as_slice() {
            [Value::Text(s)] => {
                let mut chars = s.chars();
                let ch = match chars.next() {
                    Some(ch) => ch,
                    None => {
                        return Err(CallError::ArgumentError(
                            span.args[0].start_pos(),
                            format!("Input string \"{}\" must be 1-character long", s),
                        ));
                    }
                };
                if chars.next().is_some() {
                    return Err(CallError::ArgumentError(
                        span.args[0].start_pos(),
                        format!("Input string \"{}\" must be 1-character long", s),
                    ));
                }
                let ch = if cfg!(debug_assertions) {
                    i32::try_from(ch as u32).expect("Unicode code points end at U+10FFFF")
                } else {
                    ch as i32
                };
                Ok(Value::Integer(ch))
            }
            _ => Err(CallError::SyntaxError),
        }
    }
}

/// The `CHR` function.
pub struct ChrFunction {
    metadata: CallableMetadata,
}

impl ChrFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("CHR", VarType::Text)
                .with_syntax("code%")
                .with_category(CATEGORY)
                .with_description(
                    "Returns the UTF character that corresponds to the given code.
See ASC%() for the inverse of this function.",
                )
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for ChrFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(&span.args, symbols).await?;
        match args.as_slice() {
            [v @ Value::Integer(_) | v @ Value::Double(_)] => {
                let pos = span.args[0].start_pos();

                let i = v.as_i32().map_err(|e| CallError::ArgumentError(pos, format!("{}", e)))?;
                if i < 0 {
                    return Err(CallError::ArgumentError(
                        pos,
                        format!("Character code {} must be positive", i),
                    ));
                }
                let code = i as u32;

                match char::from_u32(code) {
                    Some(ch) => Ok(Value::Text(format!("{}", ch))),
                    None => Err(CallError::ArgumentError(
                        pos,
                        format!("Invalid character code {}", code),
                    )),
                }
            }
            _ => Err(CallError::SyntaxError),
        }
    }
}

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

#[async_trait(?Send)]
impl Function for LeftFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(&span.args, symbols).await?;
        match args.as_slice() {
            [Value::Text(s), n] => {
                let n = n.as_i32().map_err(|e| {
                    CallError::ArgumentError(span.args[1].start_pos(), format!("{}", e))
                })?;
                if n < 0 {
                    Err(CallError::ArgumentError(
                        span.args[1].start_pos(),
                        "n% cannot be negative".to_owned(),
                    ))
                } else {
                    let n = min(s.len(), n as usize);
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

#[async_trait(?Send)]
impl Function for LenFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(&span.args, symbols).await?;
        match args.as_slice() {
            [Value::Text(s)] => {
                if s.len() > std::i32::MAX as usize {
                    Err(CallError::InternalError(
                        span.args[0].start_pos(),
                        "String too long".to_owned(),
                    ))
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

#[async_trait(?Send)]
impl Function for LtrimFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(&span.args, symbols).await?;
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

#[async_trait(?Send)]
impl Function for MidFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(&span.args, symbols).await?;
        match args.as_slice() {
            [Value::Text(s), start, length] => {
                let start = start.as_i32().map_err(|e| {
                    CallError::ArgumentError(span.args[1].start_pos(), format!("{}", e))
                })?;
                let length = length.as_i32().map_err(|e| {
                    CallError::ArgumentError(span.args[2].start_pos(), format!("{}", e))
                })?;
                if start < 0 {
                    Err(CallError::ArgumentError(
                        span.args[1].start_pos(),
                        "start% cannot be negative".to_owned(),
                    ))
                } else if length < 0 {
                    Err(CallError::ArgumentError(
                        span.args[2].start_pos(),
                        "length% cannot be negative".to_owned(),
                    ))
                } else {
                    let start = min(s.len(), start as usize);
                    let end = min(start + (length as usize), s.len());
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

#[async_trait(?Send)]
impl Function for RightFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(&span.args, symbols).await?;
        match args.as_slice() {
            [Value::Text(s), n] => {
                let n = n.as_i32().map_err(|e| {
                    CallError::ArgumentError(span.args[1].start_pos(), format!("{}", e))
                })?;
                if n < 0 {
                    Err(CallError::ArgumentError(
                        span.args[0].start_pos(),
                        "n% cannot be negative".to_owned(),
                    ))
                } else {
                    let n = min(s.len(), n as usize);
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

#[async_trait(?Send)]
impl Function for RtrimFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(&span.args, symbols).await?;
        match args.as_slice() {
            [Value::Text(s)] => Ok(Value::Text(s.trim_end().to_owned())),
            _ => Err(CallError::SyntaxError),
        }
    }
}

/// The `STR` function.
pub struct StrFunction {
    metadata: CallableMetadata,
}

impl StrFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("STR", VarType::Text)
                .with_syntax("expr")
                .with_category(CATEGORY)
                .with_description(
                    "Formats a scalar value as a string.
If expr evaluates to a string, this returns the string unmodified.
If expr evaluates to a boolean, this returns the strings FALSE or TRUE.
If expr evaluates to a number, this returns a string with the textual representation of the \
number.  If the number does NOT have a negative sign, the resulting string has a single space \
in front of it.
To obtain a clean representation of expr as a string without any artificial whitespace characters \
in it, do LTRIM$(STR$(expr)).",
                )
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for StrFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(&span.args, symbols).await?;
        let mut iter = args.into_iter();
        let value = match iter.next() {
            Some(v) => v,
            None => return Err(CallError::SyntaxError),
        };
        if iter.next().is_some() {
            return Err(CallError::SyntaxError);
        }
        Ok(Value::Text(value.to_text()))
    }
}

/// Adds all symbols provided by this module to the given `machine`.
pub fn add_all(machine: &mut Machine) {
    machine.add_function(AscFunction::new());
    machine.add_function(ChrFunction::new());
    machine.add_function(LeftFunction::new());
    machine.add_function(LenFunction::new());
    machine.add_function(LtrimFunction::new());
    machine.add_function(MidFunction::new());
    machine.add_function(RightFunction::new());
    machine.add_function(RtrimFunction::new());
    machine.add_function(StrFunction::new());
}

#[cfg(test)]
mod tests {
    use crate::testutils::*;

    #[test]
    fn test_asc() {
        check_expr_ok('a' as i32, r#"ASC("a")"#);
        check_expr_ok(' ' as i32, r#"ASC(" ")"#);
        check_expr_ok('오' as i32, r#"ASC("오")"#);

        check_expr_error("1:10: In call to ASC: expected char$", r#"ASC()"#);
        check_expr_error("1:10: In call to ASC: expected char$", r#"ASC(3)"#);
        check_expr_error("1:10: In call to ASC: expected char$", r#"ASC("a", 1)"#);
        check_expr_error(
            "1:10: In call to ASC: 1:14: Input string \"\" must be 1-character long",
            r#"ASC("")"#,
        );
        check_expr_error(
            "1:10: In call to ASC: 1:14: Input string \"ab\" must be 1-character long",
            r#"ASC("ab")"#,
        );
    }

    #[test]
    fn test_chr() {
        check_expr_ok("a", r#"CHR(97)"#);
        check_expr_ok("c", r#"CHR(98.6)"#);
        check_expr_ok(" ", r#"CHR(32)"#);
        check_expr_ok("오", r#"CHR(50724)"#);

        check_expr_error("1:10: In call to CHR: expected code%", r#"CHR()"#);
        check_expr_error("1:10: In call to CHR: expected code%", r#"CHR(FALSE)"#);
        check_expr_error("1:10: In call to CHR: expected code%", r#"CHR("a", 1)"#);
        check_expr_error(
            "1:10: In call to CHR: 1:14: Character code -1 must be positive",
            r#"CHR(-1)"#,
        );
        check_expr_error(
            "1:10: In call to CHR: 1:14: Invalid character code 55296",
            r#"CHR(55296)"#,
        );
    }

    #[test]
    fn test_asc_chr_integration() {
        check_expr_ok("a", r#"CHR(ASC("a"))"#);
        check_expr_ok('a' as i32, r#"ASC(CHR(97))"#);
    }

    #[test]
    fn test_left() {
        check_expr_ok("", r#"LEFT("", 0)"#);
        check_expr_ok("abc", r#"LEFT("abcdef", 3)"#);
        check_expr_ok("abcd", r#"LEFT("abcdef", 4)"#);
        check_expr_ok("abcdef", r#"LEFT("abcdef", 6)"#);
        check_expr_ok("abcdef", r#"LEFT("abcdef", 10)"#);

        check_expr_error("1:10: In call to LEFT: expected expr$, n%", r#"LEFT()"#);
        check_expr_error("1:10: In call to LEFT: expected expr$, n%", r#"LEFT("", 1, 2)"#);
        check_expr_error("1:10: In call to LEFT: expected expr$, n%", r#"LEFT(1, 2)"#);
        check_expr_error("1:10: In call to LEFT: 1:19: \"\" is not a number", r#"LEFT("", "")"#);
        check_expr_error(
            "1:10: In call to LEFT: 1:25: n% cannot be negative",
            r#"LEFT("abcdef", -5)"#,
        );
    }

    #[test]
    fn test_len() {
        check_expr_ok(0, r#"LEN("")"#);
        check_expr_ok(1, r#"LEN(" ")"#);
        check_expr_ok(5, r#"LEN("abcde")"#);

        check_expr_error("1:10: In call to LEN: expected expr$", r#"LEN()"#);
        check_expr_error("1:10: In call to LEN: expected expr$", r#"LEN(3)"#);
        check_expr_error("1:10: In call to LEN: expected expr$", r#"LEN(" ", 1)"#);
    }

    #[test]
    fn test_ltrim() {
        check_expr_ok("", r#"LTRIM("")"#);
        check_expr_ok("", r#"LTRIM("  ")"#);
        check_expr_ok("", "LTRIM(\"\t\t\")");
        check_expr_ok("foo \t ", "LTRIM(\" \t foo \t \")");

        check_expr_error("1:10: In call to LTRIM: expected expr$", r#"LTRIM()"#);
        check_expr_error("1:10: In call to LTRIM: expected expr$", r#"LTRIM(3)"#);
        check_expr_error("1:10: In call to LTRIM: expected expr$", r#"LTRIM(" ", 1)"#);
    }

    #[test]
    fn test_mid() {
        check_expr_ok("", r#"MID("", 0, 0)"#);
        check_expr_ok("", r#"MID("basic", 0, 0)"#);
        check_expr_ok("", r#"MID("basic", 1, 0)"#);
        check_expr_ok("a", r#"MID("basic", 1, 1)"#);
        check_expr_ok("as", r#"MID("basic", 1, 2)"#);
        check_expr_ok("asic", r#"MID("basic", 1, 4)"#);
        check_expr_ok("asi", r#"MID("basic", 0.8, 3.2)"#);
        check_expr_ok("asic", r#"MID("basic", 1, 10)"#);
        check_expr_ok("", r#"MID("basic", 100, 10)"#);

        check_expr_error("1:10: In call to MID: expected expr$, start%[, length%]", r#"MID()"#);
        check_expr_error("1:10: In call to MID: expected expr$, start%[, length%]", r#"MID(3)"#);
        check_expr_error(
            "1:10: In call to MID: expected expr$, start%[, length%]",
            r#"MID(" ", 1, 1, 10)"#,
        );
        check_expr_error(
            "1:10: In call to MID: 1:19: \"1\" is not a number",
            r#"MID(" ", "1", 2)"#,
        );
        check_expr_error(
            "1:10: In call to MID: 1:22: \"2\" is not a number",
            r#"MID(" ", 1, "2")"#,
        );
        check_expr_error(
            "1:10: In call to MID: 1:24: start% cannot be negative",
            r#"MID("abcdef", -5, 10)"#,
        );
        check_expr_error(
            "1:10: In call to MID: 1:27: length% cannot be negative",
            r#"MID("abcdef", 3, -5)"#,
        );
    }

    #[test]
    fn test_right() {
        check_expr_ok("", r#"RIGHT("", 0)"#);
        check_expr_ok("def", r#"RIGHT("abcdef", 3)"#);
        check_expr_ok("cdef", r#"RIGHT("abcdef", 4.2)"#);
        check_expr_ok("abcdef", r#"RIGHT("abcdef", 6)"#);
        check_expr_ok("abcdef", r#"RIGHT("abcdef", 10)"#);

        check_expr_error("1:10: In call to RIGHT: expected expr$, n%", r#"RIGHT()"#);
        check_expr_error("1:10: In call to RIGHT: expected expr$, n%", r#"RIGHT("", 1, 2)"#);
        check_expr_error("1:10: In call to RIGHT: expected expr$, n%", r#"RIGHT(1, 2)"#);
        check_expr_error("1:10: In call to RIGHT: 1:20: \"\" is not a number", r#"RIGHT("", "")"#);
        check_expr_error(
            "1:10: In call to RIGHT: 1:16: n% cannot be negative",
            r#"RIGHT("abcdef", -5)"#,
        );
    }

    #[test]
    fn test_rtrim() {
        check_expr_ok("", r#"RTRIM("")"#);
        check_expr_ok("", r#"RTRIM("  ")"#);
        check_expr_ok("", "RTRIM(\"\t\t\")");
        check_expr_ok(" \t foo", "RTRIM(\" \t foo \t \")");

        check_expr_error("1:10: In call to RTRIM: expected expr$", r#"RTRIM()"#);
        check_expr_error("1:10: In call to RTRIM: expected expr$", r#"RTRIM(3)"#);
        check_expr_error("1:10: In call to RTRIM: expected expr$", r#"RTRIM(" ", 1)"#);
    }

    #[test]
    fn test_str() {
        check_expr_ok("FALSE", r#"STR(FALSE)"#);
        check_expr_ok("TRUE", r#"STR(true)"#);

        check_expr_ok(" 0", r#"STR(0)"#);
        check_expr_ok(" 1", r#"STR(1)"#);
        check_expr_ok("-1", r#"STR(-1)"#);

        check_expr_ok(" 0.5", r#"STR(0.5)"#);
        check_expr_ok(" 1.5", r#"STR(1.5)"#);
        check_expr_ok("-1.5", r#"STR(-1.5)"#);

        check_expr_ok("", r#"STR("")"#);
        check_expr_ok(" \t ", "STR(\" \t \")");
        check_expr_ok("foo bar", r#"STR("foo bar")"#);

        check_expr_error("1:10: In call to STR: expected expr", r#"STR()"#);
        check_expr_error("1:10: In call to STR: expected expr", r#"STR(" ", 1)"#);
    }

    #[test]
    fn test_str_with_ltrim() {
        check_expr_ok("0", r#"LTRIM(STR(0))"#);
        check_expr_ok("-1", r#"LTRIM(STR(-1))"#);
        check_expr_ok("100", r#"LTRIM$(STR$(100))"#);
    }
}
