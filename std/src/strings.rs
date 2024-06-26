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
use endbasic_core::ast::{ArgSep, ExprType};
use endbasic_core::compiler::{
    AnyValueSyntax, ArgSepSyntax, RequiredValueSyntax, SingularArgSyntax,
};
use endbasic_core::exec::{Machine, Scope, ValueTag};
use endbasic_core::syms::{
    CallError, CallResult, Callable, CallableMetadata, CallableMetadataBuilder,
};
use std::borrow::Cow;
use std::cmp::min;
use std::convert::TryFrom;
use std::rc::Rc;

/// Category description for all symbols provided by this module.
const CATEGORY: &str = "String and character functions";

/// Formats a boolean `b` for display.
pub fn format_boolean(b: bool) -> &'static str {
    if b {
        "TRUE"
    } else {
        "FALSE"
    }
}

/// Parses a string `s` as a boolean.
pub fn parse_boolean(s: &str) -> Result<bool, String> {
    let raw = s.to_uppercase();
    if raw == "TRUE" || raw == "YES" || raw == "Y" {
        Ok(true)
    } else if raw == "FALSE" || raw == "NO" || raw == "N" {
        Ok(false)
    } else {
        Err(format!("Invalid boolean literal {}", s))
    }
}

/// Formats a double `d` for display.
pub fn format_double(d: f64) -> String {
    if !d.is_nan() && d.is_sign_negative() {
        d.to_string()
    } else {
        format!(" {}", d)
    }
}

/// Parses a string `s` as a double.
pub fn parse_double(s: &str) -> Result<f64, String> {
    match s.parse::<f64>() {
        Ok(d) => Ok(d),
        Err(_) => Err(format!("Invalid double-precision floating point literal {}", s)),
    }
}

/// Formats an integer `i` for display.
pub fn format_integer(i: i32) -> String {
    if i.is_negative() {
        i.to_string()
    } else {
        format!(" {}", i)
    }
}

/// Parses a string `s` as an integer.
pub fn parse_integer(s: &str) -> Result<i32, String> {
    match s.parse::<i32>() {
        Ok(d) => Ok(d),
        Err(_) => Err(format!("Invalid integer literal {}", s)),
    }
}

/// The `ASC` function.
pub struct AscFunction {
    metadata: CallableMetadata,
}

impl AscFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("ASC")
                .with_return_type(ExprType::Integer)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax { name: Cow::Borrowed("char"), vtype: ExprType::Text },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
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
impl Callable for AscFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
        debug_assert_eq!(1, scope.nargs());
        let (s, spos) = scope.pop_string_with_pos();

        let mut chars = s.chars();
        let ch = match chars.next() {
            Some(ch) => ch,
            None => {
                return Err(CallError::ArgumentError(
                    spos,
                    format!("Input string \"{}\" must be 1-character long", s),
                ));
            }
        };
        if chars.next().is_some() {
            return Err(CallError::ArgumentError(
                spos,
                format!("Input string \"{}\" must be 1-character long", s),
            ));
        }
        let ch = if cfg!(debug_assertions) {
            i32::try_from(ch as u32).expect("Unicode code points end at U+10FFFF")
        } else {
            ch as i32
        };

        scope.return_integer(ch)
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
            metadata: CallableMetadataBuilder::new("CHR")
                .with_return_type(ExprType::Text)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax {
                            name: Cow::Borrowed("code"),
                            vtype: ExprType::Integer,
                        },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
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
impl Callable for ChrFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
        debug_assert_eq!(1, scope.nargs());
        let (i, ipos) = scope.pop_integer_with_pos();

        if i < 0 {
            return Err(CallError::ArgumentError(
                ipos,
                format!("Character code {} must be positive", i),
            ));
        }
        let code = i as u32;

        match char::from_u32(code) {
            Some(ch) => scope.return_string(format!("{}", ch)),
            None => Err(CallError::ArgumentError(ipos, format!("Invalid character code {}", code))),
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
            metadata: CallableMetadataBuilder::new("LEFT")
                .with_return_type(ExprType::Text)
                .with_syntax(&[(
                    &[
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("expr"),
                                vtype: ExprType::Text,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("n"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::End,
                        ),
                    ],
                    None,
                )])
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
impl Callable for LeftFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
        debug_assert_eq!(2, scope.nargs());
        let s = scope.pop_string();
        let (n, npos) = scope.pop_integer_with_pos();

        if n < 0 {
            Err(CallError::ArgumentError(npos, "n% cannot be negative".to_owned()))
        } else {
            let n = min(s.len(), n as usize);
            scope.return_string(s[..n].to_owned())
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
            metadata: CallableMetadataBuilder::new("LEN")
                .with_return_type(ExprType::Integer)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax { name: Cow::Borrowed("expr"), vtype: ExprType::Text },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .with_category(CATEGORY)
                .with_description("Returns the length of the string in expr$.")
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for LenFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
        debug_assert_eq!(1, scope.nargs());
        let (s, spos) = scope.pop_string_with_pos();

        if s.len() > i32::MAX as usize {
            Err(CallError::InternalError(spos, "String too long".to_owned()))
        } else {
            scope.return_integer(s.len() as i32)
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
            metadata: CallableMetadataBuilder::new("LTRIM")
                .with_return_type(ExprType::Text)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax { name: Cow::Borrowed("expr"), vtype: ExprType::Text },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .with_category(CATEGORY)
                .with_description("Returns a copy of a string with leading whitespace removed.")
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for LtrimFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
        debug_assert_eq!(1, scope.nargs());
        let s = scope.pop_string();

        scope.return_string(s.trim_start().to_owned())
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
            metadata: CallableMetadataBuilder::new("MID")
                .with_return_type(ExprType::Text)
                .with_syntax(&[
                    (
                        &[
                            SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax {
                                    name: Cow::Borrowed("expr"),
                                    vtype: ExprType::Text,
                                },
                                ArgSepSyntax::Exactly(ArgSep::Long),
                            ),
                            SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax {
                                    name: Cow::Borrowed("start"),
                                    vtype: ExprType::Integer,
                                },
                                ArgSepSyntax::End,
                            ),
                        ],
                        None,
                    ),
                    (
                        &[
                            SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax {
                                    name: Cow::Borrowed("expr"),
                                    vtype: ExprType::Text,
                                },
                                ArgSepSyntax::Exactly(ArgSep::Long),
                            ),
                            SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax {
                                    name: Cow::Borrowed("start"),
                                    vtype: ExprType::Integer,
                                },
                                ArgSepSyntax::Exactly(ArgSep::Long),
                            ),
                            SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax {
                                    name: Cow::Borrowed("length"),
                                    vtype: ExprType::Integer,
                                },
                                ArgSepSyntax::End,
                            ),
                        ],
                        None,
                    ),
                ])
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
impl Callable for MidFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
        debug_assert!((2..=3).contains(&scope.nargs()));
        let s = scope.pop_string();
        let (start, startpos) = scope.pop_integer_with_pos();
        let lengtharg = if scope.nargs() > 0 { Some(scope.pop_integer_with_pos()) } else { None };
        debug_assert_eq!(0, scope.nargs());

        if start < 0 {
            return Err(CallError::ArgumentError(startpos, "start% cannot be negative".to_owned()));
        }
        let start = min(s.len(), start as usize);

        let end = if let Some((length, lengthpos)) = lengtharg {
            if length < 0 {
                return Err(CallError::ArgumentError(
                    lengthpos,
                    "length% cannot be negative".to_owned(),
                ));
            }
            min(start + (length as usize), s.len())
        } else {
            s.len()
        };

        scope.return_string(s[start..end].to_owned())
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
            metadata: CallableMetadataBuilder::new("RIGHT")
                .with_return_type(ExprType::Text)
                .with_syntax(&[(
                    &[
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("expr"),
                                vtype: ExprType::Text,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("n"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::End,
                        ),
                    ],
                    None,
                )])
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
impl Callable for RightFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
        debug_assert_eq!(2, scope.nargs());
        let s = scope.pop_string();
        let (n, npos) = scope.pop_integer_with_pos();

        if n < 0 {
            Err(CallError::ArgumentError(npos, "n% cannot be negative".to_owned()))
        } else {
            let n = min(s.len(), n as usize);
            scope.return_string(s[s.len() - n..].to_owned())
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
            metadata: CallableMetadataBuilder::new("RTRIM")
                .with_return_type(ExprType::Text)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax { name: Cow::Borrowed("expr"), vtype: ExprType::Text },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .with_category(CATEGORY)
                .with_description("Returns a copy of a string with trailing whitespace removed.")
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for RtrimFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
        debug_assert_eq!(1, scope.nargs());
        let s = scope.pop_string();

        scope.return_string(s.trim_end().to_owned())
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
            metadata: CallableMetadataBuilder::new("STR")
                .with_return_type(ExprType::Text)
                .with_syntax(&[(
                    &[SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: Cow::Borrowed("expr"), allow_missing: false },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
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
impl Callable for StrFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
        debug_assert_eq!(2, scope.nargs());
        match scope.pop_value_tag() {
            ValueTag::Boolean => {
                let b = scope.pop_boolean();
                scope.return_string(format_boolean(b).to_owned())
            }
            ValueTag::Double => {
                let d = scope.pop_double();
                scope.return_string(format_double(d))
            }
            ValueTag::Integer => {
                let i = scope.pop_integer();
                scope.return_string(format_integer(i))
            }
            ValueTag::Text => {
                let s = scope.pop_string();
                scope.return_string(s)
            }
            ValueTag::Missing => {
                unreachable!("Missing expressions aren't allowed in function calls");
            }
        }
    }
}

/// Adds all symbols provided by this module to the given `machine`.
pub fn add_all(machine: &mut Machine) {
    machine.add_callable(AscFunction::new());
    machine.add_callable(ChrFunction::new());
    machine.add_callable(LeftFunction::new());
    machine.add_callable(LenFunction::new());
    machine.add_callable(LtrimFunction::new());
    machine.add_callable(MidFunction::new());
    machine.add_callable(RightFunction::new());
    machine.add_callable(RtrimFunction::new());
    machine.add_callable(StrFunction::new());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;

    #[test]
    fn test_value_parse_boolean() {
        for s in &["true", "TrUe", "TRUE", "yes", "Yes", "y", "Y"] {
            assert!(parse_boolean(s).unwrap());
        }

        for s in &["false", "FaLsE", "FALSE", "no", "No", "n", "N"] {
            assert!(!parse_boolean(s).unwrap());
        }

        for s in &["ye", "0", "1", " true"] {
            assert_eq!(
                format!("Invalid boolean literal {}", s),
                format!("{}", parse_boolean(s).unwrap_err())
            );
        }
    }

    #[test]
    fn test_value_parse_double() {
        assert_eq!(10.0, parse_double("10").unwrap());
        assert_eq!(0.0, parse_double("0").unwrap());
        assert_eq!(-21.0, parse_double("-21").unwrap());
        assert_eq!(1.0, parse_double("1.0").unwrap());
        assert_eq!(0.01, parse_double(".01").unwrap());

        assert_eq!(
            123456789012345680000000000000.0,
            parse_double("123456789012345678901234567890.1").unwrap()
        );

        assert_eq!(1.1234567890123457, parse_double("1.123456789012345678901234567890").unwrap());

        assert_eq!(
            "Invalid double-precision floating point literal ",
            format!("{}", parse_double("").unwrap_err())
        );
        assert_eq!(
            "Invalid double-precision floating point literal - 3.0",
            format!("{}", parse_double("- 3.0").unwrap_err())
        );
        assert_eq!(
            "Invalid double-precision floating point literal 34ab3.1",
            format!("{}", parse_double("34ab3.1").unwrap_err())
        );
    }

    #[test]
    fn test_value_parse_integer() {
        assert_eq!(10, parse_integer("10").unwrap());
        assert_eq!(0, parse_integer("0").unwrap());
        assert_eq!(-21, parse_integer("-21").unwrap());

        assert_eq!("Invalid integer literal ", format!("{}", parse_integer("").unwrap_err()));
        assert_eq!("Invalid integer literal - 3", format!("{}", parse_integer("- 3").unwrap_err()));
        assert_eq!(
            "Invalid integer literal 34ab3",
            format!("{}", parse_integer("34ab3").unwrap_err())
        );
    }

    #[test]
    fn test_asc() {
        check_expr_ok('a' as i32, r#"ASC("a")"#);
        check_expr_ok(' ' as i32, r#"ASC(" ")"#);
        check_expr_ok('오' as i32, r#"ASC("오")"#);

        check_expr_ok_with_vars('a' as i32, r#"ASC(s)"#, [("s", "a".into())]);

        check_expr_compilation_error("1:10: In call to ASC: expected char$", r#"ASC()"#);
        check_expr_compilation_error(
            "1:10: In call to ASC: 1:14: INTEGER is not a STRING",
            r#"ASC(3)"#,
        );
        check_expr_compilation_error("1:10: In call to ASC: expected char$", r#"ASC("a", 1)"#);
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

        check_expr_ok_with_vars(" ", r#"CHR(i)"#, [("i", 32.into())]);

        check_expr_compilation_error("1:10: In call to CHR: expected code%", r#"CHR()"#);
        check_expr_compilation_error(
            "1:10: In call to CHR: 1:14: BOOLEAN is not a number",
            r#"CHR(FALSE)"#,
        );
        check_expr_compilation_error("1:10: In call to CHR: expected code%", r#"CHR("a", 1)"#);
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

        check_expr_ok_with_vars("abc", r#"LEFT(s, i)"#, [("s", "abcdef".into()), ("i", 3.into())]);

        check_expr_compilation_error("1:10: In call to LEFT: expected expr$, n%", r#"LEFT()"#);
        check_expr_compilation_error(
            "1:10: In call to LEFT: expected expr$, n%",
            r#"LEFT("", 1, 2)"#,
        );
        check_expr_compilation_error(
            "1:10: In call to LEFT: 1:15: INTEGER is not a STRING",
            r#"LEFT(1, 2)"#,
        );
        check_expr_compilation_error(
            "1:10: In call to LEFT: 1:19: STRING is not a number",
            r#"LEFT("", "")"#,
        );
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

        check_expr_ok_with_vars(4, r#"LEN(s)"#, [("s", "1234".into())]);

        check_expr_compilation_error("1:10: In call to LEN: expected expr$", r#"LEN()"#);
        check_expr_compilation_error(
            "1:10: In call to LEN: 1:14: INTEGER is not a STRING",
            r#"LEN(3)"#,
        );
        check_expr_compilation_error("1:10: In call to LEN: expected expr$", r#"LEN(" ", 1)"#);
    }

    #[test]
    fn test_ltrim() {
        check_expr_ok("", r#"LTRIM("")"#);
        check_expr_ok("", r#"LTRIM("  ")"#);
        check_expr_ok("", "LTRIM(\"\t\t\")");
        check_expr_ok("foo \t ", "LTRIM(\" \t foo \t \")");

        check_expr_ok_with_vars("foo ", r#"LTRIM(s)"#, [("s", " foo ".into())]);

        check_expr_compilation_error("1:10: In call to LTRIM: expected expr$", r#"LTRIM()"#);
        check_expr_compilation_error(
            "1:10: In call to LTRIM: 1:16: INTEGER is not a STRING",
            r#"LTRIM(3)"#,
        );
        check_expr_compilation_error("1:10: In call to LTRIM: expected expr$", r#"LTRIM(" ", 1)"#);
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
        check_expr_ok("asic", r#"MID("basic", 1)"#);
        check_expr_ok("", r#"MID("basic", 100, 10)"#);

        check_expr_ok_with_vars(
            "asic",
            r#"MID(s, i, j)"#,
            [("s", "basic".into()), ("i", 1.into()), ("j", 4.into())],
        );

        check_expr_compilation_error(
            "1:10: In call to MID: expected <expr$, start%> | <expr$, start%, length%>",
            r#"MID()"#,
        );
        check_expr_compilation_error(
            "1:10: In call to MID: expected <expr$, start%> | <expr$, start%, length%>",
            r#"MID(3)"#,
        );
        check_expr_compilation_error(
            "1:10: In call to MID: expected <expr$, start%> | <expr$, start%, length%>",
            r#"MID(" ", 1, 1, 10)"#,
        );
        check_expr_compilation_error(
            "1:10: In call to MID: 1:19: STRING is not a number",
            r#"MID(" ", "1", 2)"#,
        );
        check_expr_compilation_error(
            "1:10: In call to MID: 1:22: STRING is not a number",
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

        check_expr_ok_with_vars("def", r#"RIGHT(s, i)"#, [("s", "abcdef".into()), ("i", 3.into())]);

        check_expr_compilation_error("1:10: In call to RIGHT: expected expr$, n%", r#"RIGHT()"#);
        check_expr_compilation_error(
            "1:10: In call to RIGHT: expected expr$, n%",
            r#"RIGHT("", 1, 2)"#,
        );
        check_expr_compilation_error(
            "1:10: In call to RIGHT: 1:16: INTEGER is not a STRING",
            r#"RIGHT(1, 2)"#,
        );
        check_expr_compilation_error(
            "1:10: In call to RIGHT: 1:20: STRING is not a number",
            r#"RIGHT("", "")"#,
        );
        check_expr_error(
            "1:10: In call to RIGHT: 1:26: n% cannot be negative",
            r#"RIGHT("abcdef", -5)"#,
        );
    }

    #[test]
    fn test_rtrim() {
        check_expr_ok("", r#"RTRIM("")"#);
        check_expr_ok("", r#"RTRIM("  ")"#);
        check_expr_ok("", "RTRIM(\"\t\t\")");
        check_expr_ok(" \t foo", "RTRIM(\" \t foo \t \")");

        check_expr_ok_with_vars(" foo", r#"RTRIM(s)"#, [("s", " foo ".into())]);

        check_expr_compilation_error("1:10: In call to RTRIM: expected expr$", r#"RTRIM()"#);
        check_expr_compilation_error(
            "1:10: In call to RTRIM: 1:16: INTEGER is not a STRING",
            r#"RTRIM(3)"#,
        );
        check_expr_compilation_error("1:10: In call to RTRIM: expected expr$", r#"RTRIM(" ", 1)"#);
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

        check_expr_ok_with_vars(" 1", r#"STR(i)"#, [("i", 1.into())]);

        check_expr_compilation_error("1:10: In call to STR: expected expr", r#"STR()"#);
        check_expr_compilation_error("1:10: In call to STR: expected expr", r#"STR(" ", 1)"#);
    }

    #[test]
    fn test_str_with_ltrim() {
        check_expr_ok("0", r#"LTRIM(STR(0))"#);
        check_expr_ok("-1", r#"LTRIM(STR(-1))"#);
        check_expr_ok("100", r#"LTRIM$(STR$(100))"#);
    }
}
