// EndBASIC
// Copyright 2020 Julio Merino
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

//! String functions for EndBASIC.

use endbasic_core::{
    AnyValueSyntax, ArgSep, ArgSepSyntax, CallError, CallResult, Callable, CallableMetadata,
    CallableMetadataBuilder, ExprType, RequiredValueSyntax, Scope, SingularArgSyntax, VarArgTag,
};
use std::borrow::Cow;
use std::cmp::min;
use std::convert::TryFrom;
use std::rc::Rc;

use crate::MachineBuilder;

/// Category description for all symbols provided by this module.
const CATEGORY: &str = "String and character functions";

/// Formats a boolean `b` for display.
pub fn format_boolean(b: bool) -> &'static str {
    if b { "TRUE" } else { "FALSE" }
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
    if !d.is_nan() && d.is_sign_negative() { d.to_string() } else { format!(" {}", d) }
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
    if i.is_negative() { i.to_string() } else { format!(" {}", i) }
}

/// Parses a string `s` as an integer.
pub fn parse_integer(s: &str) -> Result<i32, String> {
    match s.parse::<i32>() {
        Ok(d) => Ok(d),
        Err(_) => Err(format!("Invalid integer literal {}", s)),
    }
}

/// Returns the byte offset of the given character position within `s`.
fn char_index_to_byte_index(s: &str, char_index: usize) -> usize {
    s.char_indices().nth(char_index).map(|(i, _)| i).unwrap_or(s.len())
}

/// Returns the number of characters before the given byte offset within `s`.
fn byte_index_to_char_index(s: &str, byte_index: usize) -> usize {
    s[..byte_index].chars().count()
}

/// Parses the numeric prefix in `s` according to BASIC's `VAL` rules.
fn parse_numeric_prefix(s: &str) -> f64 {
    let s = s.trim_start();
    let bytes = s.as_bytes();

    let mut i = 0;
    if let Some(b'+' | b'-') = bytes.first().copied() {
        i += 1;
    }

    let int_start = i;
    while i < bytes.len() && bytes[i].is_ascii_digit() {
        i += 1;
    }
    let have_int = i > int_start;

    if i < bytes.len() && bytes[i] == b'.' {
        i += 1;
        let frac_start = i;
        while i < bytes.len() && bytes[i].is_ascii_digit() {
            i += 1;
        }
        if !have_int && i == frac_start {
            return 0.0;
        }
    } else if !have_int {
        return 0.0;
    }

    let mut end = i;
    if i < bytes.len() && matches!(bytes[i], b'e' | b'E') {
        let mut j = i + 1;
        if j < bytes.len() && matches!(bytes[j], b'+' | b'-') {
            j += 1;
        }
        let exp_start = j;
        while j < bytes.len() && bytes[j].is_ascii_digit() {
            j += 1;
        }
        if j > exp_start {
            end = j;
        }
    }

    s[..end].parse().expect("numeric prefix must parse")
}

/// The `ASC` function.
pub struct AscFunction {
    metadata: Rc<CallableMetadata>,
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

impl Callable for AscFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(1, scope.nargs());
        let s = scope.get_string(0);

        let mut chars = s.chars();
        let ch = match chars.next() {
            Some(ch) => ch,
            None => {
                return Err(CallError::Syntax(
                    scope.get_pos(0),
                    format!("Input string \"{}\" must be 1-character long", s),
                ));
            }
        };
        if chars.next().is_some() {
            return Err(CallError::Syntax(
                scope.get_pos(0),
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
    metadata: Rc<CallableMetadata>,
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

impl Callable for ChrFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(1, scope.nargs());
        let i = scope.get_integer(0);

        if i < 0 {
            return Err(CallError::Syntax(
                scope.get_pos(0),
                format!("Character code {} must be positive", i),
            ));
        }
        let code = i as u32;

        match char::from_u32(code) {
            Some(ch) => scope.return_string(format!("{}", ch)),
            None => {
                Err(CallError::Syntax(scope.get_pos(0), format!("Invalid character code {}", code)))
            }
        }
    }
}

/// The `INSTR` function.
pub struct InstrFunction {
    metadata: Rc<CallableMetadata>,
}

impl InstrFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("INSTR")
                .with_return_type(ExprType::Integer)
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
                                    name: Cow::Borrowed("search"),
                                    vtype: ExprType::Text,
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
                                    name: Cow::Borrowed("start"),
                                    vtype: ExprType::Integer,
                                },
                                ArgSepSyntax::Exactly(ArgSep::Long),
                            ),
                            SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax {
                                    name: Cow::Borrowed("expr"),
                                    vtype: ExprType::Text,
                                },
                                ArgSepSyntax::Exactly(ArgSep::Long),
                            ),
                            SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax {
                                    name: Cow::Borrowed("search"),
                                    vtype: ExprType::Text,
                                },
                                ArgSepSyntax::End,
                            ),
                        ],
                        None,
                    ),
                ])
                .with_category(CATEGORY)
                .with_description(
                    "Searches for a substring within another string.
Returns the 1-indexed position of search$ within expr$, or 0 if not found.
If start% is given, the search begins at that 1-indexed character position.",
                )
                .build(),
        })
    }
}

impl Callable for InstrFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert!((2..=3).contains(&scope.nargs()));

        let (start, sarg, searcharg) =
            if scope.nargs() == 2 { (1, 0, 1) } else { (scope.get_integer(0), 1, 2) };
        let s = scope.get_string(sarg);
        let search = scope.get_string(searcharg);

        if start <= 0 {
            return Err(CallError::Syntax(scope.get_pos(0), "start% must be positive".to_owned()));
        }
        let start = (start - 1) as usize;

        let slen = s.chars().count();
        if start > slen {
            return scope.return_integer(0);
        }
        if search.is_empty() {
            return scope.return_integer((start + 1) as i32);
        }

        let start_byte = char_index_to_byte_index(s, start);
        let position = match s[start_byte..].find(search) {
            Some(offset) => {
                let byte_index = start_byte + offset;
                (byte_index_to_char_index(s, byte_index) + 1) as i32
            }
            None => 0,
        };
        scope.return_integer(position)
    }
}

/// The `LCASE` function.
pub struct LcaseFunction {
    metadata: Rc<CallableMetadata>,
}

impl LcaseFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("LCASE")
                .with_return_type(ExprType::Text)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax { name: Cow::Borrowed("expr"), vtype: ExprType::Text },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .with_category(CATEGORY)
                .with_description(
                    "Returns a copy of a string with all letters converted to lowercase.",
                )
                .build(),
        })
    }
}

impl Callable for LcaseFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(1, scope.nargs());
        let s = scope.get_string(0).to_owned();

        scope.return_string(s.to_lowercase())
    }
}

/// The `LEFT` function.
pub struct LeftFunction {
    metadata: Rc<CallableMetadata>,
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

impl Callable for LeftFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(2, scope.nargs());
        let s = scope.get_string(0).to_owned();
        let n = scope.get_integer(1);

        if n < 0 {
            Err(CallError::Syntax(scope.get_pos(1), "n% cannot be negative".to_owned()))
        } else {
            let n = min(s.len(), n as usize);
            scope.return_string(s[..n].to_owned())
        }
    }
}

/// The `LEN` function.
pub struct LenFunction {
    metadata: Rc<CallableMetadata>,
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

impl Callable for LenFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(1, scope.nargs());
        let s = scope.get_string(0);

        let len =
            i32::try_from(s.len()).map_err(|_| CallError::Eval("String too long".to_owned()))?;
        scope.return_integer(len)
    }
}

/// The `LTRIM` function.
pub struct LtrimFunction {
    metadata: Rc<CallableMetadata>,
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

impl Callable for LtrimFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(1, scope.nargs());
        let s = scope.get_string(0).to_owned();

        scope.return_string(s.trim_start().to_owned())
    }
}

/// The `MID` function.
pub struct MidFunction {
    metadata: Rc<CallableMetadata>,
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

impl Callable for MidFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert!((2..=3).contains(&scope.nargs()));
        let s = scope.get_string(0).to_owned();
        let start = scope.get_integer(1);
        let lengtharg = if scope.nargs() == 3 { Some(scope.get_integer(2)) } else { None };

        if start < 0 {
            return Err(CallError::Syntax(
                scope.get_pos(1),
                "start% cannot be negative".to_owned(),
            ));
        }
        let start = min(s.len(), start as usize);

        let end = if let Some(length) = lengtharg {
            if length < 0 {
                return Err(CallError::Syntax(
                    scope.get_pos(2),
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
    metadata: Rc<CallableMetadata>,
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

impl Callable for RightFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(2, scope.nargs());
        let s = scope.get_string(0).to_owned();
        let n = scope.get_integer(1);

        if n < 0 {
            Err(CallError::Syntax(scope.get_pos(1), "n% cannot be negative".to_owned()))
        } else {
            let n = min(s.len(), n as usize);
            scope.return_string(s[s.len() - n..].to_owned())
        }
    }
}

/// The `RTRIM` function.
pub struct RtrimFunction {
    metadata: Rc<CallableMetadata>,
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

impl Callable for RtrimFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(1, scope.nargs());
        let s = scope.get_string(0).to_owned();

        scope.return_string(s.trim_end().to_owned())
    }
}

/// The `SPACE` function.
pub struct SpaceFunction {
    metadata: Rc<CallableMetadata>,
}

impl SpaceFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("SPACE")
                .with_return_type(ExprType::Text)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax { name: Cow::Borrowed("n"), vtype: ExprType::Integer },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .with_category(CATEGORY)
                .with_description(
                    "Returns a string that contains n% space characters.
If n% is 0, returns an empty string.",
                )
                .build(),
        })
    }
}

impl Callable for SpaceFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(1, scope.nargs());
        let n = scope.get_integer(0);

        if n < 0 {
            Err(CallError::Syntax(scope.get_pos(0), "n% cannot be negative".to_owned()))
        } else {
            scope.return_string(" ".repeat(n as usize))
        }
    }
}

/// The `STR` function.
pub struct StrFunction {
    metadata: Rc<CallableMetadata>,
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

impl Callable for StrFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(2, scope.nargs());
        match scope.get_type(0) {
            VarArgTag::Immediate(_, ExprType::Boolean) => {
                let b = scope.get_boolean(1);
                scope.return_string(format_boolean(b).to_owned())
            }

            VarArgTag::Immediate(_, ExprType::Double) => {
                let d = scope.get_double(1);
                scope.return_string(format_double(d))
            }

            VarArgTag::Immediate(_, ExprType::Integer) => {
                let i = scope.get_integer(1);
                scope.return_string(format_integer(i))
            }

            VarArgTag::Immediate(_, ExprType::Text) => {
                let s = scope.get_string(1).to_owned();
                scope.return_string(s)
            }

            VarArgTag::Missing(..) | VarArgTag::Pointer(..) => unreachable!(),
        }
    }
}

/// The `TRIM` function.
pub struct TrimFunction {
    metadata: Rc<CallableMetadata>,
}

impl TrimFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("TRIM")
                .with_return_type(ExprType::Text)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax { name: Cow::Borrowed("expr"), vtype: ExprType::Text },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .with_category(CATEGORY)
                .with_description(
                    "Returns a copy of a string with leading and trailing whitespace removed.",
                )
                .build(),
        })
    }
}

impl Callable for TrimFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(1, scope.nargs());
        let s = scope.get_string(0).to_owned();

        scope.return_string(s.trim().to_owned())
    }
}

/// The `UCASE` function.
pub struct UcaseFunction {
    metadata: Rc<CallableMetadata>,
}

impl UcaseFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("UCASE")
                .with_return_type(ExprType::Text)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax { name: Cow::Borrowed("expr"), vtype: ExprType::Text },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .with_category(CATEGORY)
                .with_description(
                    "Returns a copy of a string with all letters converted to uppercase.",
                )
                .build(),
        })
    }
}

impl Callable for UcaseFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(1, scope.nargs());
        let s = scope.get_string(0).to_owned();

        scope.return_string(s.to_uppercase())
    }
}

/// The `VAL` function.
pub struct ValFunction {
    metadata: Rc<CallableMetadata>,
}

impl ValFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("VAL")
                .with_return_type(ExprType::Double)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax { name: Cow::Borrowed("expr"), vtype: ExprType::Text },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .with_category(CATEGORY)
                .with_description(
                    "Parses a string as a number.
Returns the numeric prefix of expr$.  Leading whitespace is ignored, and if expr$ does not start \
with a number, this returns 0.  Stops processing (without an error) at the first non-numeric \
character.",
                )
                .build(),
        })
    }
}

impl Callable for ValFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(1, scope.nargs());
        let s = scope.get_string(0);

        let value = parse_numeric_prefix(s);
        scope.return_double(value)
    }
}

/// Adds all symbols provided by this module to the given `machine`.
pub fn add_all(machine: &mut MachineBuilder) {
    machine.add_callable(AscFunction::new());
    machine.add_callable(ChrFunction::new());
    machine.add_callable(InstrFunction::new());
    machine.add_callable(LcaseFunction::new());
    machine.add_callable(LeftFunction::new());
    machine.add_callable(LenFunction::new());
    machine.add_callable(LtrimFunction::new());
    machine.add_callable(MidFunction::new());
    machine.add_callable(RightFunction::new());
    machine.add_callable(RtrimFunction::new());
    machine.add_callable(SpaceFunction::new());
    machine.add_callable(StrFunction::new());
    machine.add_callable(TrimFunction::new());
    machine.add_callable(UcaseFunction::new());
    machine.add_callable(ValFunction::new());
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

        check_expr_compilation_error("1:10: ASC expected char$", r#"ASC()"#);
        check_expr_compilation_error("1:14: Expected STRING but found INTEGER", r#"ASC(3)"#);
        check_expr_compilation_error("1:10: ASC expected char$", r#"ASC("a", 1)"#);
        check_expr_error("1:14: Input string \"\" must be 1-character long", r#"ASC("")"#);
        check_expr_error("1:14: Input string \"ab\" must be 1-character long", r#"ASC("ab")"#);
    }

    #[test]
    fn test_chr() {
        check_expr_ok("a", r#"CHR(97)"#);
        check_expr_ok("c", r#"CHR(98.6)"#);
        check_expr_ok(" ", r#"CHR(32)"#);
        check_expr_ok("오", r#"CHR(50724)"#);

        check_expr_ok_with_vars(" ", r#"CHR(i)"#, [("i", 32.into())]);

        check_expr_compilation_error("1:10: CHR expected code%", r#"CHR()"#);
        check_expr_compilation_error("1:14: BOOLEAN is not a number", r#"CHR(FALSE)"#);
        check_expr_compilation_error("1:10: CHR expected code%", r#"CHR("a", 1)"#);
        check_expr_error("1:14: Character code -1 must be positive", r#"CHR(-1)"#);
        check_expr_error("1:14: Invalid character code 55296", r#"CHR(55296)"#);
    }

    #[test]
    fn test_asc_chr_integration() {
        check_expr_ok("a", r#"CHR(ASC("a"))"#);
        check_expr_ok('a' as i32, r#"ASC(CHR(97))"#);
    }

    #[test]
    fn test_instr() {
        check_expr_ok(0, r#"INSTR("", "a")"#);
        check_expr_ok(1, r#"INSTR("basic", "b")"#);
        check_expr_ok(3, r#"INSTR("basic", "si")"#);
        check_expr_ok(0, r#"INSTR("basic", "z")"#);
        check_expr_ok(4, r#"INSTR(4, "banana", "an")"#);
        check_expr_ok(2, r#"INSTR("banana", "an")"#);
        check_expr_ok(2, r#"INSTR("한글테스트", "글")"#);
        check_expr_ok(3, r#"INSTR(3, "basic", "")"#);

        check_expr_ok_with_vars(
            3,
            r#"INSTR(i, s, t)"#,
            [("i", 2.into()), ("s", "banana".into()), ("t", "na".into())],
        );

        check_expr_compilation_error(
            "1:10: INSTR expected <expr$, search$> | <start%, expr$, search$>",
            r#"INSTR()"#,
        );
        check_expr_compilation_error(
            "1:10: INSTR expected <expr$, search$> | <start%, expr$, search$>",
            r#"INSTR("a")"#,
        );
        check_expr_compilation_error(
            "1:10: INSTR expected <expr$, search$> | <start%, expr$, search$>",
            r#"INSTR("a", "b", "c", "d")"#,
        );
        check_expr_error("1:16: start% must be positive", r#"INSTR(0, "abc", "a")"#);
    }

    #[test]
    fn test_lcase() {
        check_expr_ok("", r#"LCASE("")"#);
        check_expr_ok("basic", r#"LCASE("BaSiC")"#);
        check_expr_ok("anos", r#"LCASE("ANOS")"#);

        check_expr_ok_with_vars("hello", r#"LCASE(s)"#, [("s", "HELLO".into())]);

        check_expr_compilation_error("1:10: LCASE expected expr$", r#"LCASE()"#);
        check_expr_compilation_error("1:16: Expected STRING but found INTEGER", r#"LCASE(3)"#);
        check_expr_compilation_error("1:10: LCASE expected expr$", r#"LCASE(" ", 1)"#);
    }

    #[test]
    fn test_left() {
        check_expr_ok("", r#"LEFT("", 0)"#);
        check_expr_ok("abc", r#"LEFT("abcdef", 3)"#);
        check_expr_ok("abcd", r#"LEFT("abcdef", 4)"#);
        check_expr_ok("abcdef", r#"LEFT("abcdef", 6)"#);
        check_expr_ok("abcdef", r#"LEFT("abcdef", 10)"#);

        check_expr_ok_with_vars("abc", r#"LEFT(s, i)"#, [("s", "abcdef".into()), ("i", 3.into())]);

        check_expr_compilation_error("1:10: LEFT expected expr$, n%", r#"LEFT()"#);
        check_expr_compilation_error("1:10: LEFT expected expr$, n%", r#"LEFT("", 1, 2)"#);
        check_expr_compilation_error("1:15: Expected STRING but found INTEGER", r#"LEFT(1, 2)"#);
        check_expr_compilation_error("1:19: STRING is not a number", r#"LEFT("", "")"#);
        check_expr_error("1:25: n% cannot be negative", r#"LEFT("abcdef", -5)"#);
    }

    #[test]
    fn test_len() {
        check_expr_ok(0, r#"LEN("")"#);
        check_expr_ok(1, r#"LEN(" ")"#);
        check_expr_ok(5, r#"LEN("abcde")"#);

        check_expr_ok_with_vars(4, r#"LEN(s)"#, [("s", "1234".into())]);

        check_expr_compilation_error("1:10: LEN expected expr$", r#"LEN()"#);
        check_expr_compilation_error("1:14: Expected STRING but found INTEGER", r#"LEN(3)"#);
        check_expr_compilation_error("1:10: LEN expected expr$", r#"LEN(" ", 1)"#);
    }

    #[test]
    fn test_ltrim() {
        check_expr_ok("", r#"LTRIM("")"#);
        check_expr_ok("", r#"LTRIM("  ")"#);
        check_expr_ok("", "LTRIM(\"\t\t\")");
        check_expr_ok("foo \t ", "LTRIM(\" \t foo \t \")");

        check_expr_ok_with_vars("foo ", r#"LTRIM(s)"#, [("s", " foo ".into())]);

        check_expr_compilation_error("1:10: LTRIM expected expr$", r#"LTRIM()"#);
        check_expr_compilation_error("1:16: Expected STRING but found INTEGER", r#"LTRIM(3)"#);
        check_expr_compilation_error("1:10: LTRIM expected expr$", r#"LTRIM(" ", 1)"#);
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
            "1:10: MID expected <expr$, start%> | <expr$, start%, length%>",
            r#"MID()"#,
        );
        check_expr_compilation_error(
            "1:10: MID expected <expr$, start%> | <expr$, start%, length%>",
            r#"MID(3)"#,
        );
        check_expr_compilation_error(
            "1:10: MID expected <expr$, start%> | <expr$, start%, length%>",
            r#"MID(" ", 1, 1, 10)"#,
        );
        check_expr_compilation_error("1:19: STRING is not a number", r#"MID(" ", "1", 2)"#);
        check_expr_compilation_error("1:22: STRING is not a number", r#"MID(" ", 1, "2")"#);
        check_expr_error("1:24: start% cannot be negative", r#"MID("abcdef", -5, 10)"#);
        check_expr_error("1:27: length% cannot be negative", r#"MID("abcdef", 3, -5)"#);
    }

    #[test]
    fn test_right() {
        check_expr_ok("", r#"RIGHT("", 0)"#);
        check_expr_ok("def", r#"RIGHT("abcdef", 3)"#);
        check_expr_ok("cdef", r#"RIGHT("abcdef", 4.2)"#);
        check_expr_ok("abcdef", r#"RIGHT("abcdef", 6)"#);
        check_expr_ok("abcdef", r#"RIGHT("abcdef", 10)"#);

        check_expr_ok_with_vars("def", r#"RIGHT(s, i)"#, [("s", "abcdef".into()), ("i", 3.into())]);

        check_expr_compilation_error("1:10: RIGHT expected expr$, n%", r#"RIGHT()"#);
        check_expr_compilation_error("1:10: RIGHT expected expr$, n%", r#"RIGHT("", 1, 2)"#);
        check_expr_compilation_error("1:16: Expected STRING but found INTEGER", r#"RIGHT(1, 2)"#);
        check_expr_compilation_error("1:20: STRING is not a number", r#"RIGHT("", "")"#);
        check_expr_error("1:26: n% cannot be negative", r#"RIGHT("abcdef", -5)"#);
    }

    #[test]
    fn test_rtrim() {
        check_expr_ok("", r#"RTRIM("")"#);
        check_expr_ok("", r#"RTRIM("  ")"#);
        check_expr_ok("", "RTRIM(\"\t\t\")");
        check_expr_ok(" \t foo", "RTRIM(\" \t foo \t \")");

        check_expr_ok_with_vars(" foo", r#"RTRIM(s)"#, [("s", " foo ".into())]);

        check_expr_compilation_error("1:10: RTRIM expected expr$", r#"RTRIM()"#);
        check_expr_compilation_error("1:16: Expected STRING but found INTEGER", r#"RTRIM(3)"#);
        check_expr_compilation_error("1:10: RTRIM expected expr$", r#"RTRIM(" ", 1)"#);
    }

    #[test]
    fn test_space() {
        check_expr_ok("", r#"SPACE(0)"#);
        check_expr_ok("   ", r#"SPACE(3)"#);
        check_expr_ok("     ", r#"SPACE(4.8)"#);

        check_expr_ok_with_vars("  ", r#"SPACE(i)"#, [("i", 2.into())]);

        check_expr_compilation_error("1:10: SPACE expected n%", r#"SPACE()"#);
        check_expr_compilation_error("1:16: BOOLEAN is not a number", r#"SPACE(FALSE)"#);
        check_expr_compilation_error("1:10: SPACE expected n%", r#"SPACE(1, 2)"#);
        check_expr_error("1:16: n% cannot be negative", r#"SPACE(-1)"#);
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

        check_expr_compilation_error("1:10: STR expected expr", r#"STR()"#);
        check_expr_compilation_error("1:10: STR expected expr", r#"STR(" ", 1)"#);
    }

    #[test]
    fn test_str_with_ltrim() {
        check_expr_ok("0", r#"LTRIM(STR(0))"#);
        check_expr_ok("-1", r#"LTRIM(STR(-1))"#);
        check_expr_ok("100", r#"LTRIM$(STR$(100))"#);
    }

    #[test]
    fn test_trim() {
        check_expr_ok("", r#"TRIM("")"#);
        check_expr_ok("", r#"TRIM("  ")"#);
        check_expr_ok("foo", "TRIM(\"\t foo \t\")");

        check_expr_ok_with_vars("foo", r#"TRIM(s)"#, [("s", " foo ".into())]);

        check_expr_compilation_error("1:10: TRIM expected expr$", r#"TRIM()"#);
        check_expr_compilation_error("1:15: Expected STRING but found INTEGER", r#"TRIM(3)"#);
        check_expr_compilation_error("1:10: TRIM expected expr$", r#"TRIM(" ", 1)"#);
    }

    #[test]
    fn test_ucase() {
        check_expr_ok("", r#"UCASE("")"#);
        check_expr_ok("BASIC", r#"UCASE("BaSiC")"#);
        check_expr_ok("AOS", r#"UCASE("aos")"#);

        check_expr_ok_with_vars("HELLO", r#"UCASE(s)"#, [("s", "hello".into())]);

        check_expr_compilation_error("1:10: UCASE expected expr$", r#"UCASE()"#);
        check_expr_compilation_error("1:16: Expected STRING but found INTEGER", r#"UCASE(3)"#);
        check_expr_compilation_error("1:10: UCASE expected expr$", r#"UCASE(" ", 1)"#);
    }

    #[test]
    fn test_val() {
        check_expr_ok(0.0, r#"VAL("")"#);
        check_expr_ok(0.0, r#"VAL("foo")"#);
        check_expr_ok(10.0, r#"VAL("10")"#);
        check_expr_ok(-21.5, r#"VAL("  -21.5xyz")"#);
        check_expr_ok(0.01, r#"VAL(".01")"#);
        check_expr_ok(1200.0, r#"VAL("12e2z")"#);
        check_expr_ok(12.0, r#"VAL("12e")"#);

        check_expr_ok_with_vars(3.5, r#"VAL(s)"#, [("s", "3.5ms".into())]);

        check_expr_compilation_error("1:10: VAL expected expr$", r#"VAL()"#);
        check_expr_compilation_error("1:14: Expected STRING but found INTEGER", r#"VAL(3)"#);
        check_expr_compilation_error("1:10: VAL expected expr$", r#"VAL(" ", 1)"#);
    }
}
