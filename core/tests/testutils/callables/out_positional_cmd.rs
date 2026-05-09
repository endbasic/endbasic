// EndBASIC
// Copyright 2026 Julio Merino
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

//! A callable exposed to integration tests.

use super::{format_arg, format_vararg};
use async_trait::async_trait;
use endbasic_core::*;
use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;

/// A command that prints various positional arguments of different types.
pub(super) struct OutPositionalCommand {
    metadata: Rc<CallableMetadata>,
    output: Rc<RefCell<String>>,
}

impl OutPositionalCommand {
    pub(super) fn new(output: Rc<RefCell<String>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("OUT_POSITIONAL")
                .with_syntax(&[(
                    &[
                        SingularArgSyntax::AnyValue(
                            AnyValueSyntax { name: Cow::Borrowed("arg1"), allow_missing: true },
                            ArgSepSyntax::OneOf(&[ArgSep::Long, ArgSep::Short]),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("arg2"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::As),
                        ),
                        SingularArgSyntax::AnyValue(
                            AnyValueSyntax { name: Cow::Borrowed("arg3"), allow_missing: false },
                            ArgSepSyntax::End,
                        ),
                    ],
                    None,
                )])
                .test_build(),
            output,
        })
    }
}

#[async_trait(?Send)]
impl Callable for OutPositionalCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let mut output = self.output.borrow_mut();

        let mut i = 0;

        let (formatted, present, sep) = format_vararg(&scope, i);
        assert_ne!(ArgSep::End, sep, "Command expects more arguments");
        output.push_str(&formatted);
        output.push('\n');
        i += 1;
        if present {
            i += 1;
        }

        let formatted = format_arg(&scope, i, ExprType::Integer);
        output.push_str(&formatted);
        output.push('\n');
        i += 1;

        let (formatted, present, sep) = format_vararg(&scope, i);
        assert!(present, "Last argument is not optional");
        assert_eq!(ArgSep::End, sep, "No more arguments expected");
        output.push_str(&formatted);
        output.push('\n');

        Ok(())
    }
}
