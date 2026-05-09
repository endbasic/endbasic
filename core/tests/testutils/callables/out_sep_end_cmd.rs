// EndBASIC
// Copyright 2026 Julio Merio
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

use async_trait::async_trait;
use endbasic_core::*;
use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;

/// A command that tests OneOf and End separator interactions on singular arguments.
///
/// This callable has two different syntaxes so that we can test scenarios where
/// `ArgSepSyntax::OneOf` receives `ArgSep::End` on a singular argument and must
/// reject it, which requires having two syntax variants whose `expected_nargs`
/// ranges overlap to allow parsing to proceed past `find_syntax`.
pub(super) struct OutSepEndCommand {
    metadata: Rc<CallableMetadata>,
    output: Rc<RefCell<String>>,
}

impl OutSepEndCommand {
    pub(super) fn new(output: Rc<RefCell<String>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("OUT_SEP_END")
                .with_syntax(&[(
                    &[
                        SingularArgSyntax::AnyValue(
                            AnyValueSyntax { name: Cow::Borrowed("first"), allow_missing: true },
                            ArgSepSyntax::OneOf(&[ArgSep::Long, ArgSep::Short]),
                        ),
                        SingularArgSyntax::AnyValue(
                            AnyValueSyntax { name: Cow::Borrowed("second"), allow_missing: false },
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
impl Callable for OutSepEndCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let mut output = self.output.borrow_mut();

        let (formatted, present, sep) = super::format_vararg(&scope, 0);
        output.push_str(&formatted);
        if present {
            output.push(' ');
            output.push_str(&sep.to_string());
            output.push(' ');
        }
        output.push('\n');

        let (formatted, present, sep) = super::format_vararg(&scope, 2);
        assert!(present, "Second argument must be present");
        assert_eq!(ArgSep::End, sep, "No more arguments expected");
        output.push_str(&formatted);
        output.push('\n');

        Ok(())
    }
}
