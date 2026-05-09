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

use super::format_vararg;
use async_trait::async_trait;
use endbasic_core::*;
use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;

/// A command that prints an argument of any type.
pub(super) struct OutAnyValueOptionalCommand {
    metadata: Rc<CallableMetadata>,
    output: Rc<RefCell<String>>,
}

impl OutAnyValueOptionalCommand {
    pub(super) fn new(output: Rc<RefCell<String>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("OUT_ANY_VALUE_OPTIONAL")
                .with_syntax(&[
                    (&[], None),
                    (
                        &[SingularArgSyntax::AnyValue(
                            AnyValueSyntax { name: Cow::Borrowed("arg"), allow_missing: true },
                            ArgSepSyntax::End,
                        )],
                        None,
                    ),
                ])
                .test_build(),
            output,
        })
    }
}

#[async_trait(?Send)]
impl Callable for OutAnyValueOptionalCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let (formatted, _present, sep) = format_vararg(&scope, 0);
        assert_eq!(ArgSep::End, sep, "Command only expects one argument");

        let mut output = self.output.borrow_mut();
        output.push_str(&formatted);
        output.push('\n');
        Ok(())
    }
}
