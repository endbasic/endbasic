// EndBASIC
// Copyright 2026 Julio Merino
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

//! A callable exposed to integration tests.

use super::{format_arg, format_vararg};
use async_trait::async_trait;
use endbasic_core2::*;
use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;

/// A command that prints various positional arguments of different types.
pub(super) struct OutPositionalCommand {
    metadata: CallableMetadata,
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
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
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
