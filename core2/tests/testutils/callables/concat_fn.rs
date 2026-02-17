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

use async_trait::async_trait;
use endbasic_core2::*;
use std::borrow::Cow;
use std::rc::Rc;

/// A function that concatenates all of its string arguments.
pub(super) struct ConcatFunction {
    metadata: CallableMetadata,
}

impl ConcatFunction {
    pub(super) fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("CONCAT")
                .with_return_type(ExprType::Text)
                .with_syntax(&[(
                    &[],
                    Some(&RepeatedSyntax {
                        name: Cow::Borrowed("arg"),
                        type_syn: RepeatedTypeSyntax::AnyValue,
                        sep: ArgSepSyntax::Exactly(ArgSep::Long),
                        require_one: false,
                        allow_missing: true,
                    }),
                )])
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for ConcatFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let mut result = String::new();
        let mut reg = 1;
        loop {
            let sep = match scope.get_type(reg) {
                VarArgTag::Immediate(sep, etype) => {
                    reg += 1;
                    match etype {
                        ExprType::Text => result.push_str(scope.get_string(reg)),
                        _ => return Err(CallError::Other("Only accepts string values")),
                    }
                    sep
                }

                _ => return Err(CallError::Other("Only accepts string values")),
            };
            reg += 1;

            if sep == ArgSep::End {
                break;
            }
        }
        scope.return_string(result);
        Ok(())
    }
}
