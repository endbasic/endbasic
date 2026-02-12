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

use super::format_arg;
use async_trait::async_trait;
use endbasic_core2::*;
use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;

/// A command that prints an argument of a specific type.
pub(super) struct OutRequiredValueCommand {
    metadata: CallableMetadata,
    output: Rc<RefCell<String>>,
}

impl OutRequiredValueCommand {
    pub(super) fn new(output: Rc<RefCell<String>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("OUT_REQUIRED_VALUE")
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax {
                            name: Cow::Borrowed("arg"),
                            vtype: ExprType::Integer,
                        },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .test_build(),
            output,
        })
    }
}

#[async_trait(?Send)]
impl Callable for OutRequiredValueCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let mut output = self.output.borrow_mut();
        output.push_str(&format_arg(&scope, 0, ExprType::Integer));
        output.push('\n');
        Ok(())
    }
}
