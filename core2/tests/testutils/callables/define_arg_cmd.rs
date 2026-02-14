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

/// A command that defines the argument passed in as a reference.
pub(super) struct DefineArgCommand {
    metadata: CallableMetadata,
}

impl DefineArgCommand {
    pub(super) fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("DEFINE_ARG")
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredRef(
                        RequiredRefSyntax {
                            name: Cow::Borrowed("arg"),
                            require_array: false,
                            define_undefined: true,
                        },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for DefineArgCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, _scope: Scope<'_>) -> CallResult<()> {
        Ok(())
    }
}
