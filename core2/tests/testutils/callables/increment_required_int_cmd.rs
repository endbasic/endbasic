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

/// A command that increments the argument passed in as a reference.
pub(super) struct IncrementRequiredIntCommand {
    metadata: CallableMetadata,
}

impl IncrementRequiredIntCommand {
    pub(super) fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("INCREMENT_REQUIRED_INT")
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredRef(
                        RequiredRefSyntax {
                            name: Cow::Borrowed("arg"),
                            require_array: false,
                            define_undefined: false,
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
impl Callable for IncrementRequiredIntCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>) -> CallResult<()> {
        let mut typed_ptr = scope.get_mut_ref(0);
        if typed_ptr.vtype != ExprType::Integer {
            // TODO(jmmv): Make this error type more specific and determine the position of the
            // problematic argument via the `DebugInfo` which we should propagate through the
            // `Scope`.
            return Err(CallError::Other("Invalid type in argument"));
        }
        let mut i = typed_ptr.deref_integer();
        i += 1;
        typed_ptr.set_integer(i);
        Ok(())
    }
}
