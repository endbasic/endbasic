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

/// A function that returns whether its integer argument is positive.
pub(super) struct IsPositiveFunction {
    metadata: CallableMetadata,
}

impl IsPositiveFunction {
    pub(super) fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("IS_POSITIVE")
                .with_return_type(ExprType::Boolean)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax { name: Cow::Borrowed("n"), vtype: ExprType::Integer },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for IsPositiveFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let n = scope.get_integer(1);
        scope.return_boolean(n > 0);
        Ok(())
    }
}
