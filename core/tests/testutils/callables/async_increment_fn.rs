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

use async_trait::async_trait;
use endbasic_core::*;
use futures_lite::future::yield_now;
use std::borrow::Cow;
use std::rc::Rc;

/// A function that increments the given integer asynchronously.
pub(super) struct AsyncIncrementFunction {
    metadata: Rc<CallableMetadata>,
}

impl AsyncIncrementFunction {
    pub(super) fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("ASYNC_INCREMENT")
                .with_return_type(ExprType::Integer)
                .with_async(true)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax {
                            name: Cow::Borrowed("value"),
                            vtype: ExprType::Integer,
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
impl Callable for AsyncIncrementFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn async_exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(1, scope.nargs());
        let incremented = scope.get_integer(0) + 1;
        yield_now().await;
        scope.return_integer(incremented)
    }
}
