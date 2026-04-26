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
use endbasic_core2::*;
use std::rc::Rc;

/// A function that returns the last error recorded by the VM.
pub(super) struct LastErrorFunction {
    metadata: Rc<CallableMetadata>,
}

impl LastErrorFunction {
    pub(super) fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("LAST_ERROR")
                .with_return_type(ExprType::Text)
                .with_syntax(&[(&[], None)])
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for LastErrorFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let last_error = scope.last_error().map(str::to_owned).unwrap_or_default();
        scope.return_string(last_error)
    }
}
