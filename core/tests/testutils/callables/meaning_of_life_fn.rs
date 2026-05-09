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
use std::rc::Rc;

/// An argless function that returns the meaning of life (42).
pub(super) struct MeaningOfLifeFunction {
    metadata: Rc<CallableMetadata>,
}

impl MeaningOfLifeFunction {
    pub(super) fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("MEANING_OF_LIFE")
                .with_return_type(ExprType::Integer)
                .with_syntax(&[(&[], None)])
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for MeaningOfLifeFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        scope.return_integer(42)
    }
}
