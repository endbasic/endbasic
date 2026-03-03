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
use std::borrow::Cow;
use std::rc::Rc;

/// A function that raises an error based on a string argument.
pub(super) struct RaisefFunction {
    metadata: CallableMetadata,
}

impl RaisefFunction {
    pub(super) fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("RAISEF")
                .with_return_type(ExprType::Boolean)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax { name: Cow::Borrowed("arg"), vtype: ExprType::Text },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for RaisefFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let arg = scope.get_string(1);
        let message = match arg {
            "argument" => "Bad argument",
            "eval" => "Some eval error",
            "internal" => "Some internal error",
            "io" => "Some I/O error",
            _ => "Invalid arguments",
        };
        Err(CallError::Other(message))
    }
}
