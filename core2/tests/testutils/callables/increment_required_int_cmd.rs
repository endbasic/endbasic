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
