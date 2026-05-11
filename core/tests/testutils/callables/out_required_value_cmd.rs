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

use super::format_arg;
use endbasic_core::*;
use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;

/// A command that prints an argument of a specific type.
pub(super) struct OutRequiredValueCommand {
    metadata: Rc<CallableMetadata>,
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

impl Callable for OutRequiredValueCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let mut output = self.output.borrow_mut();
        output.push_str(&format_arg(&scope, 0, ExprType::Integer));
        output.push('\n');
        Ok(())
    }
}
