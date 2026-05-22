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

use endbasic_core::*;
use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;

/// A command that prints all of its typed integer arguments.
pub(super) struct OutTypedIntegersCommand {
    metadata: Rc<CallableMetadata>,
    output: Rc<RefCell<String>>,
}

impl OutTypedIntegersCommand {
    pub(super) fn new(output: Rc<RefCell<String>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("OUT_TYPED_INTS")
                .with_syntax(&[(
                    &[],
                    Some(&RepeatedSyntax {
                        name: Cow::Borrowed("arg"),
                        type_syn: RepeatedTypeSyntax::TypedValue(ExprType::Integer),
                        sep: ArgSepSyntax::OneOf(&[ArgSep::Long, ArgSep::Short]),
                        require_one: true,
                        allow_missing: false,
                    }),
                )])
                .test_build(),
            output,
        })
    }
}

impl Callable for OutTypedIntegersCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let mut line = String::new();
        let mut reg = 0;
        loop {
            let VarArgTag::Immediate(sep, etype) = scope.get_type(reg) else {
                return Err(CallError::Other("Only accepts integer values".to_owned()));
            };
            reg += 1;

            if etype != ExprType::Integer {
                return Err(CallError::Other("Only accepts integer values".to_owned()));
            }

            line.push_str(&format!("{}{}", scope.get_integer(reg), ExprType::Integer.annotation()));
            reg += 1;

            if sep == ArgSep::End {
                break;
            }
            line.push(' ');
            line.push_str(&sep.to_string());
            line.push(' ');
        }

        let mut output = self.output.borrow_mut();
        output.push_str(&line);
        output.push('\n');
        Ok(())
    }
}
