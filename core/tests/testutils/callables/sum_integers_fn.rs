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
use std::rc::Rc;

/// A function that adds all of its integer arguments.
pub(super) struct SumIntegersFunction {
    metadata: Rc<CallableMetadata>,
}

impl SumIntegersFunction {
    pub(super) fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("SUM_INTEGERS")
                .with_return_type(ExprType::Integer)
                .with_syntax(&[(
                    &[],
                    Some(&RepeatedSyntax {
                        name: Cow::Borrowed("arg"),
                        type_syn: RepeatedTypeSyntax::AnyValue,
                        sep: ArgSepSyntax::Exactly(ArgSep::Long),
                        require_one: false,
                        allow_missing: true,
                    }),
                )])
                .test_build(),
        })
    }
}

impl Callable for SumIntegersFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let mut total: i32 = 0;
        let mut reg = 0;
        loop {
            let sep = match scope.get_type(reg) {
                VarArgTag::Immediate(sep, etype) => {
                    reg += 1;
                    match etype {
                        ExprType::Integer => total += scope.get_integer(reg),
                        _ => return Err(CallError::Other("Only accepts integer values")),
                    }
                    sep
                }

                _ => return Err(CallError::Other("Only accepts integer values")),
            };
            reg += 1;

            if sep == ArgSep::End {
                break;
            }
        }
        scope.return_integer(total)
    }
}
