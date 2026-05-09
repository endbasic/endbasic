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
use std::borrow::Cow;
use std::rc::Rc;

/// A function that returns the sum of its initial double value and all integer arguments.
///
/// Uses `RequiredValue(Double)` followed by `TypedValue(Integer)` repeated args with
/// `ArgSepSyntax::Exactly(ArgSep::Long)` and `allow_missing = false`, which exercises the plain
/// values calling convention for the repeated args.
pub(super) struct SumMixedFunction {
    metadata: Rc<CallableMetadata>,
}

impl SumMixedFunction {
    pub(super) fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("SUM_MIXED")
                .with_return_type(ExprType::Double)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax {
                            name: Cow::Borrowed("base"),
                            vtype: ExprType::Double,
                        },
                        ArgSepSyntax::Exactly(ArgSep::Long),
                    )],
                    Some(&RepeatedSyntax {
                        name: Cow::Borrowed("expr"),
                        type_syn: RepeatedTypeSyntax::TypedValue(ExprType::Integer),
                        sep: ArgSepSyntax::Exactly(ArgSep::Long),
                        require_one: false,
                        allow_missing: false,
                    }),
                )])
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for SumMixedFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let mut total = scope.get_double(0);
        let num_singular: usize = 1;
        let mut reg = num_singular;
        while reg < scope.nargs() {
            total += f64::from(scope.get_integer(reg as u8));
            reg += 1;
        }
        scope.return_double(total)
    }
}
