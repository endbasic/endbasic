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
///
/// The first argument is a keyword that determines the error type.  When the
/// keyword is `"syntax"`, `"syntax0"`, or `"syntax1"`, the error is a
/// `CallError::Syntax` with the position overridden to point at the string
/// argument, the first argument, or the second argument respectively.  This
/// lets integration tests verify that the VM correctly propagates the position
/// override from `CallError::Syntax`.
pub(super) struct RaisefFunction {
    metadata: Rc<CallableMetadata>,
}

impl RaisefFunction {
    pub(super) fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("RAISEF")
                .with_return_type(ExprType::Boolean)
                .with_syntax(&[
                    (
                        &[SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("arg"),
                                vtype: ExprType::Text,
                            },
                            ArgSepSyntax::End,
                        )],
                        None,
                    ),
                    (
                        &[
                            SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax {
                                    name: Cow::Borrowed("arg"),
                                    vtype: ExprType::Text,
                                },
                                ArgSepSyntax::Exactly(ArgSep::Long),
                            ),
                            SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax {
                                    name: Cow::Borrowed("n"),
                                    vtype: ExprType::Integer,
                                },
                                ArgSepSyntax::End,
                            ),
                        ],
                        None,
                    ),
                ])
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for RaisefFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let arg = scope.get_string(0);
        match arg {
            "argument" => Err(CallError::Other("Bad argument")),
            "eval" => Err(CallError::Other("Some eval error")),
            "internal" => Err(CallError::Other("Some internal error")),
            "io" => Err(CallError::Other("Some I/O error")),
            "syntax" => Err(CallError::Syntax(scope.get_pos(0), "Some syntax error".to_owned())),
            "syntax0" => Err(CallError::Syntax(scope.get_pos(0), "Some syntax error".to_owned())),
            "syntax1" => Err(CallError::Syntax(scope.get_pos(1), "Some syntax error".to_owned())),
            _ => Err(CallError::Other("Invalid arguments")),
        }
    }
}
