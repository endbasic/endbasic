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

/// A command that defines the arguments passed in as a reference.
pub(super) struct DefineAndChangeArgsCommand {
    metadata: Rc<CallableMetadata>,
}

impl DefineAndChangeArgsCommand {
    pub(super) fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("DEFINE_AND_CHANGE_ARGS")
                .with_syntax(&[(
                    &[],
                    Some(&RepeatedSyntax {
                        name: Cow::Borrowed("arg"),
                        type_syn: RepeatedTypeSyntax::VariableRef,
                        sep: ArgSepSyntax::OneOf(&[ArgSep::Long, ArgSep::Short]),
                        require_one: true,
                        allow_missing: false,
                    }),
                )])
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for DefineAndChangeArgsCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn exec(&self, mut scope: Scope<'_>) -> CallResult<()> {
        let mut i = 0;
        loop {
            let VarArgTag::Pointer(sep) = scope.get_type(i) else {
                // TODO(jmmv): Replace with a proper error return and validate it.
                panic!("Command expects variable references only");
            };
            i += 1;

            let mut typed_ptr = scope.get_mut_ref(i);
            match typed_ptr.vtype {
                ExprType::Boolean => {
                    let b = typed_ptr.deref_boolean();
                    typed_ptr.set_boolean(!b);
                }

                ExprType::Double => {
                    let d = typed_ptr.deref_double();
                    typed_ptr.set_double(d + 0.6);
                }

                ExprType::Integer => {
                    let i = typed_ptr.deref_integer();
                    typed_ptr.set_integer(i + 1);
                }

                ExprType::Text => {
                    let s = typed_ptr.deref_string();
                    typed_ptr.set_string(format!("{}.", s));
                }
            }
            i += 1;

            if sep == ArgSep::End {
                break;
            }
        }
        Ok(())
    }
}
