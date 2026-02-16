// EndBASIC
// Copyright 2026 Julio Merino
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not
// use this file except in compliance with the License.  You may obtain a copy
// of the License at:
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
// License for the specific language governing permissions and limitations
// under the License.

//! A callable exposed to integration tests.

use async_trait::async_trait;
use endbasic_core2::*;
use std::borrow::Cow;
use std::rc::Rc;

/// A command that defines the arguments passed in as a reference.
pub(super) struct DefineAndChangeArgsCommand {
    metadata: CallableMetadata,
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
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
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
