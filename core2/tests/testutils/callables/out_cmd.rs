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

use super::format_arg;
use async_trait::async_trait;
use endbasic_core2::*;
use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;

/// A command that prints its arguments to a virtual console.
pub(super) struct OutCommand {
    metadata: CallableMetadata,
    output: Rc<RefCell<String>>,
}

impl OutCommand {
    pub(super) fn new(output: Rc<RefCell<String>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("OUT")
                .with_syntax(&[(
                    &[],
                    Some(&RepeatedSyntax {
                        name: Cow::Borrowed("arg"),
                        type_syn: RepeatedTypeSyntax::AnyValue,
                        sep: ArgSepSyntax::OneOf(&[ArgSep::As, ArgSep::Long, ArgSep::Short]),
                        require_one: false,
                        allow_missing: true,
                    }),
                )])
                .test_build(),
            output,
        })
    }
}

#[async_trait(?Send)]
impl Callable for OutCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let mut line = String::new();
        let mut argi = 0;
        let mut reg = 0;
        loop {
            let sep = match scope.get_type(reg) {
                VarArgTag::Immediate(sep, etype) => {
                    reg += 1;
                    let formatted = format_arg(&scope, reg, etype);
                    line.push_str(&format!("{}={}{}", argi, formatted, etype.annotation()));
                    sep
                }
                VarArgTag::Missing(sep) => {
                    line.push_str(&format!("{}=()", argi));
                    sep
                }
                VarArgTag::Pointer(sep) => {
                    reg += 1;
                    let typed_ptr = scope.get_ref(reg);
                    line.push_str(&format!("{}={}", argi, typed_ptr));
                    sep
                }
            };
            argi += 1;
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
