// EndBASIC
// Copyright 2021 Julio Merino
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

//! Test utilities.

use crate::ast::{ArgSep, ExprType};
use crate::bytecode::VarArgTag;
use crate::callable::{
    ArgSepSyntax, CallResult, Callable, CallableMetadata, CallableMetadataBuilder, RepeatedSyntax,
    RepeatedTypeSyntax, Scope,
};
use async_trait::async_trait;
use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;

/// Simplified version of `PRINT` that captures all calls to it into `data`.
///
/// This command only accepts arguments separated by the `;` short separator and concatenates
/// them with a single space.
pub struct OutCommand {
    /// Metadata describing the command's name and syntax.
    metadata: CallableMetadata,

    /// Shared storage for captured output strings.
    data: Rc<RefCell<Vec<String>>>,
}

impl OutCommand {
    /// Creates a new command that captures all calls into `data`.
    pub fn new(data: Rc<RefCell<Vec<String>>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("OUT")
                .with_syntax(&[(
                    &[],
                    Some(&RepeatedSyntax {
                        name: Cow::Borrowed("arg"),
                        type_syn: RepeatedTypeSyntax::AnyValue,
                        sep: ArgSepSyntax::Exactly(ArgSep::Short),
                        require_one: false,
                        allow_missing: false,
                    }),
                )])
                .test_build(),
            data,
        })
    }
}

#[async_trait(?Send)]
impl Callable for OutCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let mut first = true;
        let mut text = String::new();
        let mut reg = 0;
        loop {
            if !first {
                text += " ";
            }
            first = false;

            let sep = match scope.get_type(reg) {
                VarArgTag::Immediate(sep, etype) => {
                    reg += 1;
                    match etype {
                        ExprType::Boolean => text.push_str(&format!("{}", scope.get_boolean(reg))),
                        ExprType::Double => text.push_str(&format!("{}", scope.get_double(reg))),
                        ExprType::Integer => text.push_str(&format!("{}", scope.get_integer(reg))),
                        ExprType::Text => text.push_str(scope.get_string(reg)),
                    }
                    sep
                }
                VarArgTag::Missing(sep) => {
                    text.push_str("<EMPTY>");
                    sep
                }
                VarArgTag::Pointer(_sep) => todo!("Support to load pointers not needed yet"),
            };
            reg += 1;

            if sep == ArgSep::End {
                break;
            }
            text.push(' ');
            text.push_str(&sep.to_string());
            text.push(' ');
        }
        self.data.borrow_mut().push(text);
        Ok(())
    }
}
