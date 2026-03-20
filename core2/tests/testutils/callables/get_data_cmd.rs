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
use std::cell::RefCell;
use std::rc::Rc;

/// A command that dumps all DATA values visible to the upcall.
pub(super) struct GetDataCommand {
    metadata: Rc<CallableMetadata>,
    output: Rc<RefCell<String>>,
}

impl GetDataCommand {
    pub(super) fn new(output: Rc<RefCell<String>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GETDATA")
                .with_syntax(&[(&[], None)])
                .test_build(),
            output,
        })
    }
}

fn format_datum(datum: &Option<ConstantDatum>) -> String {
    match datum {
        None => "()".to_owned(),
        Some(ConstantDatum::Boolean(b)) => format!("{b}?"),
        Some(ConstantDatum::Double(d)) => format!("{d}#"),
        Some(ConstantDatum::Integer(i)) => format!("{i}%"),
        Some(ConstantDatum::Text(s)) => format!("{s}$"),
    }
}

#[async_trait(?Send)]
impl Callable for GetDataCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let text = scope
            .data()
            .iter()
            .enumerate()
            .map(|(i, datum)| format!("{i}={}", format_datum(datum)))
            .collect::<Vec<String>>()
            .join(" ");
        let mut output = self.output.borrow_mut();
        output.push_str(&text);
        output.push('\n');
        Ok(())
    }
}
