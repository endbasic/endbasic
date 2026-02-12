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

//! Callables exposed to integration tests.

use endbasic_core2::*;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

mod out_any_value_cmd;
use out_any_value_cmd::OutAnyValueCommand;

mod out_any_value_optional_cmd;
use out_any_value_optional_cmd::OutAnyValueOptionalCommand;

mod out_cmd;
use out_cmd::OutCommand;

mod out_optional_cmd;
use out_optional_cmd::OutOptionalCommand;

mod out_positional_cmd;
use out_positional_cmd::OutPositionalCommand;

mod out_required_value_cmd;
use out_required_value_cmd::OutRequiredValueCommand;

/// Formats the given argument `i` in `scope` as a string depending on its `etype`.
fn format_arg(scope: &Scope<'_>, i: u8, etype: ExprType) -> String {
    match etype {
        ExprType::Boolean => format!("{}", scope.get_boolean(i)),
        ExprType::Double => format!("{}", scope.get_double(i)),
        ExprType::Integer => format!("{}", scope.get_integer(i)),
        ExprType::Text => scope.get_string(i).to_string(),
    }
}

/// Formats variable argument `i` in `Scope` and returns the formatted argument, whether the
/// argument was present, and the separator that was found.
fn format_vararg(scope: &Scope<'_>, i: u8) -> (String, bool, ArgSep) {
    match scope.get_type(i) {
        VarArgTag::Immediate(sep, etype) => {
            let formatted = format_arg(scope, i + 1, etype);
            (format!("{}{}", formatted, etype.annotation()), true, sep)
        }
        VarArgTag::Missing(sep) => ("()".to_owned(), false, sep),
        VarArgTag::Pointer(_sep) => todo!("Support to load pointers not needed yet"),
    }
}

/// Registers all test-only callables into `upcalls_by_name`.
pub(super) fn register_all(
    upcalls_by_name: &mut HashMap<SymbolKey, Rc<dyn Callable>>,
    console: Rc<RefCell<String>>,
) {
    let cmds = [
        OutAnyValueCommand::new(console.clone()) as Rc<dyn Callable>,
        OutAnyValueOptionalCommand::new(console.clone()) as Rc<dyn Callable>,
        OutCommand::new(console.clone()) as Rc<dyn Callable>,
        OutOptionalCommand::new(console.clone()) as Rc<dyn Callable>,
        OutPositionalCommand::new(console.clone()) as Rc<dyn Callable>,
        OutRequiredValueCommand::new(console) as Rc<dyn Callable>,
    ];
    for cmd in cmds {
        upcalls_by_name.insert(SymbolKey::from(cmd.metadata().name()), cmd);
    }
}
