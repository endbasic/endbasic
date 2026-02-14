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

//! Callables exposed to integration tests.

use endbasic_core2::*;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

mod define_arg_cmd;
use define_arg_cmd::DefineArgCommand;

mod define_and_change_args_cmd;
use define_and_change_args_cmd::DefineAndChangeArgsCommand;

mod increment_required_int_cmd;
use increment_required_int_cmd::IncrementRequiredIntCommand;

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
        VarArgTag::Pointer(sep) => {
            let typed_ptr = scope.get_pointer(i + 1);
            (typed_ptr.to_string(), true, sep)
        }
    }
}

/// Registers all test-only callables into `upcalls_by_name`.
pub(super) fn register_all(
    upcalls_by_name: &mut HashMap<SymbolKey, Rc<dyn Callable>>,
    console: Rc<RefCell<String>>,
) {
    let cmds = [
        DefineArgCommand::new() as Rc<dyn Callable>,
        DefineAndChangeArgsCommand::new() as Rc<dyn Callable>,
        IncrementRequiredIntCommand::new() as Rc<dyn Callable>,
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
