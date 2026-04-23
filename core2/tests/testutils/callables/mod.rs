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

mod array_ndims_fn;
use array_ndims_fn::ArrayNdimsFunction;

mod concat_fn;
use concat_fn::ConcatFunction;

mod define_arg_cmd;
use define_arg_cmd::DefineArgCommand;

mod define_and_change_args_cmd;
use define_and_change_args_cmd::DefineAndChangeArgsCommand;

mod get_data_cmd;
use get_data_cmd::GetDataCommand;

mod increment_required_int_cmd;
use increment_required_int_cmd::IncrementRequiredIntCommand;

mod is_positive_fn;
use is_positive_fn::IsPositiveFunction;

mod last_error_fn;
use last_error_fn::LastErrorFunction;

mod max_doubles_fn;
use max_doubles_fn::MaxDoublesFunction;

mod meaning_of_life_fn;
use meaning_of_life_fn::MeaningOfLifeFunction;

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

mod out_sep_end_cmd;
use out_sep_end_cmd::OutSepEndCommand;

mod out_typed_integers_cmd;
use out_typed_integers_cmd::OutTypedIntegersCommand;

mod raise_cmd;
use raise_cmd::RaiseCommand;

mod raisef_fn;
use raisef_fn::RaisefFunction;

mod sum_doubles_fn;
use sum_doubles_fn::SumDoublesFunction;

mod sum_integers_fn;
use sum_integers_fn::SumIntegersFunction;

mod sum_mixed_fn;
use sum_mixed_fn::SumMixedFunction;

mod sum_typed_integers_fn;
use sum_typed_integers_fn::SumTypedIntegersFunction;

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
            let typed_ptr = scope.get_ref(i + 1);
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
        ArrayNdimsFunction::new() as Rc<dyn Callable>,
        ConcatFunction::new() as Rc<dyn Callable>,
        DefineAndChangeArgsCommand::new() as Rc<dyn Callable>,
        DefineArgCommand::new() as Rc<dyn Callable>,
        GetDataCommand::new(console.clone()) as Rc<dyn Callable>,
        IncrementRequiredIntCommand::new() as Rc<dyn Callable>,
        IsPositiveFunction::new() as Rc<dyn Callable>,
        LastErrorFunction::new() as Rc<dyn Callable>,
        MaxDoublesFunction::new() as Rc<dyn Callable>,
        MeaningOfLifeFunction::new() as Rc<dyn Callable>,
        OutAnyValueCommand::new(console.clone()) as Rc<dyn Callable>,
        OutAnyValueOptionalCommand::new(console.clone()) as Rc<dyn Callable>,
        OutCommand::new(console.clone()) as Rc<dyn Callable>,
        OutOptionalCommand::new(console.clone()) as Rc<dyn Callable>,
        OutPositionalCommand::new(console.clone()) as Rc<dyn Callable>,
        OutRequiredValueCommand::new(console.clone()) as Rc<dyn Callable>,
        OutSepEndCommand::new(console.clone()) as Rc<dyn Callable>,
        OutTypedIntegersCommand::new(console) as Rc<dyn Callable>,
        RaiseCommand::new() as Rc<dyn Callable>,
        RaisefFunction::new() as Rc<dyn Callable>,
        SumDoublesFunction::new() as Rc<dyn Callable>,
        SumIntegersFunction::new() as Rc<dyn Callable>,
        SumMixedFunction::new() as Rc<dyn Callable>,
        SumTypedIntegersFunction::new() as Rc<dyn Callable>,
    ];
    for cmd in cmds {
        upcalls_by_name.insert(SymbolKey::from(cmd.metadata().name()), cmd);
    }
}
