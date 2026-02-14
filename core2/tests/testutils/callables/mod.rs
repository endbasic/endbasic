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

use endbasic_core2::{Callable, SymbolKey};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

mod out_cmd;
use out_cmd::OutCommand;

/// Registers all test-only callables into `upcalls_by_name`.
pub(super) fn register_all(
    upcalls_by_name: &mut HashMap<SymbolKey, Rc<dyn Callable>>,
    console: Rc<RefCell<String>>,
) {
    let cmd = OutCommand::new(console);
    upcalls_by_name.insert(SymbolKey::from(cmd.metadata().name()), cmd);
}
