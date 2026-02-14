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
