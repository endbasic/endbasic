// EndBASIC
// Copyright 2021 Julio Merino
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

//! The EndBASIC standard library.

// Keep these in sync with other top-level files.
#![allow(clippy::await_holding_refcell_ref)]
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(unused, unused_extern_crates, unused_import_braces, unused_qualifications)]
#![warn(unsafe_code)]

use endbasic_core::exec::Machine;
use std::cell::RefCell;
use std::rc::Rc;

// TODO(jmmv): Should narrow the exposed interface by 1.0.0.
pub mod console;
mod editor;
pub mod exec;
pub mod help;
pub mod numerics;
pub mod store;
pub mod strings;
#[cfg(test)]
pub(crate) mod testutils;

/// Creates a new machine populated with all scripting commands from the standard library.
pub fn scripting_machine(console: Rc<RefCell<dyn console::Console>>) -> Machine {
    let mut machine = Machine::default();

    console::add_all(&mut machine, console);
    exec::add_all(&mut machine);
    numerics::add_all(&mut machine);
    strings::add_all(&mut machine);

    machine
}

/// Creates a new machine populated with all scripting _and_ interactive commands from the
/// standard library.  This function is private because it permits specifying the initial contents
/// of the stored `program`, which by default should be empty for public users.
fn full_machine(
    console: Rc<RefCell<dyn console::Console>>,
    store: Rc<RefCell<dyn store::Store>>,
    program: Rc<RefCell<dyn store::Program>>,
) -> Machine {
    let mut machine = scripting_machine(console.clone());

    help::add_all(&mut machine, console.clone());
    store::add_all(&mut machine, program, console, store);

    machine
}

/// Creates a new machine populated with all scripting _and_ interactive commands from the
/// standard library.
pub fn interactive_machine(
    console: Rc<RefCell<dyn console::Console>>,
    store: Rc<RefCell<dyn store::Store>>,
) -> Machine {
    let program = Rc::from(RefCell::from(editor::Editor::default()));
    full_machine(console, store, program)
}
