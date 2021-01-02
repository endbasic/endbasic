// EndBASIC
// Copyright 2020 Julio Merino
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

//! The EndBASIC language parser and interpreter.

// Keep these in sync with other top-level files.
#![allow(clippy::await_holding_refcell_ref)]
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(unused, unused_extern_crates, unused_import_braces, unused_qualifications)]
#![warn(unsafe_code)]

use crate::exec::MachineBuilder;
use std::cell::RefCell;
use std::rc::Rc;

// TODO(jmmv): Should narrow the exposed interface by 1.0.0.
pub mod ast;
pub mod console;
mod editor;
pub mod eval;
pub mod exec;
pub mod help;
mod lexer;
pub mod numerics;
mod parser;
mod reader;
pub mod repl;
pub mod store;
pub mod strings;

/// Creates a new machine builder populated with all scripting commands from the standard library.
pub fn scripting_machine_builder(console: Rc<RefCell<dyn console::Console>>) -> MachineBuilder {
    let mut builder = MachineBuilder::default();

    builder = console::add_all(builder, console);
    builder = numerics::add_all(builder);
    builder = strings::add_all(builder);

    // TODO: The "repl" doesn't belong in scripting, but this only brings in the EXIT command for
    // now and we need it here.  Should fix this in some way.
    builder = repl::add_all(builder);

    builder
}

/// Creates a new machine builder populated with all scripting _and_ interactive commands from the
/// standard library.
pub fn interactive_machine_builder(
    console: Rc<RefCell<dyn console::Console>>,
    store: Rc<RefCell<dyn store::Store>>,
) -> MachineBuilder {
    let mut builder = scripting_machine_builder(console.clone());

    let program = Rc::from(RefCell::from(editor::Editor::default()));

    builder = help::add_all(builder, console.clone());
    builder = store::add_all(builder, program, console, store);

    builder
}
