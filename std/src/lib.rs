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

use endbasic_core::exec::{Machine, Result};
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
#[cfg(feature = "crossterm")]
pub mod terminal;
pub mod testutils;

/// Creates a handle to the default console when crossterm support is built in.
#[cfg(feature = "crossterm")]
fn try_get_default_console() -> Result<Option<Rc<RefCell<dyn console::Console>>>> {
    Ok(Some(Rc::from(RefCell::from(terminal::TerminalConsole::from_stdio()?))))
}

/// Placeholder to return no default console when we don't have one.
#[cfg(not(feature = "crossterm"))]
fn try_get_default_console() -> Result<Option<Rc<RefCell<dyn console::Console>>>> {
    Ok(None)
}

/// Builder pattern to construct an EndBASIC interpreter.
///
/// Unless otherwise specified, the interpreter is connected to a terminal-based console.
#[derive(Default)]
pub struct MachineBuilder {
    console: Option<Rc<RefCell<dyn console::Console>>>,
}

impl MachineBuilder {
    /// Overrides the default terminal-based console with the given one.
    pub fn with_console(mut self, console: Rc<RefCell<dyn console::Console>>) -> Self {
        self.console = Some(console);
        self
    }

    /// Lazily initializes the console field with a default value and returns it.
    fn get_console(&mut self) -> Result<Rc<RefCell<dyn console::Console>>> {
        if self.console.is_none() {
            self.console = try_get_default_console()?;
        }
        Ok(self
            .console
            .as_ref()
            .expect("Default console not available and with_console() was not called")
            .clone())
    }

    /// Builds the interpreter.
    pub fn build(mut self) -> Result<Machine> {
        let mut machine = Machine::default();
        console::add_all(&mut machine, self.get_console()?);
        exec::add_all(&mut machine);
        numerics::add_all(&mut machine);
        strings::add_all(&mut machine);
        Ok(machine)
    }

    /// Extends the machine with interactive (REPL) features.
    pub fn make_interactive(self) -> InteractiveMachineBuilder {
        InteractiveMachineBuilder { builder: self, program: None, store: None }
    }
}

/// Builder pattern to construct an interpreter for REPL operation.
///
/// This is a superset of a `ScriptingMachineBuilder`.
///
/// Unless otherwise specified, the interpreter is connected to an in-memory store and to a stored
/// program that can be edited interactively.
pub struct InteractiveMachineBuilder {
    builder: MachineBuilder,
    program: Option<Rc<RefCell<dyn store::Program>>>,
    store: Option<Rc<RefCell<dyn store::Store>>>,
}

impl InteractiveMachineBuilder {
    /// Overrides the default stored program with the given one.
    pub fn with_program(mut self, program: Rc<RefCell<dyn store::Program>>) -> Self {
        self.program = Some(program);
        self
    }

    /// Overrides the default in-memory store with the given one.
    pub fn with_store(mut self, store: Rc<RefCell<dyn store::Store>>) -> Self {
        self.store = Some(store);
        self
    }

    /// Builds the interpreter.
    pub fn build(mut self) -> Result<Machine> {
        let console = self.builder.get_console()?;
        let mut machine = self.builder.build()?;

        let program = match self.program {
            Some(program) => program,
            None => Rc::from(RefCell::from(editor::Editor::default())),
        };

        let store = match self.store {
            Some(store) => store,
            None => Rc::from(RefCell::from(store::InMemoryStore::default())),
        };

        help::add_all(&mut machine, console.clone());
        store::add_all(&mut machine, program, console, store);

        Ok(machine)
    }
}
