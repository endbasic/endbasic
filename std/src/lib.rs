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
#![allow(clippy::collapsible_else_if)]
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(unused, unused_extern_crates, unused_import_braces, unused_qualifications)]
#![warn(unsafe_code)]

use endbasic_core::exec::{Machine, Result};
use std::cell::RefCell;
use std::rc::Rc;

// TODO(jmmv): Should narrow the exposed interface by 1.0.0.
pub mod arrays;
pub mod console;
pub mod data;
pub mod exec;
pub mod gfx;
pub mod gpio;
pub mod help;
pub mod numerics;
pub mod program;
pub mod storage;
pub mod strings;
pub mod testutils;

/// Builder pattern to construct an EndBASIC interpreter.
///
/// Unless otherwise specified, the interpreter is connected to a terminal-based console.
#[derive(Default)]
pub struct MachineBuilder {
    console: Option<Rc<RefCell<dyn console::Console>>>,
    gpio_pins: Option<Rc<RefCell<dyn gpio::Pins>>>,
    sleep_fn: Option<exec::SleepFn>,
}

impl MachineBuilder {
    /// Overrides the default terminal-based console with the given one.
    pub fn with_console(mut self, console: Rc<RefCell<dyn console::Console>>) -> Self {
        self.console = Some(console);
        self
    }

    /// Overrides the default hardware-based GPIO pins with the given ones.
    pub fn with_gpio_pins(mut self, pins: Rc<RefCell<dyn gpio::Pins>>) -> Self {
        self.gpio_pins = Some(pins);
        self
    }

    /// Overrides the default sleep function with the given one.
    pub fn with_sleep_fn(mut self, sleep_fn: exec::SleepFn) -> Self {
        self.sleep_fn = Some(sleep_fn);
        self
    }

    /// Lazily initializes the `console` field with a default value and returns it.
    pub fn get_console(&mut self) -> Rc<RefCell<dyn console::Console>> {
        if self.console.is_none() {
            self.console = Some(Rc::from(RefCell::from(console::TrivialConsole::default())));
        }
        self.console.clone().unwrap()
    }

    /// Lazily initializes the `gpio_pins` field with a default value and returns it.
    fn get_gpio_pins(&mut self) -> Rc<RefCell<dyn gpio::Pins>> {
        if self.gpio_pins.is_none() {
            self.gpio_pins = Some(Rc::from(RefCell::from(gpio::NoopPins::default())))
        }
        self.gpio_pins.as_ref().expect("Must have been initialized above").clone()
    }

    /// Builds the interpreter.
    pub fn build(mut self) -> Result<Machine> {
        let console = self.get_console();
        let gpio_pins = self.get_gpio_pins();

        let mut machine = Machine::default();
        arrays::add_all(&mut machine);
        console::add_all(&mut machine, console.clone());
        data::add_all(&mut machine);
        gfx::add_all(&mut machine, console);
        gpio::add_all(&mut machine, gpio_pins);
        exec::add_scripting(&mut machine, self.sleep_fn);
        numerics::add_all(&mut machine);
        strings::add_all(&mut machine);
        Ok(machine)
    }

    /// Extends the machine with interactive (REPL) features.
    pub fn make_interactive(self) -> InteractiveMachineBuilder {
        InteractiveMachineBuilder::from(self)
    }
}

/// Builder pattern to construct an interpreter for REPL operation.
///
/// This is a superset of a `ScriptingMachineBuilder`.
///
/// Unless otherwise specified, the interpreter is connected to an in-memory drive and to a stored
/// program that can be edited interactively.
pub struct InteractiveMachineBuilder {
    builder: MachineBuilder,
    program: Option<Rc<RefCell<dyn program::Program>>>,
    storage: Rc<RefCell<storage::Storage>>,
}

impl InteractiveMachineBuilder {
    /// Constructs an interactive machine builder from a non-interactive builder.
    fn from(builder: MachineBuilder) -> Self {
        let storage = Rc::from(RefCell::from(storage::Storage::default()));
        InteractiveMachineBuilder { builder, program: None, storage }
    }

    /// Returns the console that will be used for the machine.
    pub fn get_console(&mut self) -> Rc<RefCell<dyn console::Console>> {
        self.builder.get_console()
    }

    /// Lazily initializes the `program` field with a default value and returns it.
    pub fn get_program(&mut self) -> Rc<RefCell<dyn program::Program>> {
        if self.program.is_none() {
            self.program = Some(Rc::from(RefCell::from(program::ImmutableProgram::default())));
        }
        self.program.clone().unwrap()
    }

    /// Returns the storage subsystem that will be used for the machine.
    pub fn get_storage(&mut self) -> Rc<RefCell<storage::Storage>> {
        self.storage.clone()
    }

    /// Overrides the default stored program with the given one.
    pub fn with_program(mut self, program: Rc<RefCell<dyn program::Program>>) -> Self {
        self.program = Some(program);
        self
    }

    /// Builds the interpreter.
    pub fn build(mut self) -> Result<Machine> {
        let console = self.builder.get_console();
        let program = self.get_program();
        let storage = self.get_storage();
        let mut machine = self.builder.build()?;

        exec::add_interactive(&mut machine);
        help::add_all(&mut machine, console.clone());
        program::add_all(&mut machine, program, console.clone(), storage.clone());
        storage::add_all(&mut machine, console, storage);

        Ok(machine)
    }
}
