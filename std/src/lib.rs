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
pub mod arrays;
pub mod console;
mod editor;
pub mod exec;
pub mod gpio;
pub mod help;
pub mod numerics;
pub mod program;
pub mod service;
pub mod storage;
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

/// Obtains the default set of pins for a Raspberry Pi.
#[cfg(feature = "rpi")]
fn default_gpio_pins() -> Rc<RefCell<dyn gpio::Pins>> {
    Rc::from(RefCell::from(gpio::RppalPins::default()))
}

/// Obtains the default set of pins for a platform without GPIO support.
#[cfg(not(feature = "rpi"))]
fn default_gpio_pins() -> Rc<RefCell<dyn gpio::Pins>> {
    Rc::from(RefCell::from(gpio::NoopPins::default()))
}

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

    /// Lazily initializes the `gpio_pins` field with a default value and returns it.
    fn get_gpio_pins(&mut self) -> Rc<RefCell<dyn gpio::Pins>> {
        if self.gpio_pins.is_none() {
            self.gpio_pins = Some(default_gpio_pins());
        }
        self.gpio_pins
            .as_ref()
            .expect("Default GPIO pins not available and with_gpio_pins() was not called")
            .clone()
    }

    /// Builds the interpreter.
    pub fn build(mut self) -> Result<Machine> {
        let mut machine = Machine::default();
        arrays::add_all(&mut machine);
        console::add_all(&mut machine, self.get_console()?);
        gpio::add_all(&mut machine, self.get_gpio_pins());
        exec::add_all(&mut machine, self.sleep_fn);
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
    service: Option<Rc<RefCell<dyn service::Service>>>,
}

impl InteractiveMachineBuilder {
    /// Constructs an interactive machine builder from a non-interactive builder.
    fn from(builder: MachineBuilder) -> Self {
        let storage = Rc::from(RefCell::from(storage::Storage::default()));
        InteractiveMachineBuilder { builder, program: None, storage, service: None }
    }

    /// Lazily initializes the `storage` field with a default value and returns it.
    pub fn get_storage(&mut self) -> Rc<RefCell<storage::Storage>> {
        self.storage.clone()
    }

    /// Overrides the default stored program with the given one.
    pub fn with_program(mut self, program: Rc<RefCell<dyn program::Program>>) -> Self {
        self.program = Some(program);
        self
    }

    /// Overrides the default service client with the given one.
    pub fn with_service(mut self, service: Rc<RefCell<dyn service::Service>>) -> Self {
        self.service = Some(service);
        self
    }

    /// Builds the interpreter.
    pub fn build(mut self) -> Result<Machine> {
        let console = self.builder.get_console()?;
        let storage = self.get_storage();
        let mut machine = self.builder.build()?;

        let program = match self.program {
            Some(program) => program,
            None => Rc::from(RefCell::from(editor::Editor::default())),
        };

        let service = match self.service {
            Some(service) => service,
            None => Rc::from(RefCell::from(service::CloudService::default())),
        };

        help::add_all(&mut machine, console.clone());
        program::add_all(&mut machine, program, console.clone(), storage.clone());
        service::add_all(&mut machine, service, console.clone(), storage.clone());
        storage::add_all(&mut machine, console, storage);

        Ok(machine)
    }
}
