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

//! Test utilities for consumers of the EndBASIC interpreter.

use crate::console::{self, ClearType, Console, Key, Position};
use crate::gpio;
use crate::storage::{Drive, InMemoryDrive, Program};
use async_trait::async_trait;
use endbasic_core::ast::{Value, VarType};
use endbasic_core::exec::{self, Machine, StopReason};
use endbasic_core::syms::{Array, Command, Function, Symbol};
use futures_lite::future::block_on;
use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::io;
use std::rc::Rc;
use std::result::Result;

/// A captured command or messages sent to the mock console.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CapturedOut {
    /// Represents a call to `Console::clear`.
    Clear(ClearType),

    /// Represents a call to `Console::color`.
    Color(Option<u8>, Option<u8>),

    /// Represents a call to `Console::enter_alt`.
    EnterAlt,

    /// Represents a call to `Console::hide_cursor`.
    HideCursor,

    /// Represents a call to `Console::leave_alt`.
    LeaveAlt,

    /// Represents a call to `Console::locate`.
    Locate(Position),

    /// Represents a call to `Console::move_within_line`.
    MoveWithinLine(i16),

    /// Represents a call to `Console::print`.
    Print(String),

    /// Represents a call to `Console::show_cursor`.
    ShowCursor,

    /// Represents a call to `Console::write`.
    Write(Vec<u8>),
}

/// A console that supplies golden input and captures all output.
pub struct MockConsole {
    /// Sequence of keys to yield on `read_key` calls.
    golden_in: VecDeque<Key>,

    /// Sequence of all messages printed.
    captured_out: Vec<CapturedOut>,

    /// The size of the mock console.
    size: Position,
}

impl Default for MockConsole {
    fn default() -> Self {
        Self {
            golden_in: VecDeque::new(),
            captured_out: vec![],
            size: Position { row: std::usize::MAX, column: std::usize::MAX },
        }
    }
}

impl MockConsole {
    /// Adds a bunch of characters as golden input keys.
    ///
    /// Note that some escape characters within `s` are interpreted and added as their
    /// corresponding `Key`s for simplicity.
    pub fn add_input_chars(&mut self, s: &str) {
        for ch in s.chars() {
            match ch {
                '\n' => self.golden_in.push_back(Key::NewLine),
                '\r' => self.golden_in.push_back(Key::CarriageReturn),
                ch => self.golden_in.push_back(Key::Char(ch)),
            }
        }
    }

    /// Adds a bunch of keys as golden input.
    pub fn add_input_keys(&mut self, keys: &[Key]) {
        self.golden_in.extend(keys.iter().cloned());
    }

    /// Obtains a reference to the captured output.
    pub fn captured_out(&self) -> &[CapturedOut] {
        self.captured_out.as_slice()
    }

    /// Sets the size of the mock console.
    pub fn set_size(&mut self, size: Position) {
        self.size = size;
    }
}

impl Drop for MockConsole {
    fn drop(&mut self) {
        assert!(
            self.golden_in.is_empty(),
            "Not all golden input chars were consumed; {} left",
            self.golden_in.len()
        );
    }
}

#[async_trait(?Send)]
impl Console for MockConsole {
    fn clear(&mut self, how: ClearType) -> io::Result<()> {
        self.captured_out.push(CapturedOut::Clear(how));
        Ok(())
    }

    fn color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()> {
        self.captured_out.push(CapturedOut::Color(fg, bg));
        Ok(())
    }

    fn enter_alt(&mut self) -> io::Result<()> {
        self.captured_out.push(CapturedOut::EnterAlt);
        Ok(())
    }

    fn hide_cursor(&mut self) -> io::Result<()> {
        self.captured_out.push(CapturedOut::HideCursor);
        Ok(())
    }

    fn is_interactive(&self) -> bool {
        false
    }

    fn leave_alt(&mut self) -> io::Result<()> {
        self.captured_out.push(CapturedOut::LeaveAlt);
        Ok(())
    }

    fn locate(&mut self, pos: Position) -> io::Result<()> {
        self.captured_out.push(CapturedOut::Locate(pos));
        Ok(())
    }

    fn move_within_line(&mut self, off: i16) -> io::Result<()> {
        self.captured_out.push(CapturedOut::MoveWithinLine(off));
        Ok(())
    }

    fn print(&mut self, text: &str) -> io::Result<()> {
        self.captured_out.push(CapturedOut::Print(text.to_owned()));
        Ok(())
    }

    async fn read_key(&mut self) -> io::Result<Key> {
        match self.golden_in.pop_front() {
            Some(ch) => Ok(ch),
            None => Ok(Key::Eof),
        }
    }

    fn show_cursor(&mut self) -> io::Result<()> {
        self.captured_out.push(CapturedOut::ShowCursor);
        Ok(())
    }

    fn size(&self) -> io::Result<Position> {
        Ok(self.size)
    }

    fn write(&mut self, bytes: &[u8]) -> io::Result<()> {
        self.captured_out.push(CapturedOut::Write(bytes.to_owned()));
        Ok(())
    }
}

/// A stored program that exposes golden contents and accepts new content from the console when
/// edits are requested.
#[derive(Default)]
pub struct RecordedProgram {
    content: String,
}

#[async_trait(?Send)]
impl Program for RecordedProgram {
    async fn edit(&mut self, console: &mut dyn Console) -> io::Result<()> {
        let append = console::read_line(console, "", "").await?;
        self.content.push_str(&append);
        self.content.push('\n');
        Ok(())
    }

    fn load(&mut self, text: &str) {
        self.content = text.to_owned();
    }

    fn text(&self) -> String {
        self.content.clone()
    }
}

/// Builder pattern to prepare an EndBASIC machine for testing purposes.
#[must_use]
pub struct Tester {
    console: Rc<RefCell<MockConsole>>,
    drive: Rc<RefCell<InMemoryDrive>>,
    program: Rc<RefCell<RecordedProgram>>,
    machine: Machine,
}

impl Default for Tester {
    /// Creates a new tester for a fully-equipped (interactive) machine.
    fn default() -> Self {
        let console = Rc::from(RefCell::from(MockConsole::default()));
        let drive = Rc::from(RefCell::from(InMemoryDrive::default()));
        let program = Rc::from(RefCell::from(RecordedProgram::default()));

        // Default to the pins set that always returns errors.  We could have implemented a set of
        // fake pins here to track GPIO state changes in a nicer way, similar to how we track all
        // other machine state... but the GPIO module already implements its own mocking feature.
        // The mocking feature is necessary for integration testing in any case, so we just use that
        // everywhere instead of having yet another implementation in this module.
        let gpio_pins = Rc::from(RefCell::from(gpio::NoopPins::default()));

        let machine = crate::MachineBuilder::default()
            .with_console(console.clone())
            .with_gpio_pins(gpio_pins)
            .make_interactive()
            .with_drive(drive.clone())
            .with_program(program.clone())
            .build()
            .unwrap();

        Self { console, drive, program, machine }
    }
}

impl Tester {
    /// Creates a new tester using the given `Machine`.
    pub fn from(machine: Machine) -> Self {
        let console = Rc::from(RefCell::from(MockConsole::default()));
        let drive = Rc::from(RefCell::from(InMemoryDrive::default()));
        let program = Rc::from(RefCell::from(RecordedProgram::default()));

        Self { console, drive, program, machine }
    }

    /// Registers the given builtin command into the machine, which must not yet be registered.
    pub fn add_command(mut self, command: Rc<dyn Command>) -> Self {
        self.machine.add_command(command);
        self
    }

    /// Registers the given builtin function into the machine, which must not yet be registered.
    pub fn add_function(mut self, function: Rc<dyn Function>) -> Self {
        self.machine.add_function(function);
        self
    }

    /// Adds the `golden_in` characters as console input.
    pub fn add_input_chars(self, golden_in: &str) -> Self {
        self.console.borrow_mut().add_input_chars(golden_in);
        self
    }

    /// Returns a mutable reference to the machine inside the tester.
    ///
    /// This method should generally not be used, except to run native methods that have
    /// side-effects on the machine that we'd like to validate later.
    pub fn get_machine(&mut self) -> &mut Machine {
        &mut self.machine
    }

    /// Gets the mock console from the tester.
    ///
    /// This method should generally not be used.  Its primary utility is to hook
    /// externally-instantiated commands into the testing features.
    pub fn get_console(&self) -> Rc<RefCell<MockConsole>> {
        self.console.clone()
    }

    /// Gets the in-memory drive from the tester.
    ///
    /// This method should generally not be used.  Its primary utility is to hook
    /// externally-instantiated commands into the testing features.
    pub fn get_drive(&self) -> Rc<RefCell<InMemoryDrive>> {
        self.drive.clone()
    }

    /// Gets the recorded program from the tester.
    ///
    /// This method should generally not be used.  Its primary utility is to hook
    /// externally-instantiated commands into the testing features.
    pub fn get_program(&self) -> Rc<RefCell<RecordedProgram>> {
        self.program.clone()
    }

    /// Sets the initial contents of the recorded program to `text`.  Can only be called once and
    /// `text` must not be empty.
    pub fn set_program(self, text: &str) -> Self {
        assert!(!text.is_empty());
        {
            let mut program = self.program.borrow_mut();
            assert!(program.text().is_empty());
            program.load(text);
        }
        self
    }

    /// Creates or overwrites a file in the storage medium.
    pub fn write_file(self, name: &str, content: &str) -> Self {
        self.drive.borrow_mut().put(name, content).unwrap();
        self
    }

    /// Runs `script` in the configured machine and returns a `Checker` object to validate
    /// expectations about the execution.
    pub fn run<S: Into<String>>(&mut self, script: S) -> Checker {
        let result = block_on(self.machine.exec(&mut script.into().as_bytes()));
        Checker::new(self, result)
    }
}

/// Captures expectations about the execution of a command and validates them.
#[must_use]
pub struct Checker<'a> {
    tester: &'a Tester,
    result: exec::Result<StopReason>,
    exp_result: Result<StopReason, String>,
    exp_output: Vec<CapturedOut>,
    exp_drive: HashMap<String, String>,
    exp_program: String,
    exp_arrays: HashMap<String, Array>,
    exp_vars: HashMap<String, Value>,
}

impl<'a> Checker<'a> {
    /// Creates a new checker with default expectations based on the results of an execution.
    ///
    /// The default expectations are that the execution ran through completion and that it did not
    /// have any side-effects.
    fn new(tester: &'a Tester, result: exec::Result<StopReason>) -> Self {
        Self {
            tester,
            result,
            exp_result: Ok(StopReason::Eof),
            exp_output: vec![],
            exp_drive: HashMap::default(),
            exp_program: String::new(),
            exp_arrays: HashMap::default(),
            exp_vars: HashMap::default(),
        }
    }

    /// Expects the invocation to have successfully terminated with the given `stop_reason`.
    ///
    /// If not called, defaults to expecting that execution terminated due to EOF.  This or
    /// `expect_err` can only be called once.
    pub fn expect_ok(mut self, stop_reason: StopReason) -> Self {
        assert_eq!(Ok(StopReason::Eof), self.exp_result);
        self.exp_result = Ok(stop_reason);
        self
    }

    /// Expects the invocation to have erroneously terminated with the exact `message`.
    ///
    /// If not called, defaults to expecting that execution terminated due to EOF.  This or
    /// `expect_err` can only be called once.
    pub fn expect_err<S: Into<String>>(mut self, message: S) -> Self {
        assert_eq!(Ok(StopReason::Eof), self.exp_result);
        self.exp_result = Err(message.into());
        self
    }

    /// Adds the `name` array as an array to expect in the final state of the machine.  The array
    /// will be tested to have the same `subtype` and `dimensions`, as well as specific `contents`.
    /// The contents are provided as a collection of subscripts/value pairs to assign to the
    /// expected array.
    pub fn expect_array<S: Into<String>>(
        mut self,
        name: S,
        subtype: VarType,
        dimensions: &[usize],
        contents: Vec<(&[i32], Value)>,
    ) -> Self {
        let name = name.into().to_ascii_uppercase();
        assert!(!self.exp_arrays.contains_key(&name));
        let mut array = Array::new(subtype, dimensions.to_owned());
        for (subscripts, value) in contents.into_iter() {
            array.assign(subscripts, value).unwrap();
        }
        self.exp_arrays.insert(name, array);
        self
    }

    /// Adds the `name` array as an array to expect in the final state of the machine.  The array
    /// will be tested to have the same `subtype` and only one dimension with `contents`.
    pub fn expect_array_simple<S: Into<String>>(
        mut self,
        name: S,
        subtype: VarType,
        contents: Vec<Value>,
    ) -> Self {
        let name = name.into().to_ascii_uppercase();
        assert!(!self.exp_arrays.contains_key(&name));
        let mut array = Array::new(subtype, vec![contents.len()]);
        for (i, value) in contents.into_iter().enumerate() {
            array.assign(&[i as i32], value).unwrap();
        }
        self.exp_arrays.insert(name, array);
        self
    }

    /// Adds a file to expect in the drive with a `name` and specific `content`.
    pub fn expect_file<N: Into<String>, C: Into<String>>(mut self, name: N, content: C) -> Self {
        let name = name.into();
        assert!(!self.exp_drive.contains_key(&name));
        self.exp_drive.insert(name, content.into());
        self
    }

    /// Adds the `out` sequence of captured outputs to the expected outputs of the execution.
    pub fn expect_output<V: Into<Vec<CapturedOut>>>(mut self, out: V) -> Self {
        self.exp_output.append(&mut out.into());
        self
    }

    /// Adds the `out` sequence of strings to the expected outputs of the execution.
    ///
    /// This is a convenience function around `expect_output` that wraps all incoming strings in
    /// `CapturedOut::Print` objects, as these are the most common outputs in tests.
    pub fn expect_prints<S: Into<String>, V: Into<Vec<S>>>(mut self, out: V) -> Self {
        let out = out.into();
        self.exp_output
            .append(&mut out.into_iter().map(|x| CapturedOut::Print(x.into())).collect());
        self
    }

    /// Sets the expected contents of the stored program to `text`.  Can only be called once and
    /// `text` must not be empty.
    pub fn expect_program<S: Into<String>>(mut self, text: S) -> Self {
        assert!(self.exp_program.is_empty());
        let text = text.into();
        assert!(!text.is_empty());
        self.exp_program = text;
        self
    }

    /// Adds the `name`/`value` pair as a variable to expect in the final state of the machine.
    pub fn expect_var<S: Into<String>, V: Into<Value>>(mut self, name: S, value: V) -> Self {
        let name = name.into().to_ascii_uppercase();
        assert!(!self.exp_vars.contains_key(&name));
        self.exp_vars.insert(name, value.into());
        self
    }

    /// Validates all expectations.
    pub fn check(self) {
        match self.result {
            Ok(stop_reason) => assert_eq!(self.exp_result.unwrap(), stop_reason),
            Err(e) => assert_eq!(self.exp_result.unwrap_err(), format!("{}", e)),
        };

        let mut arrays = HashMap::default();
        let mut vars = HashMap::default();
        for (name, symbol) in self.tester.machine.get_symbols().as_hashmap() {
            match symbol {
                Symbol::Array(array) => {
                    // TODO(jmmv): This array.clone() call is a hack to simplify the equality check
                    // below.  Should try to avoid it and remove the Clone impl from Array.
                    arrays.insert(name.to_owned(), array.clone());
                }
                Symbol::Command(_) | Symbol::Function(_) => {
                    // We currently don't support user-defined callables at runtime so there is no
                    // need to validate anything about them.
                }
                Symbol::Variable(value) => {
                    vars.insert(name.to_owned(), value.clone());
                }
            }
        }

        assert_eq!(self.exp_vars, vars);
        assert_eq!(self.exp_arrays, arrays);
        assert_eq!(self.exp_output, self.tester.console.borrow().captured_out());
        assert_eq!(self.exp_program, self.tester.program.borrow().text());
        assert_eq!(self.exp_drive, *self.tester.drive.borrow().as_hashmap());
    }
}

/// Executes `stmt` on a default `Tester` instance and checks that it fails with `exp_error`.
pub fn check_stmt_err<S: Into<String>>(exp_error: S, stmt: &str) {
    Tester::default().run(stmt).expect_err(exp_error).check();
}

/// Executes `expr` on a scripting interpreter and ensures that the result is `exp_value`.
pub fn check_expr_ok<V: Into<Value>>(exp_value: V, expr: &str) {
    Tester::default()
        .run(format!("result = {}", expr))
        .expect_var("result", exp_value.into())
        .check();
}

/// Executes `expr` on a scripting interpreter and ensures that evaluation fails with `exp_error`.
///
/// Note that `exp_error` is a literal exact match on the formatted error message returned by the
/// machine.
pub fn check_expr_error<S: Into<String>>(exp_error: S, expr: &str) {
    Tester::default().run(format!("result = {}", expr)).expect_err(exp_error).check();
}
