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

use crate::console::{
    self, remove_control_chars, CharsXY, ClearType, Console, Key, PixelsXY, SizeInPixels,
};
use crate::gpio;
use crate::program::Program;
use crate::storage::Storage;
use async_trait::async_trait;
use endbasic_core::ast::{ExprType, Value, VarRef};
use endbasic_core::exec::{self, Machine, StopReason};
use endbasic_core::syms::{Array, Callable, Symbol, SymbolKey};
use futures_lite::future::block_on;
use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::io;
use std::rc::Rc;
use std::result::Result;
use std::str;

/// A captured command or messages sent to the mock console.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CapturedOut {
    /// Represents a call to `Console::clear`.
    Clear(ClearType),

    /// Represents a call to `Console::set_color`.
    SetColor(Option<u8>, Option<u8>),

    /// Represents a call to `Console::enter_alt`.
    EnterAlt,

    /// Represents a call to `Console::hide_cursor`.
    HideCursor,

    /// Represents a call to `Console::leave_alt`.
    LeaveAlt,

    /// Represents a call to `Console::locate`.
    Locate(CharsXY),

    /// Represents a call to `Console::move_within_line`.
    MoveWithinLine(i16),

    /// Represents a call to `Console::print`.
    Print(String),

    /// Represents a call to `Console::show_cursor`.
    ShowCursor,

    /// Represents a call to `Console::write`.
    Write(String),

    /// Represents a call to `Console::draw_circle`.
    DrawCircle(PixelsXY, u16),

    /// Represents a call to `Console::draw_circle_filled`.
    DrawCircleFilled(PixelsXY, u16),

    /// Represents a call to `Console::draw_line`.
    DrawLine(PixelsXY, PixelsXY),

    /// Represents a call to `Console::draw_pixel`.
    DrawPixel(PixelsXY),

    /// Represents a call to `Console::draw_rect`.
    DrawRect(PixelsXY, PixelsXY),

    /// Represents a call to `Console::draw_rect_filled`.
    DrawRectFilled(PixelsXY, PixelsXY),

    /// Represents a call to `Console::sync_now`.
    SyncNow,

    /// Represents a call to `Console::set_sync`.
    SetSync(bool),
}

/// A console that supplies golden input and captures all output.
pub struct MockConsole {
    /// Sequence of keys to yield on `read_key` calls.
    golden_in: VecDeque<Key>,

    /// Sequence of all messages printed.
    captured_out: Vec<CapturedOut>,

    /// The size of the mock text console.
    size_chars: CharsXY,

    /// The size of the mock graphical console.
    size_pixels: Option<SizeInPixels>,

    /// Whether the console is interactive or not.
    interactive: bool,
}

impl Default for MockConsole {
    fn default() -> Self {
        Self {
            golden_in: VecDeque::new(),
            captured_out: vec![],
            size_chars: CharsXY::new(u16::MAX, u16::MAX),
            size_pixels: None,
            interactive: false,
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

    /// Takes the captured output for separate analysis.
    #[must_use]
    pub fn take_captured_out(&mut self) -> Vec<CapturedOut> {
        let mut copy = Vec::with_capacity(self.captured_out.len());
        copy.append(&mut self.captured_out);
        copy
    }

    /// Sets the size of the mock text console.
    pub fn set_size_chars(&mut self, size: CharsXY) {
        self.size_chars = size;
    }

    /// Sets the size of the mock graphical console.
    pub fn set_size_pixels(&mut self, size: SizeInPixels) {
        self.size_pixels = Some(size);
    }

    /// Sets whether the mock console is interactive or not.
    pub fn set_interactive(&mut self, interactive: bool) {
        self.interactive = interactive;
    }

    /// Ensures that all prerecorded input characters were consumed.
    fn verify_all_used(&mut self) {
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

    fn color(&self) -> (Option<u8>, Option<u8>) {
        for o in self.captured_out.iter().rev() {
            if let CapturedOut::SetColor(fg, bg) = o {
                return (*fg, *bg);
            }
        }
        (None, None)
    }

    fn set_color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()> {
        self.captured_out.push(CapturedOut::SetColor(fg, bg));
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
        self.interactive
    }

    fn leave_alt(&mut self) -> io::Result<()> {
        self.captured_out.push(CapturedOut::LeaveAlt);
        Ok(())
    }

    fn locate(&mut self, pos: CharsXY) -> io::Result<()> {
        assert!(pos.x < self.size_chars.x);
        assert!(pos.y < self.size_chars.y);
        self.captured_out.push(CapturedOut::Locate(pos));
        Ok(())
    }

    fn move_within_line(&mut self, off: i16) -> io::Result<()> {
        self.captured_out.push(CapturedOut::MoveWithinLine(off));
        Ok(())
    }

    fn print(&mut self, text: &str) -> io::Result<()> {
        let text = remove_control_chars(text.to_owned());

        self.captured_out.push(CapturedOut::Print(text));
        Ok(())
    }

    async fn poll_key(&mut self) -> io::Result<Option<Key>> {
        match self.golden_in.pop_front() {
            Some(ch) => Ok(Some(ch)),
            None => Ok(None),
        }
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

    fn size_chars(&self) -> io::Result<CharsXY> {
        Ok(self.size_chars)
    }

    fn size_pixels(&self) -> io::Result<SizeInPixels> {
        match self.size_pixels {
            Some(size) => Ok(size),
            None => Err(io::Error::new(io::ErrorKind::Other, "Graphical console size not yet set")),
        }
    }

    fn write(&mut self, text: &str) -> io::Result<()> {
        let text = remove_control_chars(text.to_owned());

        self.captured_out.push(CapturedOut::Write(text));
        Ok(())
    }

    fn draw_circle(&mut self, xy: PixelsXY, r: u16) -> io::Result<()> {
        self.captured_out.push(CapturedOut::DrawCircle(xy, r));
        Ok(())
    }

    fn draw_circle_filled(&mut self, xy: PixelsXY, r: u16) -> io::Result<()> {
        self.captured_out.push(CapturedOut::DrawCircleFilled(xy, r));
        Ok(())
    }

    fn draw_line(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        self.captured_out.push(CapturedOut::DrawLine(x1y1, x2y2));
        Ok(())
    }

    fn draw_pixel(&mut self, xy: PixelsXY) -> io::Result<()> {
        self.captured_out.push(CapturedOut::DrawPixel(xy));
        Ok(())
    }

    fn draw_rect(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        self.captured_out.push(CapturedOut::DrawRect(x1y1, x2y2));
        Ok(())
    }

    fn draw_rect_filled(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        self.captured_out.push(CapturedOut::DrawRectFilled(x1y1, x2y2));
        Ok(())
    }

    fn sync_now(&mut self) -> io::Result<()> {
        self.captured_out.push(CapturedOut::SyncNow);
        Ok(())
    }

    fn set_sync(&mut self, enabled: bool) -> io::Result<bool> {
        let mut previous = true;
        for o in self.captured_out.iter().rev() {
            if let CapturedOut::SetSync(e) = o {
                previous = *e;
                break;
            }
        }
        self.captured_out.push(CapturedOut::SetSync(enabled));
        Ok(previous)
    }
}

/// Flattens the captured output into a single string resembling what would be shown in the
/// console for ease of testing.
pub fn flatten_output(captured_out: Vec<CapturedOut>) -> String {
    let mut flattened = String::new();
    for out in captured_out {
        match out {
            CapturedOut::Write(bs) => flattened.push_str(&bs),
            CapturedOut::Print(s) => flattened.push_str(&s),
            _ => (),
        }
    }
    flattened
}

/// A stored program that exposes golden contents and accepts new content from the console when
/// edits are requested.
#[derive(Default)]
pub struct RecordedProgram {
    name: Option<String>,
    content: String,
    dirty: bool,
}

#[async_trait(?Send)]
impl Program for RecordedProgram {
    fn is_dirty(&self) -> bool {
        self.dirty
    }

    async fn edit(&mut self, console: &mut dyn Console) -> io::Result<()> {
        let append = console::read_line(console, "", "", None).await?;
        self.content.push_str(&append);
        self.content.push('\n');
        self.dirty = true;
        Ok(())
    }

    fn load(&mut self, name: Option<&str>, text: &str) {
        self.name = name.map(str::to_owned);
        text.clone_into(&mut self.content);
        self.dirty = false;
    }

    fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    fn set_name(&mut self, name: &str) {
        self.name = Some(name.to_owned());
        self.dirty = false;
    }

    fn text(&self) -> String {
        self.content.clone()
    }
}

/// Builder pattern to prepare an EndBASIC machine for testing purposes.
#[must_use]
pub struct Tester {
    console: Rc<RefCell<MockConsole>>,
    storage: Rc<RefCell<Storage>>,
    program: Rc<RefCell<RecordedProgram>>,
    machine: Machine,
}

impl Default for Tester {
    /// Creates a new tester for a fully-equipped (interactive) machine.
    fn default() -> Self {
        let console = Rc::from(RefCell::from(MockConsole::default()));
        let program = Rc::from(RefCell::from(RecordedProgram::default()));

        // Default to the pins set that always returns errors.  We could have implemented a set of
        // fake pins here to track GPIO state changes in a nicer way, similar to how we track all
        // other machine state... but the GPIO module already implements its own mocking feature.
        // The mocking feature is necessary for integration testing in any case, so we just use that
        // everywhere instead of having yet another implementation in this module.
        let gpio_pins = Rc::from(RefCell::from(gpio::NoopPins::default()));

        let mut builder = crate::MachineBuilder::default()
            .with_console(console.clone())
            .with_gpio_pins(gpio_pins)
            .make_interactive()
            .with_program(program.clone());

        // Grab access to the machine's storage subsystem before we lose track of it, as we will
        // need this to check its state.
        let storage = builder.get_storage();

        let machine = builder.build().unwrap();

        Self { console, storage, program, machine }
    }
}

impl Tester {
    /// Creates a new tester with an empty `Machine`.
    pub fn empty() -> Self {
        let console = Rc::from(RefCell::from(MockConsole::default()));
        let storage = Rc::from(RefCell::from(Storage::default()));
        let program = Rc::from(RefCell::from(RecordedProgram::default()));

        let machine = Machine::default();

        Self { console, storage, program, machine }
    }

    /// Registers the given builtin command into the machine, which must not yet be registered.
    pub fn add_callable(mut self, callable: Rc<dyn Callable>) -> Self {
        self.machine.add_callable(callable);
        self
    }

    /// Adds the `golden_in` characters as console input.
    pub fn add_input_chars(self, golden_in: &str) -> Self {
        self.console.borrow_mut().add_input_chars(golden_in);
        self
    }

    /// Adds a bunch of keys as golden input to the console.
    pub fn add_input_keys(self, keys: &[Key]) -> Self {
        self.console.borrow_mut().add_input_keys(keys);
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

    /// Gets the recorded program from the tester.
    ///
    /// This method should generally not be used.  Its primary utility is to hook
    /// externally-instantiated commands into the testing features.
    pub fn get_program(&self) -> Rc<RefCell<RecordedProgram>> {
        self.program.clone()
    }

    /// Gets the storage subsystem from the tester.
    ///
    /// This method should generally not be used.  Its primary utility is to hook
    /// externally-instantiated commands into the testing features.
    pub fn get_storage(&self) -> Rc<RefCell<Storage>> {
        self.storage.clone()
    }

    /// Sets a variable to an initial value.
    pub fn set_var(mut self, name: &str, value: Value) -> Self {
        self.machine.get_mut_symbols().set_var(&VarRef::new(name, None), value).unwrap();
        self
    }

    /// Sets the initial name of the recorded program to `name` (if any) and its contents to `text`.
    /// Can only be called once and `text` must not be empty.
    pub fn set_program(self, name: Option<&str>, text: &str) -> Self {
        assert!(!text.is_empty());
        {
            let mut program = self.program.borrow_mut();
            assert!(program.text().is_empty());
            program.load(name, text);
        }
        self
    }

    /// Creates or overwrites a file in the storage medium.
    pub fn write_file(self, name: &str, content: &str) -> Self {
        block_on(self.storage.borrow_mut().put(name, content)).unwrap();
        self
    }

    /// Runs `script` in the configured machine and returns a `Checker` object to validate
    /// expectations about the execution.
    pub fn run<S: Into<String>>(&mut self, script: S) -> Checker {
        let result = block_on(self.machine.exec(&mut script.into().as_bytes()));
        Checker::new(self, result)
    }

    /// Runs `scripts` in the configured machine and returns a `Checker` object to validate
    /// expectations about the execution.
    ///
    /// The first entry in `scripts` to fail aborts execution and allows checking the result
    /// of that specific invocation.
    ///
    /// This is useful when compared to `run` because `Machine::exec` compiles the script as one
    /// unit and thus compilation errors may prevent validating other operations later on.
    pub fn run_n(&mut self, scripts: &[&str]) -> Checker {
        let mut result = Ok(StopReason::Eof);
        for script in scripts {
            result = block_on(self.machine.exec(&mut script.as_bytes()));
            if result.is_err() {
                break;
            }
        }
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
    exp_drives: HashMap<String, String>,
    exp_program_name: Option<String>,
    exp_program_text: String,
    exp_arrays: HashMap<SymbolKey, Array>,
    exp_vars: HashMap<SymbolKey, Value>,
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
            exp_drives: HashMap::default(),
            exp_program_name: None,
            exp_program_text: String::new(),
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

    /// Expects the invocation to have erroneously terminated with the exact `message` during
    /// compilation.
    ///
    /// If not called, defaults to expecting that execution terminated due to EOF.  This or
    /// `expect_err` can only be called once.
    pub fn expect_compilation_err<S: Into<String>>(mut self, message: S) -> Self {
        let message = message.into();
        assert_eq!(Ok(StopReason::Eof), self.exp_result);
        self.exp_result = Err(message.clone());
        self
    }

    /// Expects the invocation to have erroneously terminated with the exact `message`.
    ///
    /// If not called, defaults to expecting that execution terminated due to EOF.  This or
    /// `expect_err` can only be called once.
    pub fn expect_err<S: Into<String>>(mut self, message: S) -> Self {
        let message = message.into();
        assert_eq!(Ok(StopReason::Eof), self.exp_result);
        self.exp_result = Err(message.clone());
        self
    }

    /// Adds the `name` array as an array to expect in the final state of the machine.  The array
    /// will be tested to have the same `subtype` and `dimensions`, as well as specific `contents`.
    /// The contents are provided as a collection of subscripts/value pairs to assign to the
    /// expected array.
    pub fn expect_array<S: AsRef<str>>(
        mut self,
        name: S,
        subtype: ExprType,
        dimensions: &[usize],
        contents: Vec<(&[i32], Value)>,
    ) -> Self {
        let key = SymbolKey::from(name);
        assert!(!self.exp_arrays.contains_key(&key));
        let mut array = Array::new(subtype, dimensions.to_owned());
        for (subscripts, value) in contents.into_iter() {
            array.assign(subscripts, value).unwrap();
        }
        self.exp_arrays.insert(key, array);
        self
    }

    /// Adds the `name` array as an array to expect in the final state of the machine.  The array
    /// will be tested to have the same `subtype` and only one dimension with `contents`.
    pub fn expect_array_simple<S: AsRef<str>>(
        mut self,
        name: S,
        subtype: ExprType,
        contents: Vec<Value>,
    ) -> Self {
        let key = SymbolKey::from(name);
        assert!(!self.exp_arrays.contains_key(&key));
        let mut array = Array::new(subtype, vec![contents.len()]);
        for (i, value) in contents.into_iter().enumerate() {
            array.assign(&[i as i32], value).unwrap();
        }
        self.exp_arrays.insert(key, array);
        self
    }

    /// Adds tracking for all the side-effects of a clear operation on the machine.
    pub fn expect_clear(mut self) -> Self {
        self.exp_output.append(&mut vec![
            CapturedOut::LeaveAlt,
            CapturedOut::SetColor(None, None),
            CapturedOut::ShowCursor,
            CapturedOut::SetSync(true),
        ]);
        self
    }

    /// Adds a file to expect in the drive with a `name` and specific `content`.
    ///
    /// `name` must be the absolute path to the file that is expected, including the drive name.
    pub fn expect_file<N: Into<String>, C: Into<String>>(mut self, name: N, content: C) -> Self {
        let name = name.into();
        assert!(!self.exp_drives.contains_key(&name));
        self.exp_drives.insert(name, content.into());
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

    /// Sets the expected name of the stored program to `name` and its contents to `text`.  Can only
    /// be called once and `text` must not be empty.
    pub fn expect_program<S1: Into<String>, S2: Into<String>>(
        mut self,
        name: Option<S1>,
        text: S2,
    ) -> Self {
        assert!(self.exp_program_text.is_empty());
        let text = text.into();
        assert!(!text.is_empty());
        self.exp_program_name = name.map(|x| x.into());
        self.exp_program_text = text;
        self
    }

    /// Adds the `name`/`value` pair as a variable to expect in the final state of the machine.
    pub fn expect_var<S: AsRef<str>, V: Into<Value>>(mut self, name: S, value: V) -> Self {
        let key = SymbolKey::from(name);
        assert!(!self.exp_vars.contains_key(&key));
        self.exp_vars.insert(key, value.into());
        self
    }

    /// Takes the captured output for separate analysis.
    #[must_use]
    pub fn take_captured_out(&mut self) -> Vec<CapturedOut> {
        assert!(
            self.exp_output.is_empty(),
            "Cannot take output if we are already expecting prints because the test would fail"
        );
        self.tester.console.borrow_mut().take_captured_out()
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
                    arrays.insert(name.clone(), array.clone());
                }
                Symbol::Callable(_) => {
                    // We currently don't support user-defined callables at runtime so there is no
                    // need to validate anything about them.
                }
                Symbol::Variable(value) => {
                    vars.insert(name.clone(), value.clone());
                }
            }
        }

        let drive_contents = {
            let mut files = HashMap::new();
            let storage = self.tester.storage.borrow();
            for (drive_name, target) in storage.mounted().iter() {
                if target.starts_with("cloud://") {
                    // TODO(jmmv): Verifying the cloud drives is hard because we would need to mock
                    // out the requests issued by the checks below.  Ignore them for now.
                    continue;
                }

                let root = format!("{}:/", drive_name);
                for name in block_on(storage.enumerate(&root)).unwrap().dirents().keys() {
                    let path = format!("{}{}", root, name);
                    let content = block_on(storage.get(&path)).unwrap();
                    files.insert(path, content);
                }
            }
            files
        };

        assert_eq!(self.exp_vars, vars);
        assert_eq!(self.exp_arrays, arrays);
        assert_eq!(self.exp_output, self.tester.console.borrow().captured_out());
        assert_eq!(self.exp_program_name.as_deref(), self.tester.program.borrow().name());
        assert_eq!(self.exp_program_text, self.tester.program.borrow().text());
        assert_eq!(self.exp_drives, drive_contents);

        self.tester.console.borrow_mut().verify_all_used();
    }
}

/// Executes `stmt` on a default `Tester` instance and checks that it fails with `exp_error`.
pub fn check_stmt_err<S: Into<String>>(exp_error: S, stmt: &str) {
    Tester::default().run(stmt).expect_err(exp_error).check();
}

/// Executes `stmt` on a default `Tester` instance and checks that it fails with `exp_error`
/// during compilation.
pub fn check_stmt_compilation_err<S: Into<String>>(exp_error: S, stmt: &str) {
    Tester::default().run(stmt).expect_compilation_err(exp_error).check();
}

/// Executes `expr` on a scripting interpreter and ensures that the result is `exp_value`.
pub fn check_expr_ok<V: Into<Value>>(exp_value: V, expr: &str) {
    Tester::default()
        .run(format!("result = {}", expr))
        .expect_var("result", exp_value.into())
        .check();
}

/// Executes `expr` on a scripting interpreter and ensures that the result is `exp_value`.
///
/// Sets all `vars` before evaluating the expression so that the expression can contain variable
/// references.
pub fn check_expr_ok_with_vars<V: Into<Value>, VS: Into<Vec<(&'static str, Value)>>>(
    exp_value: V,
    expr: &str,
    vars: VS,
) {
    let vars = vars.into();

    let mut t = Tester::default();
    for var in vars.as_slice() {
        t = t.set_var(var.0, var.1.clone());
    }

    let mut c = t.run(format!("result = {}", expr));
    c = c.expect_var("result", exp_value.into());
    for var in vars.into_iter() {
        c = c.expect_var(var.0, var.1.clone());
    }
    c.check();
}

/// Executes `expr` on a scripting interpreter and ensures that evaluation fails with `exp_error`.
///
/// Note that `exp_error` is a literal exact match on the formatted error message returned by the
/// machine.
pub fn check_expr_error<S: Into<String>>(exp_error: S, expr: &str) {
    Tester::default().run(format!("result = {}", expr)).expect_err(exp_error).check();
}

/// Executes `expr` on a scripting interpreter and ensures that evaluation fails with `exp_error`
/// during compilation.
///
/// Note that `exp_error` is a literal exact match on the formatted error message returned by the
/// machine.
pub fn check_expr_compilation_error<S: Into<String>>(exp_error: S, expr: &str) {
    Tester::default().run(format!("result = {}", expr)).expect_compilation_err(exp_error).check();
}
