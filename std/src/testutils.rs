// EndBASIC
// Copyright 2021 Julio Merino
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

//! Test utilities for consumers of the EndBASIC interpreter.

use crate::console::{
    self, CharsXY, ClearType, Console, Key, PixelsXY, SizeInPixels, remove_control_chars,
};
use crate::program::Program;
use crate::storage::Storage;
use crate::{Machine, MachineBuilder, Signal, gpio};
use async_channel::{Receiver, Sender};
use async_trait::async_trait;
use endbasic_core::{
    Callable, ConstantDatum, ExprType, GetGlobalError, GlobalDef, GlobalDefKind, StopReason,
    SymbolKey,
};
use futures_lite::future::block_on;
use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::io;
use std::rc::Rc;
use std::result::Result as StdResult;
use std::str;

type CheckerResult = StdResult<Option<i32>, String>;

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

    /// Channel through which to send signals, if present.
    signals_tx: Option<Sender<Signal>>,
}

impl Default for MockConsole {
    fn default() -> Self {
        Self::new(None)
    }
}

impl MockConsole {
    /// Constructs a new mock console with a `signals_tx` channel.
    fn new(signals_tx: Option<Sender<Signal>>) -> Self {
        Self {
            golden_in: VecDeque::new(),
            captured_out: vec![],
            size_chars: CharsXY::new(u16::MAX, u16::MAX),
            size_pixels: None,
            interactive: false,
            signals_tx,
        }
    }

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
            Some(ch) => {
                if ch == Key::Interrupt
                    && let Some(signals_tx) = &self.signals_tx
                {
                    let _ = signals_tx.send(Signal::Break).await;
                }
                Ok(Some(ch))
            }
            None => Ok(None),
        }
    }

    async fn read_key(&mut self) -> io::Result<Key> {
        match self.golden_in.pop_front() {
            Some(ch) => {
                if ch == Key::Interrupt
                    && let Some(signals_tx) = &self.signals_tx
                {
                    let _ = signals_tx.send(Signal::Break).await;
                }
                Ok(ch)
            }
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
            None => Err(io::Error::other("Graphical console size not yet set")),
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
#[derive(Clone)]
pub struct Tester {
    console: Rc<RefCell<MockConsole>>,
    storage: Rc<RefCell<Storage>>,
    program: Rc<RefCell<RecordedProgram>>,
    callables: Vec<Rc<dyn Callable>>,
    global_defs: Vec<GlobalDef>,
    interactive: bool,
    signals_tx: Sender<Signal>,
    signals_rx: Receiver<Signal>,
}

impl Default for Tester {
    /// Creates a new tester for a fully-equipped (interactive) machine.
    fn default() -> Self {
        let (signals_tx, signals_rx) = async_channel::unbounded();
        let console = Rc::from(RefCell::from(MockConsole::new(Some(signals_tx.clone()))));
        let program = Rc::from(RefCell::from(RecordedProgram::default()));
        let storage = Rc::from(RefCell::from(Storage::default()));
        let callables = vec![];
        let global_defs = vec![];
        let interactive = true;

        Self {
            console,
            storage,
            program,
            callables,
            global_defs,
            interactive,
            signals_tx,
            signals_rx,
        }
    }
}

impl Tester {
    fn build_machine(
        console: Rc<RefCell<MockConsole>>,
        storage: Rc<RefCell<Storage>>,
        program: Rc<RefCell<RecordedProgram>>,
        callables: Vec<Rc<dyn Callable>>,
        global_defs: Vec<GlobalDef>,
        interactive: bool,
        signals_chan: (Sender<Signal>, Receiver<Signal>),
    ) -> Machine {
        // Default to the no-op pins that always return errors.  GPIO unit tests use MockPins
        // directly via `make_mock_machine` to validate operation; this Tester wiring is only used
        // for the error-path tests that go through the real (NoopPins) backend.
        let gpio_pins = Rc::from(RefCell::from(gpio::NoopPins::default()));
        let mut builder = MachineBuilder::default()
            .with_console(console)
            .with_globals(global_defs)
            .with_gpio_pins(gpio_pins)
            .with_signals_chan(signals_chan);

        for callable in callables {
            builder.add_callable(callable);
        }

        if interactive {
            builder.make_interactive().with_program(program).with_storage(storage).build()
        } else {
            builder.build()
        }
    }

    /// Creates a new tester with an empty `Machine`.
    pub fn empty() -> Self {
        Self { interactive: false, ..Self::default() }
    }

    /// Registers the given builtin command into the machine, which must not yet be registered.
    pub fn add_callable(mut self, callable: Rc<dyn Callable>) -> Self {
        self.callables.push(callable);
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

    /// Sets a global variable to an initial value.
    pub fn set_var<S: Into<String>, V: Into<ConstantDatum>>(mut self, name: S, value: V) -> Self {
        let value = value.into();
        self.global_defs.push(GlobalDef {
            name: name.into(),
            kind: GlobalDefKind::Scalar {
                etype: match &value {
                    ConstantDatum::Boolean(..) => ExprType::Boolean,
                    ConstantDatum::Double(..) => ExprType::Double,
                    ConstantDatum::Integer(..) => ExprType::Integer,
                    ConstantDatum::Text(..) => ExprType::Text,
                },
                initial_value: Some(value),
            },
        });
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
        block_on(self.storage.borrow_mut().put(name, content.as_bytes())).unwrap();
        self
    }

    /// Runs `script` in the configured machine and returns a `Checker` object to validate
    /// expectations about the execution.
    pub fn run<S: Into<String>>(&mut self, script: S) -> Checker<'_> {
        let machine = Self::build_machine(
            self.console.clone(),
            self.storage.clone(),
            self.program.clone(),
            self.callables.clone(),
            self.global_defs.clone(),
            self.interactive,
            (self.signals_tx.clone(), self.signals_rx.clone()),
        );
        let tester = TesterContinuation { tester: self, machine };
        tester.run(script)
    }

    /// Creates a continuation from the current tester state without running any code.
    pub fn continue_from_here(&self) -> TesterContinuation<'_> {
        let machine = Self::build_machine(
            self.console.clone(),
            self.storage.clone(),
            self.program.clone(),
            self.callables.clone(),
            self.global_defs.clone(),
            self.interactive,
            (self.signals_tx.clone(), self.signals_rx.clone()),
        );
        TesterContinuation { tester: self, machine }
    }

    /// Runs `scripts` in the configured machine and returns a `Checker` object to validate
    /// expectations about the execution.
    ///
    /// The first entry in `scripts` to fail aborts execution and allows checking the result
    /// of that specific invocation.
    ///
    /// This is useful when compared to `run` because `Machine::exec` compiles the script as one
    /// unit and thus compilation errors may prevent validating other operations later on.
    pub fn run_n(&mut self, scripts: &[&str]) -> Checker<'_> {
        let mut machine = Self::build_machine(
            self.console.clone(),
            self.storage.clone(),
            self.program.clone(),
            self.callables.clone(),
            self.global_defs.clone(),
            self.interactive,
            (self.signals_tx.clone(), self.signals_rx.clone()),
        );
        let mut result = Ok(None);
        for script in scripts {
            match machine.compile(&mut script.as_bytes()) {
                Ok(()) => (),
                Err(e) => {
                    result = Err(format!("{}", e));
                    break;
                }
            }
            result = block_on(machine.exec()).map_err(|e| format!("{}", e));
            if result.is_err() {
                break;
            }
        }
        Checker::new(self, machine, result)
    }
}

/// A tester that allows continuing a previous check.
///
/// This differs from `Tester` in that it provides direct access to the machine, because
/// the machine has already been built at this point.
pub struct TesterContinuation<'a> {
    tester: &'a Tester,
    machine: Machine,
}

impl<'a> TesterContinuation<'a> {
    /// Returns a mutable reference to the machine inside this continuation.
    pub fn get_machine(&mut self) -> &mut Machine {
        &mut self.machine
    }

    /// Runs `script` in the configured machine and returns a `Checker` object to validate
    /// expectations about the execution.
    pub fn run<S: Into<String>>(mut self, script: S) -> Checker<'a> {
        let result = match self.machine.compile(&mut script.into().as_bytes()) {
            Ok(()) => block_on(self.machine.exec()).map_err(|e| format!("{}", e)),
            Err(e) => Err(format!("{}", e)),
        };
        Checker::new(self.tester, self.machine, result)
    }

    /// Clears the state of the machine.
    pub fn clear(mut self) -> Self {
        self.machine.clear();
        self
    }
}

/// Captures the expected post-execution shape and values of an array.
struct ExpArray {
    /// Expected type of each array element.
    subtype: ExprType,

    /// Expected length of every array dimension in declaration order.
    dimensions: Vec<usize>,

    /// Sparse collection of expected element values indexed by subscripts.
    ///
    /// Any in-bounds position not listed here is expected to contain the default value for
    /// `subtype`.
    contents: Vec<(Vec<i32>, ConstantDatum)>,
}

/// Captures expectations about the execution of a command and validates them.
#[must_use]
pub struct Checker<'a> {
    tester: &'a Tester,
    machine: Machine,
    result: CheckerResult,
    exp_result: CheckerResult,
    exp_output: Vec<CapturedOut>,
    exp_drives: HashMap<String, String>,
    exp_program_name: Option<String>,
    exp_program_text: String,
    exp_arrays: HashMap<SymbolKey, ExpArray>,
    exp_vars: HashMap<SymbolKey, ConstantDatum>,
}

impl<'a> Checker<'a> {
    /// Creates a new checker with default expectations based on the results of an execution.
    ///
    /// The default expectations are that the execution ran through completion and that it did not
    /// have any side-effects.
    fn new(tester: &'a Tester, machine: Machine, result: CheckerResult) -> Self {
        Self {
            tester,
            machine,
            result,
            exp_result: Ok(None),
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
        self.exp_result = Ok(match stop_reason {
            StopReason::End(code) => Some(code.to_i32()),
            StopReason::Eof => None,
            StopReason::Exception(_, _) | StopReason::UpcallAsync(_) | StopReason::Yield => {
                unreachable!()
            }
        });
        self
    }

    /// Expects the invocation to have erroneously terminated with the exact `message` during
    /// compilation.
    ///
    /// If not called, defaults to expecting that execution terminated due to EOF.  This or
    /// `expect_err` can only be called once.
    pub fn expect_compilation_err<S: Into<String>>(mut self, message: S) -> Self {
        self.exp_result = Err(message.into());
        self
    }

    /// Expects the invocation to have erroneously terminated with the exact `message`.
    ///
    /// If not called, defaults to expecting that execution terminated due to EOF.  This or
    /// `expect_err` can only be called once.
    pub fn expect_err<S: Into<String>>(mut self, message: S) -> Self {
        self.exp_result = Err(message.into());
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
        contents: Vec<(Vec<i32>, ConstantDatum)>,
    ) -> Self {
        let key = SymbolKey::from(name);
        assert!(!self.exp_arrays.contains_key(&key));
        self.exp_arrays
            .insert(key, ExpArray { subtype, dimensions: dimensions.to_vec(), contents });
        self
    }

    /// Adds the `name` array as an array to expect in the final state of the machine.  The array
    /// will be tested to have the same `subtype` and only one dimension with `contents`.
    pub fn expect_array_simple<S: AsRef<str>>(
        mut self,
        name: S,
        subtype: ExprType,
        contents: Vec<ConstantDatum>,
    ) -> Self {
        let key = SymbolKey::from(name);
        assert!(!self.exp_arrays.contains_key(&key));
        let mut exp_array = Vec::with_capacity(contents.len());
        for (i, value) in contents.into_iter().enumerate() {
            exp_array.push((vec![i as i32], value));
        }
        self.exp_arrays.insert(
            key,
            ExpArray { subtype, dimensions: vec![exp_array.len()], contents: exp_array },
        );
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
    pub fn expect_var<S: AsRef<str>, V: Into<ConstantDatum>>(mut self, name: S, value: V) -> Self {
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

    fn query_array_element(&self, name: &SymbolKey, subscripts: &[i32]) -> Option<ConstantDatum> {
        match self.machine.vm.get_global_array(&self.machine.image, name, subscripts) {
            Ok(Some(value)) => Some(value),
            Ok(None) => self
                .machine
                .vm
                .get_program_array(&self.machine.image, name, subscripts)
                .unwrap_or_else(|e| panic!("Expected array {} has wrong shape: {}", name, e)),
            Err(e) => panic!("Expected array {} has wrong shape: {}", name, e),
        }
    }

    fn check_array_dims(&self, name: &SymbolKey, dimensions: &[usize]) {
        if dimensions.is_empty() {
            panic!("Expected array {} must have at least one dimension", name);
        }

        let mut subscripts = vec![0; dimensions.len()];
        for i in 0..dimensions.len() {
            subscripts[i] = dimensions[i] as i32;
            match self.machine.vm.get_global_array(&self.machine.image, name, &subscripts) {
                Err(GetGlobalError::SubscriptOutOfBounds(_)) => (),
                Ok(None) => {
                    match self.machine.vm.get_program_array(&self.machine.image, name, &subscripts)
                    {
                        Err(GetGlobalError::SubscriptOutOfBounds(_)) => (),
                        Ok(Some(_)) => panic!(
                            "Expected array {} dimension {} to be {} but found larger",
                            name, i, dimensions[i]
                        ),
                        Ok(None) => panic!("Expected array {} not defined", name),
                        Err(e) => panic!("Expected array {} has wrong shape: {}", name, e),
                    }
                }
                Ok(Some(_)) => panic!(
                    "Expected array {} dimension {} to be {} but found larger",
                    name, i, dimensions[i]
                ),
                Err(e) => panic!("Expected array {} has wrong shape: {}", name, e),
            }
            subscripts[i] = 0;
        }
    }

    fn check_array(&self, name: &SymbolKey, exp_array: &ExpArray) {
        let mut exp_contents = HashMap::with_capacity(exp_array.contents.len());
        for (subscripts, value) in exp_array.contents.iter() {
            assert_eq!(
                exp_array.dimensions.len(),
                subscripts.len(),
                "Expected array {} has wrong number of subscripts",
                name
            );
            for (i, subscript) in subscripts.iter().enumerate() {
                assert!(
                    *subscript >= 0 && *subscript < exp_array.dimensions[i] as i32,
                    "Expected array {} has out-of-bounds subscript {} at dimension {}",
                    name,
                    subscript,
                    i
                );
            }
            let previous = exp_contents.insert(subscripts.clone(), value.clone());
            assert!(previous.is_none(), "Expected array {} has duplicate subscripts", name);
        }

        let default_value = match exp_array.subtype {
            ExprType::Boolean => ConstantDatum::Boolean(false),
            ExprType::Double => ConstantDatum::Double(0.0),
            ExprType::Integer => ConstantDatum::Integer(0),
            ExprType::Text => ConstantDatum::Text(String::new()),
        };

        let mut subscripts = vec![0; exp_array.dimensions.len()];
        loop {
            let value = self
                .query_array_element(name, &subscripts)
                .unwrap_or_else(|| panic!("Expected array {} not defined", name));
            assert_eq!(
                exp_contents.get(&subscripts).unwrap_or(&default_value),
                &value,
                "Expected array {} at {:?} has wrong value",
                name,
                subscripts
            );

            let mut i = 0;
            while i < subscripts.len() {
                subscripts[i] += 1;
                if subscripts[i] < exp_array.dimensions[i] as i32 {
                    break;
                }
                subscripts[i] = 0;
                i += 1;
            }
            if i == subscripts.len() {
                break;
            }
        }

        self.check_array_dims(name, &exp_array.dimensions);
    }

    /// Validates all expectations.
    pub fn check(self) -> TesterContinuation<'a> {
        assert_eq!(self.exp_result, self.result);

        for (name, exp_value) in self.exp_vars.iter() {
            let value = match self.machine.vm.get_global(&self.machine.image, name) {
                Ok(Some(value)) => Some(value),
                Ok(None) => {
                    self.machine.vm.get_program(&self.machine.image, name).unwrap_or_else(|e| {
                        panic!("Expected variable {} has wrong shape: {}", name, e)
                    })
                }
                Err(e) => panic!("Expected variable {} has wrong shape: {}", name, e),
            };
            let value = value.unwrap_or_else(|| panic!("Expected variable {} not defined", name));
            assert_eq!(exp_value, &value, "Expected variable {} has wrong value", name);
        }

        for (name, exp_array) in self.exp_arrays.iter() {
            self.check_array(name, exp_array);
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
                    let content = String::from_utf8(content).unwrap();
                    files.insert(path, content);
                }
            }
            files
        };

        assert_eq!(self.exp_output, self.tester.console.borrow().captured_out());
        assert_eq!(self.exp_program_name.as_deref(), self.tester.program.borrow().name());
        assert_eq!(self.exp_program_text, self.tester.program.borrow().text());
        assert_eq!(self.exp_drives, drive_contents);

        TesterContinuation { tester: self.tester, machine: self.machine }
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
pub fn check_expr_ok<V: Into<ConstantDatum>>(exp_value: V, expr: &str) {
    let exp_value = exp_value.into();
    Tester::default().run(format!("result = {}", expr)).expect_var("result", exp_value).check();
}

/// Executes `expr` on a scripting interpreter and ensures that the result is `exp_value`.
///
/// Sets all `vars` before evaluating the expression so that the expression can contain variable
/// references.
pub fn check_expr_ok_with_vars<
    V: Into<ConstantDatum>,
    VS: Into<Vec<(&'static str, ConstantDatum)>>,
>(
    exp_value: V,
    expr: &str,
    vars: VS,
) {
    let vars = vars.into();

    let mut input = String::new();
    for (name, value) in vars.as_slice() {
        input.push_str(name);
        input.push_str(" = ");
        input.push_str(&value.as_source());
        input.push_str(": ");
    }
    input.push_str(&format!("result = {}", expr));

    let exp_value = exp_value.into();

    let mut t = Tester::default();
    let mut c = t.run(input);
    c = c.expect_var("result", exp_value);
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
