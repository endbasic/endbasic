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

//! The EndBASIC standard library.

use std::cell::RefCell;
use std::collections::HashMap;
use std::future::Future;
use std::io;
use std::pin::Pin;
use std::rc::Rc;

use async_channel::{Receiver, Sender, TryRecvError};
use endbasic_core::{
    CallError, Callable, CallableMetadata, Compiler, CompilerError, GlobalDef, Image, LineCol,
    StopReason, SymbolKey, Vm,
};

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
pub mod spi;
pub mod storage;
pub mod strings;
pub mod testutils;

/// Error types for callable execution.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Fails due to a callable-specific execution error.
    #[error("{0}")]
    CallError(#[from] CallError),

    /// Fails due to a program compilation error.
    #[error("{0}")]
    CompilerError(#[from] CompilerError),

    /// Fails due to an I/O error in the underlying runtime.
    #[error("{0}")]
    IoError(#[from] io::Error),

    /// Fails due to a runtime error at a specific source location.
    #[error("{0}: {1}")]
    RuntimeError(LineCol, String),

    /// Aborts execution due to an external break signal.
    #[error("Break")]
    Break,
}

/// Result type for callable execution.
pub type Result<T> = std::result::Result<T, Error>;

/// Trait for objects that maintain state that can be reset to defaults.
pub trait Clearable {
    /// Resets any state held by the object to default values.
    fn reset_state(&self);
}

/// Actions that callables can request the Machine to perform after an upcall returns.
///
/// Because callables don't have direct access to the Machine, they push requests onto an
/// action queue.  The Machine's exec loop drains this queue after each upcall, performing
/// any requested side effects before resuming execution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MachineAction {
    /// Reset all runtime state (variables, heap, clearables, last error).
    Clear,

    /// Switches execution to the given program.
    Run(String),
}

/// Signals that can be delivered to the machine.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Signal {
    /// Asks the machine to stop execution of the currently-running program.
    Break,
}

/// Type of the function used by the execution loop to yield execution.
pub type YieldNowFn = Box<dyn Fn() -> Pin<Box<dyn Future<Output = ()> + 'static>>>;

/// Executes an EndBASIC program and tracks its state.
pub struct Machine {
    compiler: Compiler,
    image: Image,
    vm: Vm,
    callables: HashMap<SymbolKey, Rc<dyn Callable>>,
    clearables: Vec<Box<dyn Clearable>>,
    actions: Rc<RefCell<Vec<MachineAction>>>,
    global_defs: Vec<GlobalDef>,
    console: Rc<RefCell<dyn console::Console>>,
    yield_now_fn: Option<YieldNowFn>,
    signals_chan: (Sender<Signal>, Receiver<Signal>),
}

impl Machine {
    /// Resets the state of the machine by clearing all variables.
    ///
    /// This clears the runtime state (variables, heap, last error), resets the compiler's symbol
    /// table, and starts with a fresh image.  The net effect is equivalent to starting a new machine
    /// session: all user variables and compiled bytecode are gone, but registered callables remain.
    pub fn clear(&mut self) {
        for clearable in self.clearables.as_slice() {
            clearable.reset_state();
        }
        self.vm.reset();
        self.compiler = Compiler::new(&self.callables, &self.global_defs)
            .expect("Compiler creation succeeded during Machine init; must also succeed here");
        self.image = Image::default();
    }

    fn run(&mut self, program: String) -> Result<()> {
        self.clear();
        self.compile(&mut program.as_bytes())
    }

    /// Consumes any pending signals so they don't affect future executions.
    pub fn drain_signals(&mut self) {
        while self.signals_chan.1.try_recv().is_ok() {
            // Do nothing.
        }
    }

    /// Returns true if execution should stop because we have hit a stop condition.
    fn should_stop(&mut self) -> bool {
        match self.signals_chan.1.try_recv() {
            Ok(Signal::Break) => true,
            Err(TryRecvError::Empty) => false,
            Err(TryRecvError::Closed) => panic!("Channel unexpectedly closed"),
        }
    }

    /// Returns true if execution should stop after yielding to the host once.
    async fn should_stop_after_yield(&mut self) -> bool {
        if let Some(yield_now) = self.yield_now_fn.as_ref() {
            (yield_now)().await;
        }
        self.should_stop()
    }

    /// Compiles the code in `input` and _appends_ it to the current machine context.
    pub fn compile(&mut self, input: &mut dyn io::Read) -> Result<()> {
        self.compiler.compile_more(&mut self.image, input)?;
        Ok(())
    }

    /// Resumes (or starts) execution from the last compiled code.
    pub async fn exec(&mut self) -> Result<Option<i32>> {
        // TODO(jmmv): This "nested" flag is a huge hack to get EDIT/RUN to more-or-less work
        // with the new core.  It doesn't work great yet but it allows us to make tests pass.
        // This must be revised because there are some odd behavioral issues stemming from it.
        let mut nested = false;
        loop {
            match self.vm.exec(&self.image) {
                StopReason::Eof => break Ok(None),
                StopReason::End(code) => {
                    if !nested {
                        break Ok(Some(code.to_i32()));
                    }
                    nested = false;

                    if !code.is_success() {
                        self.console
                            .borrow_mut()
                            .print(&format!("Program exited with code {}", code.to_i32()))?;
                    }
                }
                StopReason::Exception(pos, msg) => {
                    return Err(Error::RuntimeError(pos, msg));
                }
                StopReason::Upcall(handler) => {
                    handler.invoke().await.map_err(|e| {
                        let (pos, message) = e.parts();
                        Error::RuntimeError(pos, message)
                    })?;

                    if self.should_stop() {
                        self.vm.interrupt(&self.image);
                        return Err(Error::Break);
                    }

                    let actions: Vec<MachineAction> = self.actions.borrow_mut().drain(..).collect();
                    for action in actions {
                        match action {
                            MachineAction::Clear => self.clear(),
                            MachineAction::Run(program) => {
                                self.run(program)?;
                                nested = true;
                            }
                        }
                    }
                }
                StopReason::Yield => {
                    if self.should_stop_after_yield().await {
                        self.vm.interrupt(&self.image);
                        return Err(Error::Break);
                    }
                }
            }
        }
    }
}

/// Builder pattern to construct an EndBASIC interpreter.
///
/// Unless otherwise specified, the interpreter is connected to a terminal-based console.
#[derive(Default)]
pub struct MachineBuilder {
    callables: HashMap<SymbolKey, Rc<dyn Callable>>,
    callables_metadata: Rc<RefCell<HashMap<SymbolKey, Rc<CallableMetadata>>>>,
    clearables: Vec<Box<dyn Clearable>>,
    console: Option<Rc<RefCell<dyn console::Console>>>,
    gpio_pins: Option<Rc<RefCell<dyn gpio::Pins>>>,
    sleep_fn: Option<exec::SleepFn>,
    actions: Rc<RefCell<Vec<MachineAction>>>,
    yield_now_fn: Option<YieldNowFn>,
    signals_chan: Option<(Sender<Signal>, Receiver<Signal>)>,
    global_defs: Vec<GlobalDef>,
}

impl MachineBuilder {
    /// Returns a shared reference to the machine's action queue.
    ///
    /// This is used by callables that need to request machine-level side effects (such as CLEAR).
    pub fn actions(&self) -> Rc<RefCell<Vec<MachineAction>>> {
        self.actions.clone()
    }

    /// Registers the given builtin callable, which must not yet be registered.
    pub fn add_callable(&mut self, callable: Rc<dyn Callable>) {
        let metadata = callable.metadata();
        let key = SymbolKey::from(metadata.name());

        let previous = self.callables.insert(key.clone(), callable);
        debug_assert!(previous.is_none(), "Cannot insert a callable twice");

        let previous = self.callables_metadata.borrow_mut().insert(key, metadata);
        debug_assert!(previous.is_none(), "Cannot insert callable metadata twice");
    }

    /// Returns metadata for all callables currently registered in the builder.
    pub fn callables_metadata(&self) -> Rc<RefCell<HashMap<SymbolKey, Rc<CallableMetadata>>>> {
        self.callables_metadata.clone()
    }

    /// Registers the given clearable.
    ///
    /// In the common case, functions and commands hold a reference to the out-of-machine state
    /// they interact with.  This state is invisible from here, but we may need to have access
    /// to it to reset it as part of the `clear` operation.  In those cases, such state must be
    /// registered via this hook.
    pub fn add_clearable(&mut self, clearable: Box<dyn Clearable>) {
        self.clearables.push(clearable);
    }

    /// Overrides the default terminal-based console with the given one.
    pub fn with_console(mut self, console: Rc<RefCell<dyn console::Console>>) -> Self {
        self.console = Some(console);
        self
    }

    /// Sets a global variable to an initial value.
    pub fn with_globals(mut self, defs: Vec<GlobalDef>) -> Self {
        self.global_defs.extend(defs);
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

    /// Overrides the default yielding function with the given one.
    pub fn with_yield_now_fn(mut self, yield_now_fn: YieldNowFn) -> Self {
        self.yield_now_fn = Some(yield_now_fn);
        self
    }

    /// Overrides the default signals channel with the given one.
    pub fn with_signals_chan(mut self, chan: (Sender<Signal>, Receiver<Signal>)) -> Self {
        self.signals_chan = Some(chan);
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
    pub fn build(mut self) -> Machine {
        let console = self.get_console();
        let gpio_pins = self.get_gpio_pins();

        let signals_chan = match self.signals_chan.take() {
            Some(pair) => pair,
            None => async_channel::unbounded(),
        };

        arrays::add_all(&mut self);
        console::add_all(&mut self, console.clone());
        gfx::add_all(&mut self, console.clone());
        data::add_all(&mut self);
        gpio::add_all(&mut self, gpio_pins);
        let sleep_fn = self.sleep_fn.take();
        exec::add_scripting(&mut self, sleep_fn);
        numerics::add_all(&mut self);
        strings::add_all(&mut self);

        Machine {
            compiler: Compiler::new(&self.callables, &self.global_defs)
                .expect("Injected globals must be valid"),
            image: Image::default(),
            vm: Vm::new(self.callables.clone()),
            callables: self.callables,
            clearables: self.clearables,
            actions: self.actions.clone(),
            global_defs: self.global_defs.clone(),
            console,
            yield_now_fn: self.yield_now_fn.take(),
            signals_chan,
        }
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
    storage: Option<Rc<RefCell<storage::Storage>>>,
}

impl InteractiveMachineBuilder {
    /// Constructs an interactive machine builder from a non-interactive builder.
    fn from(builder: MachineBuilder) -> Self {
        InteractiveMachineBuilder { builder, program: None, storage: None }
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
        if self.storage.is_none() {
            self.storage = Some(Rc::from(RefCell::from(storage::Storage::default())));
        }
        self.storage.clone().unwrap()
    }

    /// Overrides the default stored program with the given one.
    pub fn with_program(mut self, program: Rc<RefCell<dyn program::Program>>) -> Self {
        self.program = Some(program);
        self
    }

    /// Overrides the default storage subsystem with the given one.
    pub fn with_storage(mut self, storage: Rc<RefCell<storage::Storage>>) -> Self {
        self.storage = Some(storage);
        self
    }

    /// Builds the interpreter.
    pub fn build(mut self) -> Machine {
        let console = self.builder.get_console();
        let program = self.get_program();
        let storage = self.get_storage();

        exec::add_interactive(&mut self.builder);
        program::add_all(&mut self.builder, program, console.clone(), storage.clone());
        storage::add_all(&mut self.builder, console.clone(), storage);
        help::add_all(&mut self.builder, console);

        self.builder.build()
    }
}
