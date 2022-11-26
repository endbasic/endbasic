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

//! Execution engine for EndBASIC programs.

use crate::ast::*;
use crate::bytecode::*;
use crate::compiler;
use crate::eval;
use crate::parser;
use crate::reader::LineCol;
use crate::syms::{CallError, CallableMetadata, Command, Function, Symbol, Symbols};
use crate::value;
use async_channel::{Receiver, Sender, TryRecvError};
use std::future::Future;
use std::io;
use std::pin::Pin;
use std::rc::Rc;

/// Execution errors.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Compilation error during execution.
    #[error("{0}")]
    CompilerError(#[from] compiler::Error),

    /// Evaluation error during execution.
    #[error("{0}")]
    EvalError(#[from] eval::Error),

    /// I/O error during execution.
    #[error("{0}")]
    IoError(#[from] io::Error),

    /// Hack to support errors that arise from within a program that is `RUN`.
    // TODO(jmmv): Consider unifying `CallError` with `exec::Error`.
    #[error("{0}")]
    NestedError(String),

    /// Parsing error during execution.
    #[error("{0}")]
    ParseError(#[from] parser::Error),

    /// Syntax error.
    #[error("{}:{}: {}", .0.line, .0.col, .1)]
    SyntaxError(LineCol, String),

    /// Value computation error during execution.
    #[error("{0}")]
    ValueError(value::Error),
}

impl Error {
    /// Annotates a call evaluation error with the command's metadata.
    // TODO(jmmv): This is a hack to support the transition to a better Command abstraction within
    // Symbols and exists to minimize the amount of impacted tests.  Should be removed and/or
    // somehow unified with the equivalent function in eval::Error.
    pub(crate) fn from_call_error(md: &CallableMetadata, e: CallError, pos: LineCol) -> Self {
        match e {
            CallError::ArgumentError(pos2, e) => Self::SyntaxError(
                pos,
                format!("In call to {}: {}:{}: {}", md.name(), pos2.line, pos2.col, e),
            ),
            CallError::EvalError(e) => Self::EvalError(e),
            CallError::InternalError(pos2, e) => Self::SyntaxError(
                pos,
                format!("In call to {}: {}:{}: {}", md.name(), pos2.line, pos2.col, e),
            ),
            CallError::IoError(e) => Self::IoError(io::Error::new(
                e.kind(),
                format!("{}:{}: In call to {}: {}", pos.line, pos.col, md.name(), e),
            )),
            CallError::NestedError(e) => Self::NestedError(e),
            CallError::SyntaxError if md.syntax().is_empty() => {
                Self::SyntaxError(pos, format!("In call to {}: expected no arguments", md.name()))
            }
            CallError::SyntaxError => Self::SyntaxError(
                pos,
                format!("In call to {}: expected {}", md.name(), md.syntax()),
            ),
        }
    }

    /// Annotates a value computation error with a position.
    fn from_value_error(e: value::Error, pos: LineCol) -> Self {
        eval::Error::from_value_error(e, pos).into()
    }

    /// Creates a position-less value computation error.
    // TODO(jmmv): This only exists because of some public operations in `Machine` that operate
    // "out of band".  We should probably remove those, put them elsewhere, and/or make them return
    // a different error type rather than weakening what we store in `Error`.
    fn from_value_error_without_pos(e: value::Error) -> Self {
        Self::ValueError(e)
    }

    /// Returns true if this type of error can be caught by `ON ERROR`.
    fn is_catchable(&self) -> bool {
        match self {
            Error::CompilerError(_) => false,
            Error::EvalError(_) => true,
            Error::IoError(_) => true,
            Error::NestedError(_) => false,
            Error::ParseError(_) => false,
            Error::SyntaxError(..) => true,
            Error::ValueError(_) => false,
        }
    }
}

/// Result for execution return values.
pub type Result<T> = std::result::Result<T, Error>;

/// Instantiates a new `Err(Error::SyntaxError(...))` from a message.  Syntactic sugar.
fn new_syntax_error<T, S: Into<String>>(pos: LineCol, message: S) -> Result<T> {
    Err(Error::SyntaxError(pos, message.into()))
}

/// Signals that can be delivered to the machine.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Signal {
    /// Asks the machine to stop execution of the currently-running program.
    Break,
}

/// Describes how the machine stopped execution while it was running a script via `exec()`.
#[derive(Clone, Debug, Eq, PartialEq)]
#[must_use]
pub enum StopReason {
    /// Execution terminates because the machine reached the end of the input.
    Eof,

    /// Execution terminated because the machine was asked to terminate with `END`.
    Exited(u8),

    /// Execution terminated because the machine received a break signal.
    Break,
}

impl StopReason {
    /// Converts the stop reason into a process exit code.
    pub fn as_exit_code(&self) -> i32 {
        match self {
            StopReason::Eof => 0,
            StopReason::Exited(i) => *i as i32,
            StopReason::Break => {
                // This mimics the behavior of typical Unix shells, which translate a signal to a
                // numerical exit code, but this is not accurate.  First, because a CTRL+C sequence
                // should be exposed as a SIGINT signal to whichever process is waiting for us, and
                // second because this is not meaningful on Windows.  But for now this will do.
                const SIGINT: i32 = 2;
                128 + SIGINT
            }
        }
    }
}

/// Trait for objects that maintain state that can be reset to defaults.
pub trait Clearable {
    /// Resets any state held by the object to default values.  `syms` contain the symbols of the
    /// machine before they are cleared, in case some state is held in them too.
    fn reset_state(&self, syms: &mut Symbols);
}

/// Type of the function used by the execution loop to yield execution.
pub type YieldNowFn = Box<dyn Fn() -> Pin<Box<dyn Future<Output = ()> + 'static>>>;

/// Machine state for the execution of an individual chunk of code.
struct Context {
    pc: Address,
    addr_stack: Vec<Address>,
    err_handler: ErrorHandlerSpan,
}

impl Default for Context {
    fn default() -> Self {
        Self { pc: 0, addr_stack: vec![], err_handler: ErrorHandlerSpan::None }
    }
}

/// Executes an EndBASIC program and tracks its state.
pub struct Machine {
    symbols: Symbols,
    clearables: Vec<Box<dyn Clearable>>,
    yield_now_fn: Option<YieldNowFn>,
    signals_chan: (Sender<Signal>, Receiver<Signal>),
    stop_reason: Option<StopReason>,
    data: Vec<Option<Value>>,
}

impl Default for Machine {
    fn default() -> Self {
        Self::with_signals_chan_and_yield_now_fn(async_channel::unbounded(), None)
    }
}

impl Machine {
    /// Constructs a new empty machine with the given signals communication channel.
    pub fn with_signals_chan(signals: (Sender<Signal>, Receiver<Signal>)) -> Self {
        Self {
            symbols: Symbols::default(),
            clearables: vec![],
            yield_now_fn: None,
            signals_chan: signals,
            stop_reason: None,
            data: vec![],
        }
    }

    /// Constructs a new empty machine with the given signals communication channel and yielding
    /// function.
    pub fn with_signals_chan_and_yield_now_fn(
        signals: (Sender<Signal>, Receiver<Signal>),
        yield_now_fn: Option<YieldNowFn>,
    ) -> Self {
        Self {
            symbols: Symbols::default(),
            clearables: vec![],
            yield_now_fn,
            signals_chan: signals,
            stop_reason: None,
            data: vec![],
        }
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

    /// Registers the given builtin command, which must not yet be registered.
    pub fn add_command(&mut self, command: Rc<dyn Command>) {
        self.symbols.add_command(command)
    }

    /// Registers the given builtin function, which must not yet be registered.
    pub fn add_function(&mut self, function: Rc<dyn Function>) {
        self.symbols.add_function(function)
    }

    /// Obtains a channel via which to send signals to the machine during execution.
    pub fn get_signals_tx(&self) -> Sender<Signal> {
        self.signals_chan.0.clone()
    }

    /// Resets the state of the machine by clearing all variable.
    pub fn clear(&mut self) {
        for clearable in self.clearables.as_slice() {
            clearable.reset_state(&mut self.symbols);
        }
        self.symbols.clear();
    }

    /// Obtains immutable access to the data values available during the *current* execution.
    pub fn get_data(&self) -> &[Option<Value>] {
        &self.data
    }

    /// Obtains immutable access to the state of the symbols.
    pub fn get_symbols(&self) -> &Symbols {
        &self.symbols
    }

    /// Obtains mutable access to the state of the symbols.
    pub fn get_mut_symbols(&mut self) -> &mut Symbols {
        &mut self.symbols
    }

    /// Retrieves the variable `name` as a boolean.  Fails if it is some other type or if it's not
    /// defined.
    pub fn get_var_as_bool(&self, name: &str) -> Result<bool> {
        match self
            .symbols
            .get_var(&VarRef::new(name, VarType::Boolean))
            .map_err(Error::from_value_error_without_pos)?
        {
            Value::Boolean(b) => Ok(*b),
            _ => panic!("Invalid type check in get()"),
        }
    }

    /// Retrieves the variable `name` as an integer.  Fails if it is some other type or if it's not
    /// defined.
    pub fn get_var_as_int(&self, name: &str) -> Result<i32> {
        match self
            .symbols
            .get_var(&VarRef::new(name, VarType::Integer))
            .map_err(Error::from_value_error_without_pos)?
        {
            Value::Integer(i) => Ok(*i),
            _ => panic!("Invalid type check in get()"),
        }
    }

    /// Retrieves the variable `name` as a string.  Fails if it is some other type or if it's not
    /// defined.
    pub fn get_var_as_string(&self, name: &str) -> Result<&str> {
        match self
            .symbols
            .get_var(&VarRef::new(name, VarType::Text))
            .map_err(Error::from_value_error_without_pos)?
        {
            Value::Text(s) => Ok(s),
            _ => panic!("Invalid type check in get()"),
        }
    }

    /// Returns true if execution should stop because we have hit a stop condition.
    async fn should_stop(&mut self) -> bool {
        if let Some(yield_now) = self.yield_now_fn.as_ref() {
            (yield_now)().await;
        }

        match self.signals_chan.1.try_recv() {
            Ok(Signal::Break) => self.stop_reason = Some(StopReason::Break),
            Err(TryRecvError::Empty) => (),
            Err(TryRecvError::Closed) => panic!("Channel unexpectedly closed"),
        }

        self.stop_reason.is_some()
    }

    /// Handles a variable assignment.
    async fn assign(&mut self, span: &AssignmentSpan) -> Result<()> {
        let value = span.expr.eval(&mut self.symbols).await?;
        self.symbols
            .set_var(&span.vref, value)
            .map_err(|e| Error::from_value_error(e, span.vref_pos))?;
        Ok(())
    }

    /// Handles an array assignment.
    async fn assign_array(&mut self, span: &ArrayAssignmentSpan) -> Result<()> {
        let mut ds = Vec::with_capacity(span.subscripts.len());
        for ss_expr in &span.subscripts {
            match ss_expr.eval(&mut self.symbols).await? {
                Value::Integer(i) => ds.push(i),
                v => {
                    return new_syntax_error(
                        ss_expr.start_pos(),
                        format!("Subscript {} must be an integer", v),
                    )
                }
            }
        }

        let value = span.expr.eval(&mut self.symbols).await?;

        match self
            .symbols
            .get_mut(&span.vref)
            .map_err(|e| Error::from_value_error(e, span.vref_pos))?
        {
            Some(Symbol::Array(array)) => {
                array.assign(&ds, value).map_err(|e| Error::from_value_error(e, span.vref_pos))?;
                Ok(())
            }
            Some(_) => new_syntax_error(
                span.vref_pos,
                format!("Cannot index non-array {}", span.vref.name()),
            ),
            None => new_syntax_error(
                span.vref_pos,
                format!("Cannot index undefined array {}", span.vref.name()),
            ),
        }
    }

    /// Handles a builtin call.
    async fn call_builtin(&mut self, span: &BuiltinCallSpan) -> Result<()> {
        let cmd = match self
            .symbols
            .get(&VarRef::new(&span.name, VarType::Auto))
            .map_err(|e| Error::from_value_error(e, span.name_pos))?
        {
            Some(Symbol::Command(cmd)) => cmd.clone(),
            Some(_) => {
                return new_syntax_error(span.name_pos, format!("{} is not a command", span.name))
            }
            None => {
                return new_syntax_error(span.name_pos, format!("Unknown builtin {}", span.name))
            }
        };
        cmd.exec(span, self)
            .await
            .map_err(|e| Error::from_call_error(cmd.metadata(), e, span.name_pos))
    }

    /// Handles an array definition.  The array must not yet exist, and the name may not overlap
    /// function or variable names.
    pub async fn dim_array(&mut self, span: &DimArraySpan) -> Result<()> {
        let mut ds = Vec::with_capacity(span.dimensions.len());
        for dim_expr in &span.dimensions {
            match dim_expr.eval(&mut self.symbols).await? {
                Value::Integer(i) => {
                    if i <= 0 {
                        return new_syntax_error(
                            dim_expr.start_pos(),
                            "Dimensions in DIM array must be positive",
                        );
                    }
                    ds.push(i as usize);
                }
                _ => {
                    return new_syntax_error(
                        dim_expr.start_pos(),
                        "Dimensions in DIM array must be integers",
                    )
                }
            }
        }
        self.symbols
            .dim_array(&span.name, span.subtype, ds)
            .map_err(|e| Error::from_value_error(e, span.name_pos))?;
        Ok(())
    }

    /// Consumes any pending signals so that they don't interfere with an upcoming execution.
    pub fn drain_signals(&mut self) {
        while self.signals_chan.1.try_recv().is_ok() {
            // Do nothing.
        }
    }

    /// Tells the machine to stop execution at the next statement boundary.
    async fn end(&mut self, span: &EndSpan) -> Result<()> {
        let code = match &span.code {
            None => 0,
            Some(expr) => match expr.eval(&mut self.symbols).await?.as_i32() {
                Ok(n) if n < 0 => {
                    return new_syntax_error(
                        expr.start_pos(),
                        "Exit code must be a positive integer".to_owned(),
                    );
                }
                Ok(n) if n >= 128 => {
                    return new_syntax_error(
                        expr.start_pos(),
                        "Exit code cannot be larger than 127".to_owned(),
                    );
                }
                Ok(n) => n as u8,
                Err(e) => return Err(Error::from_value_error(e, expr.start_pos())),
            },
        };
        self.stop_reason = Some(StopReason::Exited(code));
        Ok(())
    }

    /// Helper for `exec` that only worries about execution.  Errors are handled on the caller side
    /// depending on the `ON ERROR` handling policy that is currently configured.
    async fn exec_safe(&mut self, context: &mut Context, instrs: &[Instruction]) -> Result<()> {
        while context.pc < instrs.len() {
            if self.should_stop().await {
                break;
            }

            let instr = &instrs[context.pc];
            match instr {
                Instruction::ArrayAssignment(span) => {
                    self.assign_array(span).await?;
                    context.pc += 1;
                }

                Instruction::Assignment(span) => {
                    self.assign(span).await?;
                    context.pc += 1;
                }

                Instruction::BuiltinCall(span) => {
                    self.call_builtin(span).await?;
                    context.pc += 1;
                }

                Instruction::Call(span) => {
                    context.addr_stack.push(context.pc + 1);
                    context.pc = span.addr;
                }

                Instruction::Dim(span) => {
                    self.symbols
                        .dim(&span.name, span.vtype)
                        .map_err(|e| Error::from_value_error(e, span.name_pos))?;
                    context.pc += 1;
                }

                Instruction::DimArray(span) => {
                    self.dim_array(span).await?;
                    context.pc += 1;
                }

                Instruction::End(span) => {
                    self.end(span).await?;
                }

                Instruction::Jump(span) => {
                    context.pc = span.addr;
                }

                Instruction::JumpIfDefined(span) => {
                    if self.symbols.get_auto(&span.var).is_some() {
                        context.pc = span.addr;
                    } else {
                        context.pc += 1;
                    }
                }

                Instruction::JumpIfNotTrue(span) => {
                    match span.cond.eval(&mut self.symbols).await? {
                        Value::Boolean(true) => context.pc += 1,
                        Value::Boolean(false) => context.pc = span.addr,
                        _ => {
                            return new_syntax_error(span.cond.start_pos(), span.error_msg);
                        }
                    }
                }

                Instruction::Nop => {
                    context.pc += 1;
                }

                Instruction::Return(span) => match context.addr_stack.pop() {
                    Some(addr) => context.pc = addr,
                    None => {
                        return new_syntax_error(span.pos, "No address to return to".to_owned())
                    }
                },

                Instruction::SetErrorHandler(span) => {
                    context.err_handler = *span;
                    context.pc += 1;
                }
            }
        }

        Ok(())
    }

    /// Executes a program extracted from the `input` readable.
    ///
    /// Note that this does not consume `self`.  As a result, it is possible to execute multiple
    /// different programs on the same machine, all sharing state.
    pub async fn exec(&mut self, input: &mut dyn io::Read) -> Result<StopReason> {
        debug_assert!(self.stop_reason.is_none());

        // TODO(jmmv): It should be possible to make the parser return statements one at a time and
        // stream them to the compiler, instead of buffering everything in a vector.
        let stmts = parser::parse(input)?;
        let image = compiler::compile(stmts)?;

        assert!(self.data.is_empty());
        self.data = image.data;

        let mut context = Context::default();
        let mut result;
        loop {
            result = self.exec_safe(&mut context, &image.instrs).await;
            match result.as_ref() {
                Ok(()) => break,
                Err(e) if e.is_catchable() => {
                    let _ignore = self.symbols.unset("ERRMSG");
                    self.symbols
                        .set_var(
                            &VarRef::new("ERRMSG", VarType::Text),
                            Value::Text(format!("{}", e)),
                        )
                        .expect("Cannot fail; we have previously unset the variable.");

                    match context.err_handler {
                        ErrorHandlerSpan::Jump(addr) => context.pc = addr,
                        ErrorHandlerSpan::None => break,
                        ErrorHandlerSpan::ResumeNext => context.pc += 1,
                    }
                }
                Err(_) => break,
            }
        }

        self.data.clear();
        result?;

        Ok(self.stop_reason.take().unwrap_or(StopReason::Eof))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;
    use futures_lite::future::block_on;
    use std::cell::RefCell;
    use std::rc::Rc;

    /// A clearable that tracks whether it has been called.
    struct MockClearable {
        cleared: Rc<RefCell<bool>>,
    }

    impl Clearable for MockClearable {
        fn reset_state(&self, syms: &mut Symbols) {
            // Make sure we can see the symbols before they are cleared.
            assert!(syms.get_var(&VarRef::new("a", VarType::Boolean)).is_ok());
            assert!(syms.get_var(&VarRef::new("b", VarType::Integer)).is_ok());

            *self.cleared.borrow_mut() = true;
        }
    }

    #[test]
    fn test_clear() {
        let mut machine = Machine::default();

        let cleared = Rc::from(RefCell::from(false));
        let clearable = Box::from(MockClearable { cleared: cleared.clone() });
        machine.add_clearable(clearable);

        assert_eq!(
            StopReason::Eof,
            block_on(machine.exec(&mut b"a = TRUE: b = 1".as_ref())).expect("Execution failed")
        );
        assert!(machine.get_var_as_bool("a").is_ok());
        assert!(machine.get_var_as_int("b").is_ok());
        assert!(!*cleared.borrow());
        machine.clear();
        assert!(machine.get_var_as_bool("a").is_err());
        assert!(machine.get_var_as_int("b").is_err());
        assert!(*cleared.borrow());
    }

    #[test]
    fn test_get_data() {
        let captured_data = Rc::from(RefCell::from(vec![]));
        let mut machine = Machine::default();
        machine.add_command(GetDataCommand::new(captured_data.clone()));

        assert!(machine.get_data().is_empty());

        assert_eq!(
            StopReason::Eof,
            block_on(machine.exec(&mut b"DATA 3: GETDATA".as_ref())).unwrap()
        );
        assert!(machine.get_data().is_empty());
        assert_eq!(&[Some(Value::Integer(3))], captured_data.borrow().as_slice());

        assert_eq!(
            StopReason::Eof,
            block_on(
                machine.exec(
                    &mut b"
                        GETDATA
                        IF FALSE THEN: DATA 5: ELSE: DATA 6: END IF
                        WHILE FALSE: DATA 1: WEND
                        FOR i = 0 TO 0: DATA 0: NEXT
                    "
                    .as_ref()
                )
            )
            .unwrap()
        );
        assert!(machine.get_data().is_empty());
        assert_eq!(
            &[
                Some(Value::Integer(5)),
                Some(Value::Integer(6)),
                Some(Value::Integer(1)),
                Some(Value::Integer(0))
            ],
            captured_data.borrow().as_slice()
        );
    }

    #[test]
    fn test_get_data_is_empty_after_execution() {
        let mut machine = Machine::default();

        assert_eq!(StopReason::Eof, block_on(machine.exec(&mut b"DATA 3".as_ref())).unwrap());
        assert!(machine.get_data().is_empty());

        block_on(machine.exec(&mut b"DATA 3: abc".as_ref())).unwrap_err();
        assert!(machine.get_data().is_empty());

        block_on(machine.exec(&mut b"DATA 3: GOTO @foo".as_ref())).unwrap_err();
        assert!(machine.get_data().is_empty());
    }

    #[test]
    fn test_get_var_as_bool() {
        let mut machine = Machine::default();
        assert_eq!(
            StopReason::Eof,
            block_on(machine.exec(&mut b"a = TRUE: b = 1".as_ref())).expect("Execution failed")
        );
        assert!(machine.get_var_as_bool("a").expect("Failed to query a"));
        assert_eq!(
            "Incompatible types in b? reference",
            format!("{}", machine.get_var_as_bool("b").expect_err("Querying b succeeded"))
        );
        assert_eq!(
            "Undefined variable c",
            format!("{}", machine.get_var_as_bool("c").expect_err("Querying c succeeded"))
        );
    }

    #[test]
    fn test_get_var_as_int() {
        let mut machine = Machine::default();
        assert_eq!(
            StopReason::Eof,
            block_on(machine.exec(&mut b"a = 1: b = \"foo\"".as_ref())).expect("Execution failed")
        );
        assert_eq!(1, machine.get_var_as_int("a").expect("Failed to query a"));
        assert_eq!(
            "Incompatible types in b% reference",
            format!("{}", machine.get_var_as_int("b").expect_err("Querying b succeeded"))
        );
        assert_eq!(
            "Undefined variable c",
            format!("{}", machine.get_var_as_int("c").expect_err("Querying c succeeded"))
        );
    }

    #[test]
    fn test_get_var_as_string() {
        let mut machine = Machine::default();
        assert_eq!(
            StopReason::Eof,
            block_on(machine.exec(&mut b"a = \"foo\": b = FALSE".as_ref()))
                .expect("Execution failed")
        );
        assert_eq!("foo", machine.get_var_as_string("a").expect("Failed to query a"));
        assert_eq!(
            "Incompatible types in b$ reference",
            format!("{}", machine.get_var_as_string("b").expect_err("Querying b succeeded"))
        );
        assert_eq!(
            "Undefined variable c",
            format!("{}", machine.get_var_as_string("c").expect_err("Querying c succeeded"))
        );
    }

    /// Runs the `input` code on a new test machine.
    ///
    /// `golden_in` is the sequence of values to yield by `IN`.
    /// `expected_out` is updated with the sequence of calls to `OUT`.
    fn run(
        input: &str,
        golden_in: &'static [&'static str],
        captured_out: Rc<RefCell<Vec<String>>>,
    ) -> Result<StopReason> {
        let mut machine = Machine::default();
        machine.add_command(InCommand::new(Box::from(RefCell::from(golden_in.iter()))));
        machine.add_command(OutCommand::new(captured_out.clone()));
        machine.add_function(OutfFunction::new(captured_out));
        machine.add_function(RaiseFunction::new());
        machine.add_function(SumFunction::new());
        machine.add_function(TypeCheckFunction::new(Value::Boolean(true)));
        block_on(machine.exec(&mut input.as_bytes()))
    }

    /// Runs the `input` code on a new test machine and verifies its output.
    ///
    /// `golden_in` is the sequence of values to yield by `IN`.
    /// `expected_out` is the sequence of expected calls to `OUT`.
    fn do_ok_test(
        input: &str,
        golden_in: &'static [&'static str],
        expected_out: &'static [&'static str],
    ) {
        let captured_out = Rc::from(RefCell::from(vec![]));
        assert_eq!(
            StopReason::Eof,
            run(input, golden_in, captured_out.clone()).expect("Execution failed")
        );
        assert_eq!(expected_out, captured_out.borrow().as_slice());
    }

    /// Runs the `input` code on a new test machine and verifies that it fails with `expected_err`.
    ///
    /// Given that the code has side-effects until it fails, this follows the same process as
    /// `do_ok_test` regarding `golden_in` and `expected_out`.
    fn do_error_test(
        input: &str,
        golden_in: &'static [&'static str],
        expected_out: &'static [&'static str],
        expected_err: &str,
    ) {
        let captured_out = Rc::from(RefCell::from(vec![]));
        let err = run(input, golden_in, captured_out.clone()).expect_err("Execution did not fail");
        assert_eq!(expected_err, format!("{}", err));
        assert_eq!(expected_out, captured_out.borrow().as_slice());
    }

    /// Runs the `input` code on a new machine and verifies that it fails with `expected_err`.
    ///
    /// This is a syntactic wrapper over `do_error_test` to simplify those tests that are not
    /// expected to request any input nor generate any output.
    fn do_simple_error_test(input: &str, expected_err: &str) {
        do_error_test(input, &[], &[], expected_err);
    }

    #[test]
    fn test_array_assignment_ok() {
        do_ok_test("DIM a(3)\na(1) = 5 + 1\nOUT a(0); a(1); a(2)", &[], &["0 6 0"]);
        do_ok_test("DIM a(3) AS STRING\na$(1) = \"x\"\nOUT a(0); a(1); a$(2)", &[], &[" x "]);
        do_ok_test(
            "DIM a(3, 8, 2) AS BOOLEAN\na(3 - 3, 2 * 2, 1) = TRUE\nOUT a(0, 4, 1)",
            &[],
            &["TRUE"],
        );
    }

    #[test]
    fn test_array_assignment_ok_casting() {
        do_ok_test("DIM a(1)\na(0) = 3.6\nOUT a(0)", &[], &["4"]);
        do_ok_test("DIM a(1) AS INTEGER\na(0) = 3.6\nOUT a(0)", &[], &["4"]);
        do_ok_test("DIM a(1) AS DOUBLE\na(0) = 3\nOUT a(0)", &[], &["3"]);
    }

    #[test]
    fn test_array_assignment_ok_case_insensitive() {
        do_ok_test("DIM a(3)\nA(1) = 5\na(2) = 1\nOUT A(0); a(1); A(2)", &[], &["0 5 1"]);
    }

    #[test]
    fn test_array_assignment_errors() {
        do_simple_error_test("a() = 3\n", "1:1: Cannot index undefined array a");
        do_simple_error_test("a = 3\na(0) = 3\n", "2:1: Cannot index non-array a");
        do_simple_error_test(
            "DIM a(2)\na() = 3\n",
            "2:1: Cannot index array with 0 subscripts; need 1",
        );
        do_simple_error_test("DIM a(1)\na(-1) = 3\n", "2:1: Subscript -1 cannot be negative");
        do_simple_error_test("DIM a(1)\na(1, 3.0) = 3\n", "2:6: Subscript 3.0 must be an integer");
        do_simple_error_test("DIM a(2)\na$(1) = 3", "2:1: Incompatible types in a$ reference");
    }

    #[test]
    fn test_assignment_ok_types() {
        do_ok_test("a = TRUE\nOUT a; a?", &[], &["TRUE TRUE"]);
        do_ok_test("a? = FALSE\nOUT a; a?", &[], &["FALSE FALSE"]);

        do_ok_test("a = 3.5\nOUT a; a#", &[], &["3.5 3.5"]);
        do_ok_test("a# = 3.5\nOUT a; a#", &[], &["3.5 3.5"]);

        do_ok_test("a = 3\nOUT a; a%", &[], &["3 3"]);
        do_ok_test("a% = 3\nOUT a; a%", &[], &["3 3"]);

        do_ok_test("a = \"some text\"\nOUT a; a$", &[], &["some text some text"]);
        do_ok_test("a$ = \"some text\"\nOUT a; a$", &[], &["some text some text"]);

        do_ok_test("a = 1\na = a + 1\nOUT a", &[], &["2"]);
    }

    #[test]
    fn test_assignment_ok_casting() {
        do_ok_test("a = 5.2\nOUT a; a#", &[], &["5.2 5.2"]);
        do_ok_test("a% = 5.2\nOUT a; a%", &[], &["5 5"]);

        do_ok_test("a = 3 + 5.2\nOUT a; a#", &[], &["8.2 8.2"]);
        do_ok_test("a = 3.7 + 5.2\nOUT a; a#", &[], &["8.9 8.9"]);

        do_ok_test("a% = 3 + 5.2\nOUT a; a%", &[], &["8 8"]);
        do_ok_test("a% = 3.7 + 5.2\nOUT a; a%", &[], &["9 9"]);

        do_ok_test("a# = 3\nOUT a; a#", &[], &["3 3"]);
        do_ok_test("a# = 2.8 + 3\nOUT a; a#", &[], &["5.8 5.8"]);
    }

    #[test]
    fn test_assignment_ok_case_insensitive() {
        do_ok_test("foo = 32\nOUT FOO", &[], &["32"]);
    }

    #[test]
    fn test_assignment_errors() {
        do_simple_error_test("a =\n", "1:4: Missing expression in assignment");
        do_simple_error_test("a = b\n", "1:5: Undefined variable b");
        do_simple_error_test(
            "a = 3\na = TRUE\n",
            "2:1: Cannot assign value of type BOOLEAN to variable of type INTEGER",
        );
        do_simple_error_test(
            "a? = 3",
            "1:1: Cannot assign value of type INTEGER to variable of type BOOLEAN",
        );
    }

    #[test]
    fn test_dim_ok() {
        do_ok_test("DIM foo\nDIM bar AS BOOLEAN\nOUT foo%; bar?", &[], &["0 FALSE"]);
    }

    #[test]
    fn test_dim_errors() {
        do_simple_error_test("DIM i\nDIM i", "2:5: Cannot DIM already-defined symbol i");
        do_simple_error_test("DIM i\nDIM I", "2:5: Cannot DIM already-defined symbol I");
        do_simple_error_test("i = 0\nDIM i", "2:5: Cannot DIM already-defined symbol i");
    }

    #[test]
    fn test_dim_array_ok() {
        do_ok_test(
            "DIM foo(3, 4)\nDIM bar(1) AS BOOLEAN\nOUT foo%(2, 2); bar?(0)",
            &[],
            &["0 FALSE"],
        );
    }

    #[test]
    fn test_dim_array_errors() {
        do_simple_error_test("DIM i()", "1:6: Arrays require at least one dimension");
        do_simple_error_test("DIM i(FALSE)", "1:7: Dimensions in DIM array must be integers");
        do_simple_error_test("DIM i(-3)", "1:7: Dimensions in DIM array must be positive");
        do_simple_error_test("DIM i\nDIM i(3)", "2:5: Cannot DIM already-defined symbol i");
    }

    #[test]
    fn test_end_no_code() {
        let captured_out = Rc::from(RefCell::from(vec![]));
        assert_eq!(
            StopReason::Exited(5),
            run("OUT 1\nEND 5\nOUT 2", &[], captured_out.clone()).expect("Execution failed")
        );
        assert_eq!(&["1"], captured_out.borrow().as_slice());
    }

    fn do_end_with_code_test(code: u8) {
        let captured_out = Rc::from(RefCell::from(vec![]));
        assert_eq!(
            StopReason::Exited(code),
            run(&format!("OUT 1: END {}: OUT 2", code), &[], captured_out.clone())
                .expect("Execution failed")
        );
        assert_eq!(&["1"], captured_out.borrow().as_slice());

        let captured_out = Rc::from(RefCell::from(vec![]));
        assert_eq!(
            StopReason::Exited(code),
            run(&format!("OUT 1: END {}.2: OUT 2", code), &[], captured_out.clone())
                .expect("Execution failed")
        );
        assert_eq!(&["1"], captured_out.borrow().as_slice());
    }

    #[test]
    fn text_end_with_code() {
        do_end_with_code_test(0);
        do_end_with_code_test(1);
        do_end_with_code_test(42);
        do_end_with_code_test(127);
    }

    #[test]
    fn test_end_errors() {
        do_simple_error_test("END 1, 2", "1:6: Expected newline but found ,");
        do_simple_error_test("END \"b\"", "1:5: \"b\" is not a number");
        do_simple_error_test("END -3", "1:5: Exit code must be a positive integer");
        do_simple_error_test("END 128", "1:5: Exit code cannot be larger than 127");
    }

    #[test]
    fn test_end_if() {
        let captured_out = Rc::from(RefCell::from(vec![]));
        let input = r#"
            IF TRUE THEN
                OUT OUTF(1, 100)
                END
                OUT OUTF(2, 200)
            ELSEIF OUTF(3, 300) THEN
                OUT OUTF(4, 400)
            ELSE
                OUT OUTF(5, 500)
            END IF
            "#;
        assert_eq!(StopReason::Exited(0), run(input, &[], captured_out.clone()).unwrap());
        assert_eq!(&["100", "1"], captured_out.borrow().as_slice());
    }

    #[test]
    fn test_end_for() {
        let captured_out = Rc::from(RefCell::from(vec![]));
        let input = r#"FOR i = 1 TO OUTF(10, i * 100): IF i = 3 THEN: END: END IF: OUT i: NEXT"#;
        assert_eq!(StopReason::Exited(0), run(input, &[], captured_out.clone()).unwrap());
        assert_eq!(&["100", "1", "200", "2", "300"], captured_out.borrow().as_slice());
    }

    #[test]
    fn test_end_while() {
        let captured_out = Rc::from(RefCell::from(vec![]));
        let input = r#"i = 1: WHILE i < OUTF(10, i * 100): IF i = 4 THEN: END: END IF: OUT i: i = i + 1: WEND"#;
        assert_eq!(StopReason::Exited(0), run(input, &[], captured_out.clone()).unwrap());
        assert_eq!(&["100", "1", "200", "2", "300", "3", "400"], captured_out.borrow().as_slice());
    }

    #[test]
    fn test_end_nested() {
        let captured_out = Rc::from(RefCell::from(vec![]));
        assert_eq!(
            StopReason::Exited(42),
            run(
                "FOR a = 0 TO 10\nOUT a\nIF a = 3 THEN\nEND 42\nOUT \"no\"\nEND IF\nNEXT",
                &[],
                captured_out.clone()
            )
            .expect("Execution failed")
        );
        assert_eq!(&["0", "1", "2", "3"], captured_out.borrow().as_slice());
    }

    #[test]
    fn test_end_can_resume() {
        let captured_out = Rc::from(RefCell::from(vec![]));
        let mut machine = Machine::default();
        machine.add_command(OutCommand::new(captured_out.clone()));
        machine.add_function(SumFunction::new());

        assert_eq!(
            StopReason::Exited(10),
            block_on(machine.exec(&mut "OUT 1\nEND 10\nOUT 2".as_bytes()))
                .expect("Execution failed")
        );
        assert_eq!(&["1"], captured_out.borrow().as_slice());

        captured_out.borrow_mut().clear();
        assert_eq!(
            StopReason::Exited(11),
            block_on(machine.exec(&mut "OUT 2\nEND 11\nOUT 3".as_bytes()))
                .expect("Execution failed")
        );
        assert_eq!(&["2"], captured_out.borrow().as_slice());
    }

    #[tokio::test]
    async fn test_signals_stop() {
        let mut machine = Machine::default();
        let signals_tx = machine.get_signals_tx();

        // This is a best-effort test because we are trying to exercise a condition for which we
        // have no synchronization primitives.
        for _ in 0..10 {
            let input = &mut "WHILE TRUE: WEND".as_bytes();
            machine.drain_signals();
            let future = machine.exec(input);

            // There is no guarantee that the tight loop inside the machine is running immediately
            // at this point (particularly because we run with just one thread in this test), thus
            // we may send the signal prematurely.  We would still get a `Break` stop reason because
            // we would detect the signal *before* entering the loop, but that would defeat the
            // purpose of this test.  Give a chance to the machine code to run first and get stuck.
            tokio::task::yield_now().await;

            signals_tx.send(Signal::Break).await.unwrap();
            let result = future.await;
            assert_eq!(StopReason::Break, result.unwrap());
        }
    }

    #[test]
    fn test_if_ok() {
        let code = r#"
            IN n
            IF n = 3 THEN
                OUT "match"
            END IF
            IF n <> 3 THEN
                OUT "no match"
            END IF
        "#;
        do_ok_test(code, &["3"], &["match"]);
        do_ok_test(code, &["5"], &["no match"]);

        let code = r#"
            IN n
            IF n = 1 THEN
                OUT "first"
            ELSEIF n = 2 THEN
                OUT "second"
            ELSEIF n = 3 THEN
                OUT "third"
            ELSE
                OUT "fourth"
            END IF
        "#;
        do_ok_test(code, &["1"], &["first"]);
        do_ok_test(code, &["2"], &["second"]);
        do_ok_test(code, &["3"], &["third"]);
        do_ok_test(code, &["4"], &["fourth"]);
    }

    #[test]
    fn test_if_ok_on_malformed_branch() {
        let code = r#"
            IN n
            IF n = 3 THEN
                OUT "match"
            ELSEIF "foo" THEN 'Invalid expression type but not evaluated.
                OUT "no match"
            END IF
        "#;
        do_ok_test(code, &["3"], &["match"]);
        do_error_test(code, &["5"], &[], "5:20: IF/ELSEIF require a boolean condition");
    }

    #[test]
    fn test_if_errors() {
        do_simple_error_test("IF TRUE THEN END IF", "1:14: Expecting newline after THEN");
        do_simple_error_test(
            "IF TRUE THEN\nELSE IF TRUE THEN\nEND IF",
            "2:6: Expecting newline after ELSE",
        );
        do_simple_error_test("IF TRUE\nEND IF\nOUT 3", "1:8: No THEN in IF statement");

        do_simple_error_test("IF 2\nEND IF", "1:5: No THEN in IF statement");
        do_simple_error_test("IF 2 THEN\nEND IF", "1:4: IF/ELSEIF require a boolean condition");
        do_simple_error_test(
            "IF FALSE THEN\nELSEIF 2 THEN\nEND IF",
            "2:8: IF/ELSEIF require a boolean condition",
        );
    }

    #[test]
    fn test_for_incrementing() {
        do_ok_test("FOR a = 0 TO 0: OUT a: NEXT", &[], &["0"]);
        do_ok_test("FOR a = 0 TO 3: OUT a: NEXT", &[], &["0", "1", "2", "3"]);
        do_ok_test("FOR a = 1.3 TO 3: OUT a: NEXT", &[], &["1.3", "2.3"]);
        do_ok_test("FOR a = 1.3 TO 3.3: OUT a: NEXT", &[], &["1.3", "2.3", "3.3"]);
        do_ok_test("FOR a = 1 TO 3.3: OUT a: NEXT", &[], &["1", "2", "3"]);
        do_ok_test("FOR a = 1 TO 3.7: OUT a: NEXT", &[], &["1", "2", "3"]);
        do_ok_test("FOR a# = 1 TO 2: OUT a: NEXT", &[], &["1", "2"]);
        do_ok_test("FOR a = 1.1 TO 2.1: b% = (a * 10): OUT b: NEXT", &[], &["11", "21"]);
        do_ok_test("FOR a# = 1.1 TO 2.1: b% = (a * 10): OUT b: NEXT", &[], &["11", "21"]);
    }

    #[test]
    fn test_for_incrementing_with_step() {
        do_ok_test("FOR a = 0 TO 0 STEP 3: OUT a: NEXT", &[], &["0"]);
        do_ok_test("FOR a = 0 TO 2 STEP 3: OUT a: NEXT", &[], &["0"]);
        do_ok_test("FOR a = 0 TO 3 STEP 3: OUT a: NEXT", &[], &["0", "3"]);
        do_ok_test("FOR a = 0 TO 10 STEP 3: OUT a: NEXT", &[], &["0", "3", "6", "9"]);
        do_ok_test("FOR a = 1 TO 2 STEP 0.4: b% = (a * 10): OUT b: NEXT", &[], &["10", "14", "18"]);
        do_ok_test(
            "FOR a# = 1 TO 2 STEP 0.4: b% = (a * 10): OUT b: NEXT",
            &[],
            &["10", "14", "18"],
        );
    }

    #[test]
    fn test_for_decrementing_with_step() {
        do_ok_test("FOR a = 0 TO 0 STEP -2: OUT a: NEXT", &[], &["0"]);
        do_ok_test("FOR a = 2 TO 0 STEP -2: OUT a: NEXT", &[], &["2", "0"]);
        do_ok_test("FOR a = -2 TO -6 STEP -2: OUT a: NEXT", &[], &["-2", "-4", "-6"]);
        do_ok_test("FOR a = 10 TO 1 STEP -2: OUT a: NEXT", &[], &["10", "8", "6", "4", "2"]);
        do_ok_test(
            "FOR a# = 2 TO 1 STEP -0.4: b% = (a * 10): OUT b: NEXT",
            &[],
            &["20", "16", "12"],
        );
    }

    #[test]
    fn test_for_doubles_on_integer_iterator() {
        // This tests a corner case where using a DOUBLE step value on a variable that is declared
        // as an INTEGER results in an infinite loop due to rounding.  We could error our in this
        // case (or force the iterator to be a DOUBLE if it is not yet defined), but I'm not yet
        // sure if there would be legitimate reasons for someone to want this.
        do_ok_test(
            r#"
            i = 0
            DIM a AS INTEGER
            FOR a = 1.0 TO 2.0 STEP 0.4
                i = i + 1
                IF i = 100 THEN
                    GOTO @out
                END IF
            NEXT
            @out: OUT i
            "#,
            &[],
            &["100"],
        );
    }

    #[test]
    fn test_for_already_done() {
        do_ok_test("FOR i = 10 TO 9\nOUT i\nNEXT", &[], &[]);
        do_ok_test("FOR i = 9 TO 10 STEP -1\nOUT i\nNEXT", &[], &[]);
    }

    #[test]
    fn test_for_iterator_is_visible_after_next() {
        let code = r#"
            FOR something = 1 TO 10 STEP 8
            NEXT
            OUT something
        "#;
        do_ok_test(code, &[], &["17"]);
    }

    #[test]
    fn test_for_iterator_can_be_modified() {
        let code = r#"
            FOR something = 1 TO 5
                OUT something
                something = something + 1
            NEXT
        "#;
        do_ok_test(code, &[], &["1", "3", "5"]);
    }

    #[test]
    fn test_for_errors() {
        do_simple_error_test("FOR\nNEXT", "1:4: No iterator name in FOR statement");
        do_simple_error_test("FOR a = 1 TO 10\nEND IF", "2:1: END IF without IF");

        do_simple_error_test(
            "FOR i = \"a\" TO 3\nNEXT",
            "1:13: Cannot compare \"a\" and 3 with <=",
        );
        do_simple_error_test(
            "FOR i = 1 TO \"a\"\nNEXT",
            "1:11: Cannot compare 1 and \"a\" with <=",
        );

        do_simple_error_test(
            "FOR i = \"b\" TO 7 STEP -8\nNEXT",
            "1:13: Cannot compare \"b\" and 7 with >=",
        );
        do_simple_error_test(
            "FOR i = 1 TO \"b\" STEP -8\nNEXT",
            "1:11: Cannot compare 1 and \"b\" with >=",
        );
    }

    #[test]
    fn test_function_call_ok() {
        do_ok_test("x = 3\nOUT SUM(x, Sum%(4, 5), 1, sum())", &[], &["13"]);
    }

    #[test]
    fn test_function_call_argless() {
        do_ok_test("x = FALSE: OUT x: x = TYPE_CHECK: OUT x", &[], &["FALSE", "TRUE"]);
    }

    #[test]
    fn test_function_call_errors() {
        do_simple_error_test("OUT OUT()", "1:5: OUT is not an array or a function");
        do_simple_error_test("OUT SUM?()", "1:5: Incompatible types in SUM? reference");
        do_simple_error_test(
            "OUT TYPE_CHECK()",
            "1:5: In call to TYPE_CHECK: expected no arguments nor parenthesis",
        );
    }

    #[test]
    fn test_gosub_and_return() {
        do_ok_test(
            r#"
                i = 10
                GOSUB @sub
                GOSUB 20
                GOTO @end
                @sub 20: OUT i: i = i + 1: RETURN
                @end
            "#,
            &[],
            &["10", "11"],
        );
    }

    #[test]
    fn test_gosub_and_return_nested() {
        do_ok_test(
            r#"
                GOTO @main
                @sub1: OUT 1: GOSUB @sub2: OUT 2: RETURN
                @sub2: OUT 3: RETURN
                @main
                GOSUB @sub1
            "#,
            &[],
            &["1", "3", "2"],
        );
    }

    #[test]
    fn test_gosub_and_return_from_other() {
        do_ok_test(
            r#"
                GOTO @main
                @sub1: OUT 1: GOTO @sub2: RETURN
                @sub2: OUT 3: RETURN
                @main
                GOSUB @sub1
            "#,
            &[],
            &["1", "3"],
        );
    }

    #[test]
    fn test_gosub_without_return() {
        do_ok_test(r#"GOSUB @sub: @sub: OUT 1"#, &[], &["1"]);
    }

    #[test]
    fn test_gosub_and_return_errors() {
        do_simple_error_test("GOSUB @foo", "1:7: Unknown label foo");
        do_simple_error_test("RETURN", "1:1: No address to return to");
        do_simple_error_test("GOTO @foo\n@foo: RETURN", "2:7: No address to return to");
    }

    #[test]
    fn test_goto_top_level_go_forward() {
        do_ok_test("OUT 1: GOTO @skip: OUT 2: @skip: OUT 3", &[], &["1", "3"]);
    }

    #[test]
    fn test_goto_top_level_go_backward() {
        do_ok_test(
            "OUT 1: GOTO @skip: @before: OUT 2: GOTO @end: @skip: OUT 3: GOTO @before: @end",
            &[],
            &["1", "3", "2"],
        );
    }

    #[test]
    fn test_goto_nested_can_go_up() {
        do_ok_test(
            "IF TRUE THEN: FOR i = 1 TO 10: OUT i: GOTO @out: NEXT: OUT 99: @out: OUT 100: END IF",
            &[],
            &["1", "100"],
        );

        do_ok_test(
            "IF TRUE THEN: WHILE TRUE: OUT 1: GOTO @out: WEND: OUT 99: END IF: @out: OUT 100",
            &[],
            &["1", "100"],
        );
    }

    #[test]
    fn test_goto_nested_can_go_down() {
        do_ok_test(
            "IF TRUE THEN: GOTO @sibling: OUT 1: END IF: IF TRUE THEN: @sibling: OUT 2: END IF",
            &[],
            &["2"],
        );
    }

    #[test]
    fn test_goto_as_last_statement() {
        let captured_out = Rc::from(RefCell::from(vec![]));
        assert_eq!(
            StopReason::Exited(5),
            run(
                "i = 0: @a: IF i = 5 THEN: END i: END IF: i = i + 1: GOTO @a",
                &[],
                captured_out.clone()
            )
            .expect("Execution failed")
        );
        assert!(captured_out.borrow().is_empty());
    }

    #[test]
    fn test_goto_middle_of_line() {
        do_ok_test("GOTO 20\nOUT 1: 20 OUT 2", &[], &["2"]);
    }

    #[test]
    fn test_goto_errors() {
        do_simple_error_test("GOTO 10", "1:6: Unknown label 10");
        do_simple_error_test("GOTO @foo", "1:6: Unknown label foo");
    }

    #[test]
    fn test_label_ok() {
        do_ok_test("OUT 1: 10: 20 OUT 2", &[], &["1", "2"]);
        do_ok_test("OUT 1: @foo: OUT 2", &[], &["1", "2"]);
    }

    #[test]
    fn test_label_avoid_redefinition() {
        do_ok_test(
            "i = 0: @x: @y: i = i + 1: IF i = 2 THEN: GOTO @end: END IF: GOTO @x: @end",
            &[],
            &[],
        );
    }

    #[test]
    fn test_label_duplicate() {
        do_simple_error_test("@foo: IF TRUE THEN: @foo: END IF", "1:21: Duplicate label foo");
        do_simple_error_test(
            "IF TRUE THEN: @foo: END IF: IF TRUE THEN: @foo: END IF",
            "1:43: Duplicate label foo",
        );

        do_simple_error_test("@foo: @bar: @foo", "1:13: Duplicate label foo");

        do_simple_error_test(
            r#"
            i = 0
            @a
                @b
                    @c
                        i = i + 1
                        IF i = 1 THEN: GOTO @b: END IF
                        @a
                        IF i = 2 THEN: GOTO @c: END IF
                        IF i = 3 THEN: GOTO @out: END IF
            @out
            "#,
            "8:25: Duplicate label a",
        );
    }

    #[test]
    fn test_on_error_goto_line() {
        do_ok_test(
            r#"
            ON ERROR GOTO 100
            OUT 1
            OUT RAISE("syntax")
            OUT 2
            100 OUT ERRMSG
            "#,
            &[],
            &["1", "4:17: In call to RAISE: expected arg1$"],
        );
    }

    #[test]
    fn test_on_error_goto_label() {
        do_ok_test(
            r#"
            ON ERROR GOTO @foo
            OUT 1
            OUT RAISE("syntax")
            OUT 2
            @foo
            OUT ERRMSG
            "#,
            &[],
            &["1", "4:17: In call to RAISE: expected arg1$"],
        );
    }

    #[test]
    fn test_on_error_reset() {
        do_error_test(
            r#"
            ON ERROR GOTO @foo
            OUT 1
            OUT RAISE("syntax")
            @foo
            ON ERROR GOTO 0
            OUT 2
            OUT RAISE("syntax")
            "#,
            &[],
            &["1", "2"],
            "8:17: In call to RAISE: expected arg1$",
        );
    }

    #[test]
    fn test_on_error_resume_next() {
        do_ok_test(
            r#"
            ON ERROR RESUME NEXT
            OUT 1
            OUT RAISE("syntax")
            OUT ERRMSG
            "#,
            &[],
            &["1", "4:17: In call to RAISE: expected arg1$"],
        );
    }

    #[test]
    fn test_on_error_types() {
        do_ok_test(
            r#"ON ERROR RESUME NEXT: OUT RAISE("argument"): OUT ERRMSG"#,
            &[],
            &["1:27: In call to RAISE: 1:33: Bad argument"],
        );

        do_ok_test(
            r#"ON ERROR RESUME NEXT: OUT RAISE("eval"): OUT ERRMSG"#,
            &[],
            &["1:27: In call to RAISE: 1:33: Some eval error"],
        );

        do_ok_test(
            r#"ON ERROR RESUME NEXT: OUT RAISE("internal"): OUT ERRMSG"#,
            &[],
            &["1:27: In call to RAISE: 1:33: Some internal error"],
        );

        do_ok_test(
            r#"ON ERROR RESUME NEXT: OUT RAISE("io"): OUT ERRMSG"#,
            &[],
            &["1:27: In call to RAISE: Some I/O error"],
        );

        do_ok_test(
            r#"ON ERROR RESUME NEXT: OUT RAISE("syntax"): OUT ERRMSG"#,
            &[],
            &["1:27: In call to RAISE: expected arg1$"],
        );
    }

    #[test]
    fn test_on_error_unset_incompatible_errmsg() {
        do_ok_test(
            r#"
            ERRMSG = 3 ' This should be a string and not cause trouble.
            ON ERROR RESUME NEXT
            OUT ERRMSG
            OUT RAISE("syntax")
            OUT ERRMSG
            "#,
            &[],
            &["3", "5:17: In call to RAISE: expected arg1$"],
        );
    }

    #[test]
    fn test_while_ok() {
        let code = r#"
            IN n
            WHILE n > 0
                OUT "n is"; n
                n = n - 1
            WEND
        "#;
        do_ok_test(code, &["0"], &[]);
        do_ok_test(code, &["3"], &["n is 3", "n is 2", "n is 1"]);

        do_ok_test("WHILE FALSE\nOUT 1\nWEND", &[], &[]);
    }

    #[test]
    fn test_while_errors() {
        do_simple_error_test("WHILE\nWEND", "1:6: No expression in WHILE statement");
        do_simple_error_test("WHILE\nEND IF", "1:6: No expression in WHILE statement");

        do_simple_error_test("\n\n\nWHILE 2\n", "4:1: WHILE without WEND");
        do_simple_error_test("WHILE 3\nEND", "1:1: WHILE without WEND");
        do_simple_error_test("WHILE 3\nEND IF", "2:1: END IF without IF");
        do_simple_error_test("WHILE 2\nWEND", "1:7: WHILE requires a boolean condition");
    }

    #[test]
    fn test_misc_comments_and_spaces() {
        let code = r#"
            REM This is the start of the program.

            OUT "Hello" 'Some remark here.

            IF TRUE THEN

                OUT "Bye" 'And another remark here after a blank line.
            END IF
        "#;
        do_ok_test(code, &[], &["Hello", "Bye"]);
    }

    #[test]
    fn test_top_level_syntax_errors_prevent_execution() {
        do_simple_error_test("+ b", "1:1: Unexpected + in statement");
        do_error_test(r#"OUT "a": + b: OUT "b""#, &[], &[], "1:10: Unexpected + in statement");
    }

    #[test]
    fn test_inner_level_syntax_errors_prevent_execution() {
        do_simple_error_test("+ b", "1:1: Unexpected + in statement");
        do_error_test(
            r#"OUT "a": IF TRUE THEN: + b: END IF: OUT "b""#,
            &[],
            &[],
            "1:24: Unexpected + in statement",
        );
    }

    #[test]
    fn test_top_level_semantic_errors_allow_execution() {
        do_simple_error_test("FOO BAR", "1:1: Unknown builtin FOO");
        do_error_test(r#"OUT "a": FOO BAR: OUT "b""#, &[], &["a"], "1:10: Unknown builtin FOO");
    }

    #[test]
    fn test_inner_level_semantic_errors_allow_execution() {
        do_simple_error_test(r#"IF TRUE THEN: FOO BAR: END IF"#, "1:15: Unknown builtin FOO");
        do_error_test(
            r#"OUT "a": IF TRUE THEN: FOO BAR: END IF: OUT "b""#,
            &[],
            &["a"],
            "1:24: Unknown builtin FOO",
        );
    }

    #[test]
    fn test_exec_shares_state() {
        let mut machine = Machine::default();
        assert_eq!(
            StopReason::Eof,
            block_on(machine.exec(&mut b"a = 10".as_ref())).expect("Execution failed")
        );
        assert_eq!(
            StopReason::Eof,
            block_on(machine.exec(&mut b"b = a".as_ref())).expect("Execution failed")
        );
    }
}
