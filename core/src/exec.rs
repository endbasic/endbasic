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
use crate::parser;
use crate::reader::LineCol;
use crate::syms::{CallError, Callable, CallableMetadata, Symbol, Symbols};
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
    #[error("{}:{}: {}", .0.line, .0.col, .1)]
    EvalError(LineCol, String),

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
    fn from_call_error(md: &CallableMetadata, e: CallError, pos: LineCol) -> Self {
        match e {
            CallError::ArgumentError(pos2, e) => Self::SyntaxError(
                pos,
                format!("In call to {}: {}:{}: {}", md.name(), pos2.line, pos2.col, e),
            ),
            CallError::EvalError(pos2, e) => {
                if md.return_type() == VarType::Void {
                    Self::EvalError(pos2, e)
                } else {
                    Self::EvalError(
                        pos,
                        format!("In call to {}: {}:{}: {}", md.name(), pos2.line, pos2.col, e),
                    )
                }
            }
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
        Self::EvalError(pos, e.message)
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
            Error::EvalError(..) => true,
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
    value_stack: Vec<(Value, LineCol)>,
    err_handler: ErrorHandlerISpan,
}

impl Default for Context {
    fn default() -> Self {
        Self {
            pc: 0,
            addr_stack: vec![],
            value_stack: vec![],
            err_handler: ErrorHandlerISpan::None,
        }
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

    /// Registers the given builtin callable, which must not yet be registered.
    pub fn add_callable(&mut self, callable: Rc<dyn Callable>) {
        self.symbols.add_callable(callable)
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

    /// Obtains the value of a variable.
    ///
    /// Returns an error if the variable is not defined, if the referenced symbol is not a variable,
    /// or if the type annotation in the variable reference does not match the type of the value
    /// that the variable contains.
    pub fn get_var(&self, vref: &VarRef) -> std::result::Result<&Value, value::Error> {
        self.symbols.get_var(vref)
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

    /// Given a collection of arguments (values), loads all of those that are variable references.
    ///
    /// All commands should use this before inspecting their arguments, unless they care about
    /// using values by reference.
    pub fn load_all(
        &self,
        args: Vec<(Value, LineCol)>,
    ) -> std::result::Result<Vec<(Value, LineCol)>, CallError> {
        self.symbols.load_all(args)
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

    /// Handles an array assignment.
    async fn assign_array(
        &mut self,
        context: &mut Context,
        vref: &VarRef,
        vref_pos: LineCol,
        nargs: usize,
    ) -> Result<()> {
        let mut ds = Vec::with_capacity(nargs);
        for _ in 0..nargs {
            let (value, pos) = context.value_stack.pop().unwrap();
            match value {
                Value::Integer(i) => ds.push(i),
                v => return new_syntax_error(pos, format!("Subscript {} must be an integer", v)),
            }
        }

        let (value, _pos) = context.value_stack.pop().unwrap();

        match self.symbols.get_mut(vref).map_err(|e| Error::from_value_error(e, vref_pos))? {
            Some(Symbol::Array(array)) => {
                array.assign(&ds, value).map_err(|e| Error::from_value_error(e, vref_pos))?;
                Ok(())
            }
            Some(_) => {
                new_syntax_error(vref_pos, format!("Cannot index non-array {}", vref.name()))
            }
            None => {
                new_syntax_error(vref_pos, format!("Cannot index undefined array {}", vref.name()))
            }
        }
    }

    /// Handles a builtin call.
    async fn builtin_call(
        &mut self,
        context: &mut Context,
        bref: &VarRef,
        bref_pos: LineCol,
        nargs: usize,
    ) -> Result<()> {
        match self.symbols.get(bref).map_err(|e| Error::from_value_error(e, bref_pos))? {
            Some(Symbol::Callable(b)) => {
                let metadata = b.metadata();
                if metadata.is_function() {
                    return Err(Error::EvalError(bref_pos, format!("{} is not a command", bref)));
                }
                if !bref.accepts(metadata.return_type()) {
                    return Err(Error::EvalError(
                        bref_pos,
                        "Incompatible type annotation for builtin call".to_owned(),
                    ));
                }

                let mut args = Vec::with_capacity(nargs);
                for _ in 0..nargs {
                    let (value, pos) = context.value_stack.pop().unwrap();
                    args.push((value, pos));
                }

                let b = b.clone();
                let value = b
                    .exec(args, self)
                    .await
                    .map_err(|e| Error::from_call_error(b.metadata(), e, bref_pos))?;
                assert_eq!(value, Value::Void, "Commands do return values");
                Ok(())
            }

            Some(_) => Err(Error::EvalError(bref_pos, format!("{} is not a command", bref))),
            None => Err(Error::EvalError(bref_pos, format!("Unknown builtin {}", bref))),
        }
    }

    /// Handles an array definition.  The array must not yet exist, and the name may not overlap
    /// function or variable names.
    fn dim_array(&mut self, context: &mut Context, span: &DimArrayISpan) -> Result<()> {
        let mut ds = Vec::with_capacity(span.dimensions);
        for _ in 0..span.dimensions {
            let (value, pos) = context.value_stack.pop().unwrap();
            match value {
                Value::Integer(i) => {
                    if i <= 0 {
                        return new_syntax_error(pos, "Dimensions in DIM array must be positive");
                    }
                    ds.push(i as usize);
                }
                Value::VarRef(_) => panic!("Should never get unevaluated varrefs"),
                _ => return new_syntax_error(pos, "Dimensions in DIM array must be integers"),
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
    fn end(&mut self, context: &mut Context, has_code: bool) -> Result<()> {
        let code = if has_code {
            let (code, code_pos) = context.value_stack.pop().unwrap();
            match code.as_i32().map_err(|e| Error::from_value_error(e, code_pos))? {
                n if n < 0 => {
                    return new_syntax_error(
                        code_pos,
                        "Exit code must be a positive integer".to_owned(),
                    );
                }
                n if n >= 128 => {
                    return new_syntax_error(
                        code_pos,
                        "Exit code cannot be larger than 127".to_owned(),
                    );
                }
                n => n as u8,
            }
        } else {
            0
        };
        self.stop_reason = Some(StopReason::Exited(code));
        Ok(())
    }

    /// Handles a unary operator that is part of an expression.
    fn exec_unary_op<F: Fn(&Value) -> value::Result<Value>>(
        context: &mut Context,
        op: F,
        pos: LineCol,
    ) -> Result<()> {
        let (value, _pos) = context.value_stack.pop().unwrap();
        let result = op(&value).map_err(|e| Error::from_value_error(e, pos))?;
        context.value_stack.push((result, pos));
        Ok(())
    }

    /// Handles a binary operator that is part of an expression.
    fn exec_binary_op<F: Fn(&Value, &Value) -> value::Result<Value>>(
        context: &mut Context,
        op: F,
        pos: LineCol,
    ) -> Result<()> {
        let (rhs, _pos) = context.value_stack.pop().unwrap();
        let (lhs, _pos) = context.value_stack.pop().unwrap();
        let result = op(&lhs, &rhs).map_err(|e| Error::from_value_error(e, pos))?;
        context.value_stack.push((result, pos));
        Ok(())
    }

    /// Evaluates the subscripts of an array reference.
    fn get_array_args(&self, context: &mut Context, nargs: usize) -> Result<Vec<i32>> {
        let mut subscripts = Vec::with_capacity(nargs);
        for _ in 0..nargs {
            let (value, pos) = context.value_stack.pop().unwrap();
            match value {
                Value::Integer(i) => {
                    subscripts.push(i);
                    continue;
                }
                Value::VarRef(vref) => {
                    let value =
                        self.symbols.get_var(&vref).map_err(|e| Error::from_value_error(e, pos))?;
                    if let Value::Integer(i) = value {
                        subscripts.push(*i);
                        continue;
                    }
                }
                _ => (), // Fall through to error.
            }
            return Err(Error::EvalError(pos, "Array subscripts must be integers".to_owned()));
        }
        Ok(subscripts)
    }

    /// Evaluates a function call specified by `fref` and arguments `args` on the function `f`.
    async fn do_function_call(
        &mut self,
        context: &mut Context,
        fref: &VarRef,
        fref_pos: LineCol,
        nargs: usize,
        f: Rc<dyn Callable>,
    ) -> Result<()> {
        let metadata = f.metadata();
        if !fref.accepts(metadata.return_type()) {
            return Err(Error::EvalError(
                fref_pos,
                "Incompatible type annotation for function call".to_owned(),
            ));
        }

        let mut args = Vec::with_capacity(nargs);
        for _ in 0..nargs {
            let (value, pos) = context.value_stack.pop().unwrap();
            args.push((value, pos));
        }

        let result = f.exec(args, self).await;
        match result {
            Ok(value) => {
                debug_assert!(metadata.return_type() != VarType::Auto);
                let fref = VarRef::new(fref.name(), metadata.return_type());
                // Given that we only support built-in functions at the moment, this
                // could well be an assertion.  Doing so could turn into a time bomb
                // when/if we add user-defined functions, so handle the problem as an
                // error.
                if !fref.accepts(value.as_vartype()) {
                    return Err(Error::EvalError(
                        fref_pos,
                        format!(
                            "Value returned by {} is incompatible with its type definition",
                            fref.name(),
                        ),
                    ));
                }
                context.value_stack.push((value, fref_pos));
                Ok(())
            }
            Err(e) => Err(Error::from_call_error(metadata, e, fref_pos)),
        }
    }

    /// Handles a function call or an array reference.
    async fn function_call_or_array_ref(
        &mut self,
        context: &mut Context,
        fref: &VarRef,
        fref_pos: LineCol,
        nargs: usize,
    ) -> Result<()> {
        match self.symbols.get(fref).map_err(|e| Error::from_value_error(e, fref_pos))? {
            Some(Symbol::Array(_)) => (), // Fallthrough.
            Some(Symbol::Callable(f)) => {
                if !f.metadata().is_function() {
                    return Err(Error::EvalError(
                        fref_pos,
                        format!("{} is not an array nor a function", f.metadata().name()),
                    ));
                }
                if f.metadata().is_argless() {
                    return Err(Error::EvalError(
                        fref_pos,
                        format!(
                            "In call to {}: expected no arguments nor parenthesis",
                            f.metadata().name()
                        ),
                    ));
                }
                let f = f.clone();
                return self.do_function_call(context, fref, fref_pos, nargs, f).await;
            }
            Some(Symbol::Variable(_)) => {
                return Err(Error::EvalError(
                    fref_pos,
                    format!("{} is not an array or a function", fref),
                ))
            }
            None => {
                return Err(Error::EvalError(
                    fref_pos,
                    format!("Unknown function or array {}", fref),
                ))
            }
        }

        // We have to handle arrays outside of the match above because we cannot hold a
        // reference to the array while we evaluate subscripts.  This implies that we have
        // to do a second lookup of the array right below, which isn't great...
        let subscripts = self.get_array_args(context, nargs)?;
        match self.symbols.get(fref).map_err(|e| Error::from_value_error(e, fref_pos))? {
            Some(Symbol::Array(array)) => {
                let value = array
                    .index(&subscripts)
                    .cloned()
                    .map_err(|e| Error::from_value_error(e, fref_pos))?;
                context.value_stack.push((value, fref_pos));
                Ok(())
            }
            _ => unreachable!(),
        }
    }

    /// Evaluates a call to an argless function.
    async fn argless_function_call(
        &mut self,
        fref: VarRef,
        fref_pos: LineCol,
        f: Rc<dyn Callable>,
    ) -> Result<Value> {
        let metadata = f.metadata();
        if !metadata.is_function() {
            return Err(Error::EvalError(
                fref_pos,
                format!("{} is not an array nor a function", metadata.name()),
            ));
        }
        if !fref.accepts(metadata.return_type()) {
            return Err(Error::EvalError(
                fref_pos,
                "Incompatible type annotation for function call".to_owned(),
            ));
        }

        let result = f.exec(vec![], self).await;
        match result {
            Ok(value) => {
                debug_assert!(metadata.return_type() != VarType::Auto);
                let fref_checker = VarRef::new(fref.name(), metadata.return_type());
                // Given that we only support built-in functions at the moment, this
                // could well be an assertion.  Doing so could turn into a time bomb
                // when/if we add user-defined functions, so handle the problem as an
                // error.
                if !fref_checker.accepts(value.as_vartype()) {
                    return Err(Error::EvalError(
                        fref_pos,
                        format!(
                            "Value returned by {} is incompatible with its type definition",
                            fref.name(),
                        ),
                    ));
                }
                Ok(value)
            }
            Err(e) => Err(Error::from_call_error(metadata, e, fref_pos)),
        }
    }

    /// Helper for `exec_one` that only worries about execution of a single instruction.
    ///
    /// Errors are handled on the caller side depending on the `ON ERROR` handling policy that is
    /// currently configured.
    async fn exec_safe(&mut self, context: &mut Context, instrs: &[Instruction]) -> Result<()> {
        let instr = &instrs[context.pc];
        match instr {
            Instruction::And(pos) => {
                Machine::exec_binary_op(context, |lhs, rhs| lhs.and(rhs), *pos)?;
                context.pc += 1;
            }

            Instruction::Or(pos) => {
                Machine::exec_binary_op(context, |lhs, rhs| lhs.or(rhs), *pos)?;
                context.pc += 1;
            }

            Instruction::Xor(pos) => {
                Machine::exec_binary_op(context, |lhs, rhs| lhs.xor(rhs), *pos)?;
                context.pc += 1;
            }

            Instruction::Not(pos) => {
                Machine::exec_unary_op(context, |value| value.not(), *pos)?;
                context.pc += 1;
            }

            Instruction::ShiftLeft(pos) => {
                Machine::exec_binary_op(context, |lhs, rhs| lhs.shl(rhs), *pos)?;
                context.pc += 1;
            }

            Instruction::ShiftRight(pos) => {
                Machine::exec_binary_op(context, |lhs, rhs| lhs.shr(rhs), *pos)?;
                context.pc += 1;
            }

            Instruction::Equal(pos) => {
                Machine::exec_binary_op(context, |lhs, rhs| lhs.eq(rhs), *pos)?;
                context.pc += 1;
            }

            Instruction::NotEqual(pos) => {
                Machine::exec_binary_op(context, |lhs, rhs| lhs.ne(rhs), *pos)?;
                context.pc += 1;
            }

            Instruction::Less(pos) => {
                Machine::exec_binary_op(context, |lhs, rhs| lhs.lt(rhs), *pos)?;
                context.pc += 1;
            }

            Instruction::LessEqual(pos) => {
                Machine::exec_binary_op(context, |lhs, rhs| lhs.le(rhs), *pos)?;
                context.pc += 1;
            }

            Instruction::Greater(pos) => {
                Machine::exec_binary_op(context, |lhs, rhs| lhs.gt(rhs), *pos)?;
                context.pc += 1;
            }

            Instruction::GreaterEqual(pos) => {
                Machine::exec_binary_op(context, |lhs, rhs| lhs.ge(rhs), *pos)?;
                context.pc += 1;
            }

            Instruction::Add(pos) => {
                Machine::exec_binary_op(context, |lhs, rhs| lhs.add(rhs), *pos)?;
                context.pc += 1;
            }

            Instruction::Subtract(pos) => {
                Machine::exec_binary_op(context, |lhs, rhs| lhs.sub(rhs), *pos)?;
                context.pc += 1;
            }

            Instruction::Multiply(pos) => {
                Machine::exec_binary_op(context, |lhs, rhs| lhs.mul(rhs), *pos)?;
                context.pc += 1;
            }

            Instruction::Divide(pos) => {
                Machine::exec_binary_op(context, |lhs, rhs| lhs.div(rhs), *pos)?;
                context.pc += 1;
            }

            Instruction::Modulo(pos) => {
                Machine::exec_binary_op(context, |lhs, rhs| lhs.modulo(rhs), *pos)?;
                context.pc += 1;
            }

            Instruction::Power(pos) => {
                Machine::exec_binary_op(context, |lhs, rhs| lhs.pow(rhs), *pos)?;
                context.pc += 1;
            }

            Instruction::Negate(pos) => {
                Machine::exec_unary_op(context, |value| value.neg(), *pos)?;
                context.pc += 1;
            }

            Instruction::Assign(vref, vref_pos) => {
                let (value, _pos) = context.value_stack.pop().unwrap();
                self.symbols
                    .set_var(vref, value)
                    .map_err(|e| Error::from_value_error(e, *vref_pos))?;
                context.pc += 1;
            }

            Instruction::ArrayAssignment(vref, vref_pos, nargs) => {
                self.assign_array(context, vref, *vref_pos, *nargs).await?;
                context.pc += 1;
            }

            Instruction::BuiltinCall(bref, bref_pos, nargs) => {
                self.builtin_call(context, bref, *bref_pos, *nargs).await?;
                context.pc += 1;
            }

            Instruction::Call(span) => {
                context.addr_stack.push(context.pc + 1);
                context.pc = span.addr;
            }

            Instruction::FunctionCall(fref, pos, nargs) => {
                self.function_call_or_array_ref(context, fref, *pos, *nargs).await?;
                context.pc += 1;
            }

            Instruction::Dim(span) => {
                self.symbols
                    .dim(&span.name, span.vtype)
                    .map_err(|e| Error::from_value_error(e, span.name_pos))?;
                context.pc += 1;
            }

            Instruction::DimArray(span) => {
                self.dim_array(context, span)?;
                context.pc += 1;
            }

            Instruction::End(has_code) => {
                self.end(context, *has_code)?;
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

            Instruction::JumpIfTrue(span) => {
                let (arg, pos) = context.value_stack.pop().unwrap();
                match arg {
                    Value::Boolean(false) => context.pc += 1,
                    Value::Boolean(true) => context.pc = span.addr,
                    _ => {
                        return new_syntax_error(pos, span.error_msg);
                    }
                }
            }

            Instruction::JumpIfNotTrue(span) => {
                let (arg, pos) = context.value_stack.pop().unwrap();
                match arg {
                    Value::Boolean(true) => context.pc += 1,
                    Value::Boolean(false) => context.pc = span.addr,
                    _ => {
                        return new_syntax_error(pos, span.error_msg);
                    }
                }
            }

            Instruction::Load(vref, pos) => {
                let value = match self
                    .symbols
                    .get(vref)
                    .map_err(|e| Error::from_value_error(e, *pos))?
                {
                    Some(Symbol::Variable(v)) => v.clone(),
                    Some(Symbol::Callable(f)) => {
                        if !f.metadata().is_argless() {
                            return new_syntax_error(
                                *pos,
                                format!("{} requires one or more arguments", vref.name()),
                            );
                        }
                        let f = f.clone();
                        self.argless_function_call(vref.clone(), *pos, f).await?
                    }
                    Some(_) => {
                        return new_syntax_error(*pos, format!("{} is not a variable", vref.name()))
                    }
                    None => {
                        return new_syntax_error(
                            *pos,
                            format!("Undefined variable {}", vref.name()),
                        )
                    }
                };
                context.value_stack.push((value, *pos));
                context.pc += 1;
            }

            Instruction::LoadRef(vref, pos) => {
                let sym = self.symbols.get(vref).map_err(|e| Error::from_value_error(e, *pos))?;
                if let Some(Symbol::Callable(f)) = sym {
                    if f.metadata().is_argless() {
                        let f = f.clone();
                        let value = self.argless_function_call(vref.clone(), *pos, f).await?;
                        context.value_stack.push((value, *pos));
                        context.pc += 1;
                        return Ok(());
                    }
                };

                context.value_stack.push((Value::VarRef(vref.clone()), *pos));
                context.pc += 1;
            }

            Instruction::Nop => {
                context.pc += 1;
            }

            Instruction::Push(value, pos) => {
                context.value_stack.push((value.clone(), *pos));
                context.pc += 1;
            }

            Instruction::Return(pos) => match context.addr_stack.pop() {
                Some(addr) => context.pc = addr,
                None => return new_syntax_error(*pos, "No address to return to".to_owned()),
            },

            Instruction::SetErrorHandler(span) => {
                context.err_handler = *span;
                context.pc += 1;
            }

            Instruction::Unset(span) => {
                self.symbols.unset(&span.name).map_err(|e| Error::from_value_error(e, span.pos))?;
                context.pc += 1;
            }
        }

        Ok(())
    }

    /// Executes a single instruction in `instrs` as pointed to by the program counter in `context`.
    async fn exec_one(&mut self, context: &mut Context, instrs: &[Instruction]) -> Result<()> {
        let mut result = self.exec_safe(context, instrs).await;
        if let Err(e) = result.as_ref() {
            if e.is_catchable() {
                self.symbols
                    .set_var(&VarRef::new("0errmsg", VarType::Text), Value::Text(format!("{}", e)))
                    .expect("Internal symbol must be of a specific type");

                match context.err_handler {
                    ErrorHandlerISpan::Jump(addr) => {
                        context.pc = addr;
                        result = Ok(());
                    }
                    ErrorHandlerISpan::None => (),
                    ErrorHandlerISpan::ResumeNext => {
                        if instrs[context.pc].is_statement() {
                            context.pc += 1;
                        } else {
                            loop {
                                context.pc += 1;
                                if context.pc >= instrs.len() {
                                    break;
                                } else if instrs[context.pc].is_statement() {
                                    context.pc += 1;
                                    break;
                                }
                            }
                        }
                        result = Ok(());
                    }
                }
            }
        }
        result
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
        let mut result = Ok(());
        while result.is_ok() && context.pc < image.instrs.len() && !self.should_stop().await {
            result = self.exec_one(&mut context, &image.instrs).await;
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
        machine.add_callable(GetDataCommand::new(captured_data.clone()));

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
        machine.add_callable(ArglessFunction::new(Value::Integer(1234)));
        machine.add_callable(ClearCommand::new());
        machine.add_callable(CountFunction::new());
        machine.add_callable(GetHiddenFunction::new());
        machine.add_callable(InCommand::new(Box::from(RefCell::from(golden_in.iter()))));
        machine.add_callable(OutCommand::new(captured_out.clone()));
        machine.add_callable(OutfFunction::new(captured_out));
        machine.add_callable(RaiseCommand::new());
        machine.add_callable(RaisefFunction::new());
        machine.add_callable(SumFunction::new());
        machine.add_callable(TypeCheckFunction::new(Value::Integer(5)));
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
    fn test_assignment_array_access_with_varref() {
        do_ok_test("DIM a(1)\na(0) = 123\ni = 0\nr = a(i)\nOUT r", &[], &["123"]);
    }

    #[test]
    fn test_assignment_argless_function_call() {
        do_ok_test("a = SUM(3, COUNT, 5)\nOUT a", &[], &["9"]);
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
    fn test_dim_array_varref_ok() {
        do_ok_test("i = 3\nDIM foo(i)\nOUT foo%(2)", &[], &["0"]);
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
        machine.add_callable(OutCommand::new(captured_out.clone()));
        machine.add_callable(SumFunction::new());

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
    fn test_do_infinite_ok() {
        let code = r#"
            IN n
            DO
                IF n = 0 THEN: EXIT DO: END IF
                OUT "n is"; n
                n = n - 1
            LOOP
        "#;
        do_ok_test(code, &["0"], &[]);
        do_ok_test(code, &["3"], &["n is 3", "n is 2", "n is 1"]);
    }

    #[test]
    fn test_do_pre_until_ok() {
        let code = r#"
            IN n
            DO UNTIL n = 0
                OUT "n is"; n
                n = n - 1
            LOOP
        "#;
        do_ok_test(code, &["0"], &[]);
        do_ok_test(code, &["3"], &["n is 3", "n is 2", "n is 1"]);

        do_ok_test("DO UNTIL TRUE\nOUT 1\nLOOP", &[], &[]);
    }

    #[test]
    fn test_do_pre_while_ok() {
        let code = r#"
            IN n
            DO WHILE n > 0
                OUT "n is"; n
                n = n - 1
            LOOP
        "#;
        do_ok_test(code, &["0"], &[]);
        do_ok_test(code, &["3"], &["n is 3", "n is 2", "n is 1"]);

        do_ok_test("DO WHILE FALSE\nOUT 1\nLOOP", &[], &[]);
    }

    #[test]
    fn test_do_post_until_ok() {
        let code = r#"
            IN n
            DO
                OUT "n is"; n
                n = n - 1
            LOOP UNTIL n = 0
        "#;
        do_ok_test(code, &["1"], &["n is 1"]);
        do_ok_test(code, &["3"], &["n is 3", "n is 2", "n is 1"]);

        do_ok_test("DO\nOUT 1\nLOOP UNTIL TRUE", &[], &["1"]);
    }

    #[test]
    fn test_do_post_while_ok() {
        let code = r#"
            IN n
            DO
                OUT "n is"; n
                n = n - 1
            LOOP WHILE n > 0
        "#;
        do_ok_test(code, &["1"], &["n is 1"]);
        do_ok_test(code, &["3"], &["n is 3", "n is 2", "n is 1"]);

        do_ok_test("DO\nOUT 1\nLOOP WHILE FALSE", &[], &["1"]);
    }

    #[test]
    fn test_do_errors() {
        do_simple_error_test("DO WHILE 2\nLOOP", "1:10: DO requires a boolean condition");
    }

    #[test]
    fn test_exit_do() {
        do_ok_test(
            r#"
            i = 5
            DO WHILE i > 0
                j = 2
                DO UNTIL j = 0
                    OUT i; j
                    IF i = 3 AND j = 2 THEN: EXIT DO: END IF
                    j = j - 1
                LOOP
                IF i = 2 THEN: EXIT DO: END IF
                i = i - 1
            LOOP
            "#,
            &[],
            &["5 2", "5 1", "4 2", "4 1", "3 2", "2 2", "2 1"],
        );
    }

    #[test]
    fn test_exit_do_sequential() {
        do_ok_test(
            r#"
            i = 2
            DO WHILE i > 0
                OUT "First"; i
                i = i - 1
            LOOP
            i = 2
            DO WHILE i > 0
                OUT "Second"; i
                i = i - 1
            LOOP
            "#,
            &[],
            &["First 2", "First 1", "Second 2", "Second 1"],
        );
    }

    #[test]
    fn test_exit_do_nested_indirectly() {
        do_ok_test(
            r#"
            i = 5
            DO WHILE i > 0
                GOSUB @another
                IF i = 2 THEN: EXIT DO: END IF
                i = i - 1
            LOOP
            GOTO @end
            @another
            j = 2
            DO UNTIL j = 0
                OUT i; j
                IF i = 3 AND j = 2 THEN: EXIT DO: END IF
                j = j - 1
            LOOP
            RETURN
            @end
            "#,
            &[],
            &["5 2", "5 1", "4 2", "4 1", "3 2", "2 2", "2 1"],
        );
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
        do_simple_error_test("IF TRUE THEN END IF", "1:14: END IF without IF");
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
        do_ok_test("x = FALSE: OUT x: y = ARGLESS: OUT y", &[], &["FALSE", "1234"]);
    }

    #[test]
    fn test_function_call_errors() {
        do_simple_error_test("TYPE_CHECK", "1:1: TYPE_CHECK is not a command");
        do_simple_error_test("SUM(3)", "1:1: SUM is not a command");
        do_simple_error_test("OUT CLEAR", "1:5: CLEAR is not an array nor a function");
        do_simple_error_test("OUT CLEAR()", "1:5: CLEAR is not an array nor a function");
        do_simple_error_test("OUT OUT()", "1:5: OUT is not an array nor a function");
        do_simple_error_test("OUT OUT(3)", "1:5: OUT is not an array nor a function");
        do_simple_error_test("OUT SUM?()", "1:5: Incompatible types in SUM? reference");
        do_simple_error_test(
            "OUT TYPE_CHECK",
            "1:5: Value returned by TYPE_CHECK is incompatible with its type definition",
        );
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
            OUT RAISEF("syntax")
            OUT 2
            100 OUT GETHIDDEN("0ERRMSG")
            "#,
            &[],
            &["1", "4:17: In call to RAISEF: expected arg1$"],
        );
    }

    #[test]
    fn test_on_error_goto_label() {
        do_ok_test(
            r#"
            ON ERROR GOTO @foo
            OUT 1
            OUT RAISEF("syntax")
            OUT 2
            @foo
            OUT GETHIDDEN("0ERRMSG")
            "#,
            &[],
            &["1", "4:17: In call to RAISEF: expected arg1$"],
        );
    }

    #[test]
    fn test_on_error_reset() {
        do_error_test(
            r#"
            ON ERROR GOTO @foo
            OUT 1
            OUT RAISEF("syntax")
            @foo
            ON ERROR GOTO 0
            OUT 2
            OUT RAISEF("syntax")
            "#,
            &[],
            &["1", "2"],
            "8:17: In call to RAISEF: expected arg1$",
        );
    }

    #[test]
    fn test_on_error_resume_next_line_function_failure() {
        do_ok_test(
            r#"
            ON ERROR RESUME NEXT
            OUT 1
            OUT RAISEF("syntax")
            OUT GETHIDDEN("0ERRMSG")
            "#,
            &[],
            &["1", "4:17: In call to RAISEF: expected arg1$"],
        );
    }

    #[test]
    fn test_on_error_resume_next_line_command_failure() {
        do_ok_test(
            r#"
            ON ERROR RESUME NEXT
            OUT 1
            RAISE "syntax"
            OUT GETHIDDEN("0ERRMSG")
            "#,
            &[],
            &["1", "4:13: In call to RAISE: expected arg1$"],
        );
    }

    #[test]
    fn test_on_error_resume_next_statement_function_failure() {
        do_ok_test(
            r#"
            ON ERROR RESUME NEXT
            OUT 1: OUT RAISEF("syntax"): OUT GETHIDDEN("0ERRMSG")
            "#,
            &[],
            &["1", "3:24: In call to RAISEF: expected arg1$"],
        );
    }

    #[test]
    fn test_on_error_resume_next_statement_command_failure() {
        do_ok_test(
            r#"
            ON ERROR RESUME NEXT
            OUT 1: RAISE "syntax": OUT GETHIDDEN("0ERRMSG")
            "#,
            &[],
            &["1", "3:20: In call to RAISE: expected arg1$"],
        );
    }

    #[test]
    fn test_on_error_types() {
        do_ok_test(
            r#"ON ERROR RESUME NEXT: OUT RAISEF("argument"): OUT GETHIDDEN("0ERRMSG")"#,
            &[],
            &["1:27: In call to RAISEF: 1:34: Bad argument"],
        );

        do_ok_test(
            r#"ON ERROR RESUME NEXT: OUT RAISEF("eval"): OUT GETHIDDEN("0ERRMSG")"#,
            &[],
            &["1:27: In call to RAISEF: 1:34: Some eval error"],
        );

        do_ok_test(
            r#"ON ERROR RESUME NEXT: OUT RAISEF("internal"): OUT GETHIDDEN("0ERRMSG")"#,
            &[],
            &["1:27: In call to RAISEF: 1:34: Some internal error"],
        );

        do_ok_test(
            r#"ON ERROR RESUME NEXT: OUT RAISEF("io"): OUT GETHIDDEN("0ERRMSG")"#,
            &[],
            &["1:27: In call to RAISEF: Some I/O error"],
        );

        do_ok_test(
            r#"ON ERROR RESUME NEXT: OUT RAISEF("syntax"): OUT GETHIDDEN("0ERRMSG")"#,
            &[],
            &["1:27: In call to RAISEF: expected arg1$"],
        );
    }

    #[test]
    fn test_select_ok() {
        let code = r#"
            IN n
            SELECT CASE n
                CASE 1, 3, 5, 7, 9: OUT "Odd"
                CASE 0, 2, 4, 6, 8: OUT "Even"
                CASE 10 TO 20: OUT "Large"
                CASE IS < 0: OUT "Negative"
                CASE ELSE: OUT "Too large"
            END SELECT
        "#;
        do_ok_test(code, &["3"], &["Odd"]);
        do_ok_test(code, &["5"], &["Odd"]);
        do_ok_test(code, &["0"], &["Even"]);
        do_ok_test(code, &["8"], &["Even"]);
        do_ok_test(code, &["10"], &["Large"]);
        do_ok_test(code, &["15"], &["Large"]);
        do_ok_test(code, &["20"], &["Large"]);
        do_ok_test(code, &["-1"], &["Negative"]);
        do_ok_test(code, &["21"], &["Too large"]);
        do_ok_test(code, &["10000"], &["Too large"]);
    }

    #[test]
    fn test_select_test_expression_evaluated_only_once() {
        let code = r#"
            SELECT CASE COUNT
                CASE 100: OUT "Not hit"
                CASE 200: OUT "Not hit"
                CASE ELSE: OUT "Giving up"
            END SELECT
            OUT COUNT
        "#;
        do_ok_test(code, &[], &["Giving up", "2"]);
    }

    #[test]
    fn test_select_test_expression_evaluated_once_even_if_no_cases() {
        let code = r#"
            SELECT CASE COUNT
            END SELECT
            OUT COUNT
        "#;
        do_ok_test(code, &[], &["2"]);
    }

    #[test]
    fn test_select_test_expression_evaluated_once_even_if_no_matches() {
        let code = r#"
            SELECT CASE COUNT
                CASE 0: OUT "Not hit"
                CASE 3
            END SELECT
            OUT COUNT
        "#;
        do_ok_test(code, &[], &["2"]);
    }

    #[test]
    fn test_select_strings() {
        let code = r#"
            IN s$
            SELECT CASE s$
                CASE "exact": OUT "Exact match"
                CASE IS > "ZZZ": OUT "IS match"
                CASE "B" TO "Y": OUT "TO match"
            END SELECT
        "#;
        do_ok_test(code, &["exact"], &["Exact match"]);
        do_ok_test(code, &["ZZZ"], &[]);
        do_ok_test(code, &["ZZZa"], &["IS match"]);
        do_ok_test(code, &["A"], &[]);
        do_ok_test(code, &["B"], &["TO match"]);
        do_ok_test(code, &["M"], &["TO match"]);
        do_ok_test(code, &["Y"], &["TO match"]);
        do_ok_test(code, &["Z"], &[]);
    }

    #[test]
    fn test_select_double_to_integer() {
        let code = r#"
            IN n#
            SELECT CASE n#
                CASE 2: OUT "OK 1"
                CASE IS > 5: OUT "OK 2"
            END SELECT
        "#;
        do_ok_test(code, &["1.9"], &[]);
        do_ok_test(code, &["2.0"], &["OK 1"]);
        do_ok_test(code, &["2.1"], &[]);
        do_ok_test(code, &["5.0"], &[]);
        do_ok_test(code, &["5.1"], &["OK 2"]);
    }

    #[test]
    fn test_select_integer_to_double() {
        let code = r#"
            IN n%
            SELECT CASE n%
                CASE 2.0: OUT "OK 1"
                CASE 5.0, -1.0: OUT "OK 2"
                CASE 10.2 TO 11.8: OUT "OK 3"
            END SELECT
        "#;
        do_ok_test(code, &["2"], &["OK 1"]);
        do_ok_test(code, &["5"], &["OK 2"]);
        do_ok_test(code, &["-1"], &["OK 2"]);
        do_ok_test(code, &["10"], &[]);
        do_ok_test(code, &["11"], &["OK 3"]);
        do_ok_test(code, &["12"], &[]);
    }

    #[test]
    fn test_select_no_test_var_leaks() {
        let code = r#"
            i = 0
            SELECT CASE 5 + 1
                CASE 6: i = i + 3
            END SELECT

            SELECT CASE TRUE
                CASE TRUE: i = i + 1
            END SELECT
        "#;

        let mut machine = Machine::default();
        assert_eq!(StopReason::Eof, block_on(machine.exec(&mut code.as_bytes())).unwrap());
        assert_eq!(1, machine.get_symbols().as_hashmap().len());
        assert_eq!(4, machine.get_var_as_int("I").unwrap());
    }

    #[test]
    fn test_select_clear_causes_internal_error() {
        let code = r#"
            SELECT CASE 4
                CASE 4: CLEAR
            END SELECT
        "#;

        let mut machine = Machine::default();
        machine.add_callable(ClearCommand::new());
        let e = block_on(machine.exec(&mut code.as_bytes())).unwrap_err();
        // This is a corner case of how the current implementation uses "hidden" variables to hold
        // the test expression and a `clear()` can unset this variable.  We could try to be better
        // here, but I'd say that if a program is issuing a `clear()` halfway through its execution,
        // it is bound to suffer from issues anyway so it's not worth improving this.
        assert_eq!("4:13: 0select1 is not defined", format!("{}", e));
    }

    #[test]
    fn test_select_nested() {
        let code = r#"
            i = 5
            SELECT CASE i
                CASE 5
                    OUT "OK 1"
                    i = 6
                    SELECT CASE i
                        CASE 6
                            OUT "OK 2"
                    END SELECT
                CASE 6
                    OUT "Not OK"
            END SELECT
        "#;
        do_ok_test(code, &[], &["OK 1", "OK 2"]);
    }

    #[test]
    fn test_select_nested_indirectly() {
        let code = r#"
            i = 5
            SELECT CASE i
                CASE 5
                    OUT "OK 1"
                    GOSUB @another
                CASE 6
                    OUT "Not OK"
            END SELECT
            GOTO @end
            @another
            i = 6
            SELECT CASE i
                CASE 6
                    OUT "OK 2"
            END SELECT
            RETURN
            @end
        "#;
        do_ok_test(code, &[], &["OK 1", "OK 2"]);
    }

    #[test]
    fn test_select_errors() {
        do_simple_error_test(
            "SELECT CASE\nEND SELECT",
            "1:12: No expression in SELECT CASE statement",
        );
        do_simple_error_test("SELECT CASE\nEND IF", "1:1: SELECT without END SELECT");
        do_simple_error_test("\n\n\nSELECT CASE 2\n", "4:1: SELECT without END SELECT");

        do_simple_error_test(
            "SELECT CASE 2\nCASE FALSE\nEND SELECT",
            "2:6: Cannot compare 2 and FALSE with =",
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
