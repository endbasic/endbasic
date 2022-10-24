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
use crate::eval;
use crate::parser;
use crate::reader::LineCol;
use crate::syms::{CallError, CallableMetadata, Command, Function, Symbol, Symbols};
use crate::value;
use async_recursion::async_recursion;
use std::collections::HashSet;
use std::io;
use std::rc::Rc;

/// Execution errors.
#[derive(Debug, thiserror::Error)]
pub enum Error {
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
}

/// Result for execution return values.
pub type Result<T> = std::result::Result<T, Error>;

/// Instantiates a new `Err(Error::SyntaxError(...))` from a message.  Syntactic sugar.
fn new_syntax_error<T, S: Into<String>>(pos: LineCol, message: S) -> Result<T> {
    Err(Error::SyntaxError(pos, message.into()))
}

/// Describes how the machine stopped execution while it was running a script via `exec()`.
#[derive(Clone, Debug, Eq, PartialEq)]
#[must_use]
pub enum StopReason {
    /// Execution terminates because the machine reached the end of the input.
    Eof,

    /// Execution terminated because the machine was asked to terminate with `exit()`.
    Exited(u8),
}

impl StopReason {
    /// Converts the stop reason into a process exit code.
    pub fn as_exit_code(&self) -> i32 {
        match self {
            StopReason::Eof => 0,
            StopReason::Exited(i) => *i as i32,
        }
    }
}

/// Trait for objects that maintain state that can be reset to defaults.
pub trait Clearable {
    /// Resets any state held by the object to default values.  `syms` contain the symbols of the
    /// machine before they are cleared, in case some state is held in them too.
    fn reset_state(&self, syms: &mut Symbols);
}

/// Executes an EndBASIC program and tracks its state.
#[derive(Default)]
pub struct Machine {
    symbols: Symbols,
    clearables: Vec<Box<dyn Clearable>>,
    stop_reason: Option<StopReason>,
    pending_goto: Option<GotoSpan>,
}

impl Machine {
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

    /// Resets the state of the machine by clearing all variable.
    pub fn clear(&mut self) {
        for clearable in self.clearables.as_slice() {
            clearable.reset_state(&mut self.symbols);
        }
        self.symbols.clear();
    }

    /// Tells the machine to stop execution at the next statement boundary.
    ///
    /// The `exec()` call that's stopped by this invocation will return the `code` given to this
    /// call.
    pub fn exit(&mut self, code: u8) {
        self.stop_reason = Some(StopReason::Exited(code));
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

    /// Executes a `FOR` loop.
    async fn do_for(&mut self, span: &ForSpan) -> Result<()> {
        debug_assert!(
            span.iter.ref_type() == VarType::Auto || span.iter.ref_type() == VarType::Integer
        );
        let start_value = span.start.eval(&mut self.symbols).await?;
        match start_value {
            Value::Integer(_) => self
                .symbols
                .set_var(&span.iter, start_value)
                .map_err(|e| Error::from_value_error(e, span.start.start_pos()))?,
            _ => {
                return new_syntax_error(
                    span.start.start_pos(),
                    "FOR supports integer iteration only",
                )
            }
        }

        loop {
            match span.end.eval(&mut self.symbols).await? {
                Value::Boolean(false) => {
                    break;
                }
                Value::Boolean(true) => (),
                _ => panic!("Built-in condition should have evaluated to a boolean"),
            }

            self.exec_multiple(&span.body).await?;
            if self.pending_goto.is_some() {
                break;
            }

            let next_value = span.next.eval(&mut self.symbols).await?;
            self.symbols
                .set_var(&span.iter, next_value)
                .map_err(|e| Error::from_value_error(e, span.next.start_pos()))?;
        }
        Ok(())
    }

    /// Executes an `IF` statement.
    async fn do_if(&mut self, span: &IfSpan) -> Result<()> {
        for branch in &span.branches {
            match branch.guard.eval(&mut self.symbols).await? {
                Value::Boolean(true) => {
                    self.exec_multiple(&branch.body).await?;
                    break;
                }
                Value::Boolean(false) => (),
                _ => {
                    return new_syntax_error(
                        branch.guard.start_pos(),
                        "IF/ELSEIF require a boolean condition",
                    )
                }
            };
        }
        Ok(())
    }

    /// Executes a `WHILE` loop.
    async fn do_while(&mut self, span: &WhileSpan) -> Result<()> {
        loop {
            match span.expr.eval(&mut self.symbols).await? {
                Value::Boolean(true) => {
                    self.exec_multiple(&span.body).await?;
                    if self.pending_goto.is_some() {
                        break;
                    }
                }
                Value::Boolean(false) => break,
                _ => {
                    return new_syntax_error(
                        span.expr.start_pos(),
                        "WHILE requires a boolean condition",
                    )
                }
            }
        }
        Ok(())
    }

    /// Executes a collection of statements.
    ///
    /// All callers of this function should inspect `self.pending_goto` to see if it is set after
    /// this completes.  If that's the case, the callers must unwind processing as soon as possible
    /// so that the target of the `GOTO` can be found.
    #[async_recursion(?Send)]
    async fn exec_multiple(&mut self, stmts: &[Statement]) -> Result<()> {
        let mut seen_labels = HashSet::<String>::default();
        let mut i = 0;
        while i < stmts.len() || self.pending_goto.is_some() {
            if self.stop_reason.is_some() {
                return Ok(());
            }

            if let Some(GotoSpan { target, .. }) = self.pending_goto.as_ref() {
                i = 0;
                seen_labels.clear();
                while i < stmts.len() {
                    if let Statement::Label(span) = &stmts[i] {
                        let ok = seen_labels.insert(span.name.clone());
                        assert!(ok, "Duplicate label found but not caught during execution");
                        if target == &span.name {
                            i += 1;
                            self.pending_goto = None;
                            break;
                        }
                    }
                    i += 1;
                }
                if i == stmts.len() {
                    return Ok(());
                }
            }

            match &stmts[i] {
                Statement::ArrayAssignment(span) => self.assign_array(span).await?,
                Statement::Assignment(span) => self.assign(span).await?,
                Statement::BuiltinCall(span) => self.call_builtin(span).await?,
                Statement::Dim(span) => self
                    .symbols
                    .dim(&span.name, span.vtype)
                    .map_err(|e| Error::from_value_error(e, span.name_pos))?,
                Statement::DimArray(span) => self.dim_array(span).await?,
                Statement::For(span) => self.do_for(span).await?,
                Statement::Goto(span) => self.pending_goto = Some(span.clone()),
                Statement::If(span) => self.do_if(span).await?,
                Statement::Label(span) => {
                    if !seen_labels.insert(span.name.clone()) {
                        return new_syntax_error(
                            span.name_pos,
                            format!("Duplicate label {} at this level", span.name),
                        );
                    }
                }
                Statement::While(span) => self.do_while(span).await?,
            }

            i += 1;
        }
        Ok(())
    }

    /// Executes a program extracted from the `input` readable.
    ///
    /// Note that this does not consume `self`.  As a result, it is possible to execute multiple
    /// different programs on the same machine, all sharing state.
    pub async fn exec(&mut self, input: &mut dyn io::Read) -> Result<StopReason> {
        debug_assert!(self.stop_reason.is_none());
        let stmts = parser::parse(input)?;
        self.exec_multiple(&stmts).await?;
        if let Some(span) = self.pending_goto.take() {
            return new_syntax_error(span.target_pos, format!("Unknown label {}", span.target));
        }
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
        machine.add_command(ExitCommand::new());
        machine.add_command(InCommand::new(Box::from(RefCell::from(golden_in.iter()))));
        machine.add_command(OutCommand::new(captured_out));
        machine.add_function(SumFunction::new());
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

        do_ok_test("a = 3\nOUT a; a%", &[], &["3 3"]);
        do_ok_test("a% = 3\nOUT a; a%", &[], &["3 3"]);

        do_ok_test("a = \"some text\"\nOUT a; a$", &[], &["some text some text"]);
        do_ok_test("a$ = \"some text\"\nOUT a; a$", &[], &["some text some text"]);

        do_ok_test("a = 1\na = a + 1\nOUT a", &[], &["2"]);
    }

    #[test]
    fn test_assignment_ok_case_insensitive() {
        do_ok_test("foo = 32\nOUT FOO", &[], &["32"]);
    }

    #[test]
    fn test_assignment_errors() {
        do_simple_error_test("a =\n", "1:4: Missing expression in assignment");
        do_simple_error_test("a = b\n", "1:5: Undefined variable b");
        do_simple_error_test("a = 3\na = TRUE\n", "2:1: Incompatible types in a assignment");
        do_simple_error_test("a? = 3", "1:1: Incompatible types in a? assignment");
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
    fn test_exit_simple() {
        let captured_out = Rc::from(RefCell::from(vec![]));
        assert_eq!(
            StopReason::Exited(5),
            run("OUT 1\nEXIT 5\nOUT 2", &[], captured_out.clone()).expect("Execution failed")
        );
        assert_eq!(&["1"], captured_out.borrow().as_slice());
    }

    #[test]
    fn test_exit_zero_is_not_special() {
        let captured_out = Rc::from(RefCell::from(vec![]));
        assert_eq!(
            StopReason::Exited(0),
            run("OUT 1\nOUT 2\nEXIT 0\nOUT 3", &[], captured_out.clone())
                .expect("Execution failed")
        );
        assert_eq!(&["1", "2"], captured_out.borrow().as_slice());
    }

    #[test]
    fn test_exit_nested() {
        let captured_out = Rc::from(RefCell::from(vec![]));
        assert_eq!(
            StopReason::Exited(42),
            run(
                "FOR a = 0 TO 10\nOUT a\nIF a = 3 THEN\nEXIT 42\nOUT \"no\"\nEND IF\nNEXT",
                &[],
                captured_out.clone()
            )
            .expect("Execution failed")
        );
        assert_eq!(&["0", "1", "2", "3"], captured_out.borrow().as_slice());
    }

    #[test]
    fn test_exit_can_resume() {
        let captured_out = Rc::from(RefCell::from(vec![]));
        let mut machine = Machine::default();
        machine.add_command(ExitCommand::new());
        machine.add_command(OutCommand::new(captured_out.clone()));
        machine.add_function(SumFunction::new());

        assert_eq!(
            StopReason::Exited(10),
            block_on(machine.exec(&mut "OUT 1\nEXIT 10\nOUT 2".as_bytes()))
                .expect("Execution failed")
        );
        assert_eq!(&["1"], captured_out.borrow().as_slice());

        captured_out.borrow_mut().clear();
        assert_eq!(
            StopReason::Exited(11),
            block_on(machine.exec(&mut "OUT 2\nEXIT 11\nOUT 3".as_bytes()))
                .expect("Execution failed")
        );
        assert_eq!(&["2"], captured_out.borrow().as_slice());
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
        let code = r#"
            IN first
            IN last
            FOR a = first TO last
                OUT "a is"; a
            NEXT
        "#;
        do_ok_test(code, &["0", "0"], &["a is 0"]);
        do_ok_test(code, &["0", "3"], &["a is 0", "a is 1", "a is 2", "a is 3"]);
    }

    #[test]
    fn test_for_incrementing_with_step() {
        let code = r#"
            IN first
            IN last
            FOR a = first TO last STEP 3
                OUT "a is"; a
            NEXT
        "#;
        do_ok_test(code, &["0", "0"], &["a is 0"]);
        do_ok_test(code, &["0", "2"], &["a is 0"]);
        do_ok_test(code, &["0", "3"], &["a is 0", "a is 3"]);
        do_ok_test(code, &["0", "10"], &["a is 0", "a is 3", "a is 6", "a is 9"]);
    }

    #[test]
    fn test_for_decrementing_with_step() {
        let code = r#"
            IN first
            IN last
            FOR a = first TO last STEP -2
                OUT "a is"; a
            NEXT
        "#;
        do_ok_test(code, &["0", "0"], &["a is 0"]);
        do_ok_test(code, &["2", "0"], &["a is 2", "a is 0"]);
        do_ok_test(code, &["-2", "-6"], &["a is -2", "a is -4", "a is -6"]);
        do_ok_test(code, &["10", "1"], &["a is 10", "a is 8", "a is 6", "a is 4", "a is 2"]);
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
        do_simple_error_test("FOR a = 1 TO 10\nEND IF", "2:1: Unexpected END in statement");

        do_simple_error_test(
            "FOR i = \"a\" TO 3\nNEXT",
            "1:9: FOR supports integer iteration only",
        );
        do_simple_error_test(
            "FOR i = 1 TO \"a\"\nNEXT",
            "1:11: Cannot compare 1 and \"a\" with <=",
        );

        do_simple_error_test(
            "FOR i = \"b\" TO 7 STEP -8\nNEXT",
            "1:9: FOR supports integer iteration only",
        );
        do_simple_error_test(
            "FOR i = 1 TO \"b\" STEP -8\nNEXT",
            "1:11: Cannot compare 1 and \"b\" with >=",
        );

        do_simple_error_test(
            "FOR a = 1.0 TO 10.0\nNEXT",
            "1:9: FOR supports integer iteration only",
        );
    }

    #[test]
    fn test_function_call_ok() {
        do_ok_test("x = 3\nOUT SUM(x, Sum%(4, 5), 1, sum())", &[], &["13"]);
    }

    #[test]
    fn test_function_call_errors() {
        do_simple_error_test("OUT OUT()", "1:5: OUT is not an array or a function");
        do_simple_error_test("OUT SUM?()", "1:5: Incompatible types in SUM? reference");
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
    fn test_goto_nested_cannot_go_down() {
        do_simple_error_test(
            "IF TRUE THEN: GOTO @sibling: END IF: IF TRUE THEN: @sibling: OUT 1: END IF",
            "1:20: Unknown label sibling",
        );
    }

    #[test]
    fn test_goto_as_last_statement() {
        let captured_out = Rc::from(RefCell::from(vec![]));
        assert_eq!(
            StopReason::Exited(5),
            run(
                "i = 0: @a: IF i = 5 THEN: EXIT i: END IF: i = i + 1: GOTO @a",
                &[],
                captured_out.clone()
            )
            .expect("Execution failed")
        );
        assert!(captured_out.borrow().is_empty());
    }

    #[test]
    fn test_goto_errors() {
        do_simple_error_test("GOTO @foo", "1:6: Unknown label foo");
    }

    #[test]
    fn test_label_ok() {
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
        do_ok_test("@foo: IF TRUE THEN: @foo: END IF", &[], &[]);
        do_ok_test("IF TRUE THEN: @foo: END IF: IF TRUE THEN: @foo: END IF", &[], &[]);

        do_simple_error_test("@foo: @bar: @foo", "1:13: Duplicate label foo at this level");

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
            "8:25: Duplicate label a at this level",
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
        do_simple_error_test("WHILE\nEND IF", "1:1: WHILE without WEND");

        do_simple_error_test("\n\n\nWHILE 2\n", "4:1: WHILE without WEND");
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
