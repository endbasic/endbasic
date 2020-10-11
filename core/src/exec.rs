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

use crate::ast::{ArgSep, Expr, Statement, Value, VarRef, VarType};
use crate::eval::{self, Vars};
use crate::parser::{self, Parser};
use async_trait::async_trait;
use futures_lite::future::FutureExt;
use std::collections::HashMap;
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

    /// Parsing error during execution.
    #[error("{0}")]
    ParseError(#[from] parser::Error),

    /// Syntax error.
    #[error("{0}")]
    SyntaxError(String),

    /// Execution of a builtin command failed due to a user call error.
    #[error("{0}")]
    UsageError(String),
}

/// Result for execution return values.
pub type Result<T> = std::result::Result<T, Error>;

/// Instantiates a new `Err(Error::SyntaxError(...))` from a message.  Syntactic sugar.
fn new_syntax_error<T, S: Into<String>>(message: S) -> Result<T> {
    Err(Error::SyntaxError(message.into()))
}

/// Instantiates a new `Err(Error::UsageError(...))` from a message.  Syntactic sugar.
pub fn new_usage_error<T, S: Into<String>>(message: S) -> Result<T> {
    Err(Error::UsageError(message.into()))
}

/// A trait to define a command that is executed by a `Machine`.
///
/// The commands themselves are immutable but they can reference mutable state.  Given that
/// EndBASIC is not threaded, it is sufficient for those references to be behind a `RefCell`
/// and/or an `Rc`.
#[async_trait(?Send)]
pub trait BuiltinCommand {
    /// Returns the name of the command, all in uppercase letters.
    fn name(&self) -> &'static str;

    /// Returns a specification of the command's syntax.
    fn syntax(&self) -> &'static str;

    /// Returns the usage message of the command.
    fn description(&self) -> &'static str;

    /// Executes the command.
    ///
    /// `args` contains the arguments as provided in the invocation of the command.  Each entry in
    /// this array contains an optional expression (to support things like `PRINT a, , b`) and the
    /// separator that was used between that argument and the next.  The last entry in `args` always
    /// has `ArgSep::End` as the separator.
    ///
    /// `machine` provides mutable access to the current state of the machine invoking the command.
    ///
    /// Commands cannot return any value except for errors.
    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Result<()>;
}

/// Builder pattern for a new machine.
///
/// The `default` constructor creates a new builder for a machine with no builtin commands.
#[derive(Default)]
pub struct MachineBuilder {
    builtins: HashMap<&'static str, Rc<dyn BuiltinCommand>>,
}

impl MachineBuilder {
    /// Registers the given builtin command, which must not yet be registered.
    pub fn add_builtin(mut self, command: Rc<dyn BuiltinCommand>) -> Self {
        assert!(
            command.name() == command.name().to_ascii_uppercase(),
            "Command name must be in uppercase"
        );
        assert!(
            self.builtins.get(&command.name()).is_none(),
            "Command with the same name already registered"
        );
        for l in command.description().lines() {
            assert!(!l.is_empty(), "Description cannot contain empty lines");
        }
        self.builtins.insert(command.name(), command);
        self
    }

    /// Registers the given builtin commands.  See `add_builtin` for more details.
    pub fn add_builtins(mut self, commands: Vec<Rc<dyn BuiltinCommand>>) -> Self {
        for command in commands {
            self = self.add_builtin(command);
        }
        self
    }

    /// Creates a new machine with the current configuration.
    pub fn build(self) -> Machine {
        Machine { builtins: self.builtins, vars: Vars::default() }
    }
}

/// Executes an EndBASIC program and tracks its state.
#[derive(Default)]
pub struct Machine {
    builtins: HashMap<&'static str, Rc<dyn BuiltinCommand>>,
    vars: Vars,
}

impl Machine {
    /// Resets the state of the machine by clearing all variable.
    pub fn clear(&mut self) {
        self.vars.clear()
    }

    /// Obtains immutable access to the builtins supported by this machine.
    pub fn get_builtins(&self) -> &HashMap<&'static str, Rc<dyn BuiltinCommand>> {
        &self.builtins
    }

    /// Obtains immutable access to the state of the variables.
    pub fn get_vars(&self) -> &Vars {
        &self.vars
    }

    /// Obtains mutable access to the state of the variables.
    pub fn get_mut_vars(&mut self) -> &mut Vars {
        &mut self.vars
    }

    /// Retrieves the variable `name` as a boolean.  Fails if it is some other type or if it's not
    /// defined.
    pub fn get_var_as_bool(&self, name: &str) -> Result<bool> {
        match self.vars.get(&VarRef::new(name, VarType::Boolean))? {
            Value::Boolean(b) => Ok(*b),
            _ => panic!("Invalid type check in get()"),
        }
    }

    /// Retrieves the variable `name` as an integer.  Fails if it is some other type or if it's not
    /// defined.
    pub fn get_var_as_int(&self, name: &str) -> Result<i32> {
        match self.vars.get(&VarRef::new(name, VarType::Integer))? {
            Value::Integer(i) => Ok(*i),
            _ => panic!("Invalid type check in get()"),
        }
    }

    /// Retrieves the variable `name` as a string.  Fails if it is some other type or if it's not
    /// defined.
    pub fn get_var_as_string(&self, name: &str) -> Result<&str> {
        match self.vars.get(&VarRef::new(name, VarType::Text))? {
            Value::Text(s) => Ok(s),
            _ => panic!("Invalid type check in get()"),
        }
    }

    /// Assigns the value of `expr` to the variable `vref`.
    fn assign(&mut self, vref: &VarRef, expr: &Expr) -> Result<()> {
        let value = expr.eval(&self.vars)?;
        self.vars.set(&vref, value)?;
        Ok(())
    }

    /// Executes an `IF` statement.
    async fn do_if(&mut self, branches: &[(Expr, Vec<Statement>)]) -> Result<()> {
        for (expr, stmts) in branches {
            match expr.eval(&self.vars)? {
                Value::Boolean(true) => {
                    for s in stmts {
                        self.exec_one(s).await?;
                    }
                    break;
                }
                Value::Boolean(false) => (),
                _ => return new_syntax_error("IF/ELSEIF require a boolean condition"),
            };
        }
        Ok(())
    }

    /// Executes a `WHILE` loop.
    async fn do_while(&mut self, condition: &Expr, body: &[Statement]) -> Result<()> {
        loop {
            match condition.eval(&self.vars)? {
                Value::Boolean(true) => {
                    for s in body {
                        self.exec_one(s).await?;
                    }
                }
                Value::Boolean(false) => break,
                _ => return new_syntax_error("WHILE requires a boolean condition"),
            }
        }
        Ok(())
    }

    /// Executes a single statement.
    async fn exec_one<'a>(&'a mut self, stmt: &'a Statement) -> Result<()> {
        match stmt {
            Statement::Assignment(vref, expr) => self.assign(vref, expr)?,
            Statement::BuiltinCall(name, args) => {
                let cmd = match self.builtins.get(name.as_str()) {
                    Some(cmd) => cmd.clone(),
                    None => return new_syntax_error(format!("Unknown builtin {}", name)),
                };
                cmd.exec(&args, self).await?
            }
            Statement::If(branches) => {
                let f = self.do_if(branches).boxed_local();
                f.await?;
            }
            Statement::While(condition, body) => {
                let f = self.do_while(condition, body).boxed_local();
                f.await?;
            }
        }
        Ok(())
    }

    /// Executes a program extracted from the `input` readable.
    ///
    /// Note that this does not consume `self`.  As a result, it is possible to execute multiple
    /// different programs on the same machine, all sharing state.
    pub async fn exec(&mut self, input: &mut dyn io::Read) -> Result<()> {
        let mut parser = Parser::from(input);
        while let Some(stmt) = parser.parse()? {
            self.exec_one(&stmt).await?;
        }
        Ok(())
    }
}

/// The `CLEAR` command.
#[derive(Default)]
pub struct ClearCommand {}

#[async_trait(?Send)]
impl BuiltinCommand for ClearCommand {
    fn name(&self) -> &'static str {
        "CLEAR"
    }

    fn syntax(&self) -> &'static str {
        ""
    }

    fn description(&self) -> &'static str {
        "Clears all variables to restore initial state."
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Result<()> {
        if !args.is_empty() {
            return new_usage_error("CLEAR takes no arguments");
        }
        machine.clear();
        Ok(())
    }
}

#[cfg(test)]
pub(crate) mod testutils {
    use super::*;
    use std::cell::RefCell;

    /// Simplified version of `INPUT` to feed input values based on some golden `data`.
    ///
    /// Every time this command is invoked, it yields the next value from the `data` iterator and
    /// assigns it to the variable provided as its only argument.
    pub(crate) struct InCommand {
        data: Box<RefCell<dyn Iterator<Item = &'static &'static str>>>,
    }

    impl InCommand {
        /// Creates a new command with the golden `data`.
        pub(crate) fn from(data: Box<RefCell<dyn Iterator<Item = &'static &'static str>>>) -> Self {
            Self { data }
        }
    }

    #[async_trait(?Send)]
    impl BuiltinCommand for InCommand {
        fn name(&self) -> &'static str {
            "IN"
        }

        fn syntax(&self) -> &'static str {
            "variableref"
        }

        fn description(&self) -> &'static str {
            "See docstring for test code."
        }

        async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Result<()> {
            if args.len() != 1 {
                return new_usage_error("IN only takes one argument");
            }
            if args[0].1 != ArgSep::End {
                return new_usage_error("Invalid separator");
            }
            let vref = match &args[0].0 {
                Some(Expr::Symbol(vref)) => vref,
                _ => return new_usage_error("IN requires a variable reference"),
            };

            let mut data = self.data.borrow_mut();
            let raw_value = data.next().unwrap().to_owned();
            let value = Value::parse_as(vref.ref_type(), raw_value)?;
            machine.get_mut_vars().set(vref, value)?;
            Ok(())
        }
    }

    /// Simplified version of `PRINT` that captures all calls to it into `data`.
    ///
    /// This command only accepts arguments separated by the `;` short separator and concatenates
    /// them with a single space.
    pub(crate) struct OutCommand {
        data: Rc<RefCell<Vec<String>>>,
    }

    impl OutCommand {
        /// Creates a new command that captures all calls into `data`.
        pub(crate) fn from(data: Rc<RefCell<Vec<String>>>) -> Self {
            Self { data }
        }
    }

    #[async_trait(?Send)]
    impl BuiltinCommand for OutCommand {
        fn name(&self) -> &'static str {
            "OUT"
        }

        fn syntax(&self) -> &'static str {
            "[expr1 [; .. exprN]]"
        }

        fn description(&self) -> &'static str {
            "See docstring for test code."
        }

        async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Result<()> {
            let mut text = String::new();
            for arg in args.iter() {
                if let Some(expr) = arg.0.as_ref() {
                    text += &expr.eval(machine.get_vars())?.to_string();
                }
                match arg.1 {
                    ArgSep::End => break,
                    ArgSep::Short => text += " ",
                    ArgSep::Long => return new_usage_error("Cannot use the ',' separator"),
                }
            }
            self.data.borrow_mut().push(text);
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::testutils::*;
    use super::*;
    use futures_lite::future::block_on;
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn test_clear() {
        let mut machine = Machine::default();
        block_on(machine.exec(&mut b"a = TRUE: b = 1".as_ref())).expect("Execution failed");
        assert!(machine.get_var_as_bool("a").is_ok());
        assert!(machine.get_var_as_int("b").is_ok());
        machine.clear();
        assert!(machine.get_var_as_bool("a").is_err());
        assert!(machine.get_var_as_int("b").is_err());
    }

    #[test]
    fn test_get_var_as_bool() {
        let mut machine = Machine::default();
        block_on(machine.exec(&mut b"a = TRUE: b = 1".as_ref())).expect("Execution failed");
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
        block_on(machine.exec(&mut b"a = 1: b = \"foo\"".as_ref())).expect("Execution failed");
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
        block_on(machine.exec(&mut b"a = \"foo\": b = FALSE".as_ref())).expect("Execution failed");
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
    ) -> Result<()> {
        let in_cmd = InCommand::from(Box::from(RefCell::from(golden_in.iter())));
        let out_cmd = OutCommand::from(captured_out);
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(in_cmd))
            .add_builtin(Rc::from(out_cmd))
            .build();
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
        run(input, golden_in, captured_out.clone()).expect("Execution failed");
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
        do_simple_error_test("a =\n", "Missing expression in assignment");
        do_simple_error_test("a = b\n", "Undefined variable b");
        do_simple_error_test("a = 3\na = TRUE\n", "Incompatible types in a assignment");
        do_simple_error_test("a? = 3", "Incompatible types in a? assignment");
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
        do_error_test(code, &["5"], &[], "IF/ELSEIF require a boolean condition");
    }

    #[test]
    fn test_if_errors() {
        do_simple_error_test("IF TRUE THEN END IF", "Expecting newline after THEN");
        do_simple_error_test(
            "IF TRUE THEN\nELSE IF TRUE THEN\nEND IF",
            "Expecting newline after ELSE",
        );
        do_simple_error_test("IF TRUE\nEND IF\nOUT 3", "No THEN in IF statement");

        do_simple_error_test("IF 2\nEND IF", "No THEN in IF statement");
        do_simple_error_test("IF 2 THEN\nEND IF", "IF/ELSEIF require a boolean condition");
        do_simple_error_test(
            "IF FALSE THEN\nELSEIF 2 THEN\nEND IF",
            "IF/ELSEIF require a boolean condition",
        );
    }

    #[test]
    fn test_while_ok() {
        let code = r#"
            IN n
            WHILE n > 0
                OUT "n is"; n
                n = n - 1
            END WHILE
        "#;
        do_ok_test(code, &["0"], &[]);
        do_ok_test(code, &["3"], &["n is 3", "n is 2", "n is 1"]);

        do_ok_test("WHILE FALSE\nOUT 1\nEND WHILE", &[], &[]);
    }

    #[test]
    fn test_while_errors() {
        do_simple_error_test("WHILE\nEND WHILE", "No expression in WHILE statement");
        do_simple_error_test("WHILE\nEND IF", "WHILE without END WHILE");

        do_simple_error_test("WHILE 2\n", "WHILE without END WHILE");
        do_simple_error_test("WHILE 2\nEND WHILE", "WHILE requires a boolean condition");
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
    fn test_top_level_errors() {
        do_simple_error_test("FOO BAR", "Unknown builtin FOO");
        do_error_test("OUT \"a\"\nFOO BAR\nOUT \"b\"", &[], &["a"], "Unknown builtin FOO");

        do_simple_error_test("+ b", "Unexpected token Plus in statement");
        do_error_test(
            "OUT \"a\"\n+ b\nOUT \"b\"",
            &[],
            &["a"],
            "Unexpected token Plus in statement",
        );
    }

    #[test]
    fn test_exec_shares_state() {
        let mut machine = Machine::default();
        block_on(machine.exec(&mut b"a = 10".as_ref())).expect("Execution failed");
        block_on(machine.exec(&mut b"b = a".as_ref())).expect("Execution failed");
    }

    #[test]
    fn test_clear_ok() {
        let mut machine = MachineBuilder::default().add_builtin(Rc::from(ClearCommand {})).build();
        block_on(machine.exec(&mut b"a = 1".as_ref())).unwrap();
        assert!(machine.get_var_as_int("a").is_ok());
        block_on(machine.exec(&mut b"CLEAR".as_ref())).unwrap();
        assert!(machine.get_var_as_int("a").is_err());
    }

    #[test]
    fn test_clear_errors() {
        let mut machine = MachineBuilder::default().add_builtin(Rc::from(ClearCommand {})).build();
        assert_eq!(
            "CLEAR takes no arguments",
            format!("{}", block_on(machine.exec(&mut b"CLEAR 123".as_ref())).unwrap_err())
        );
    }
}
