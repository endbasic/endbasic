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
use crate::parser::Parser;
use failure::Fallible;
use std::collections::HashMap;
use std::io;
use std::mem;
use std::rc::Rc;

/// A trait to define a command that is executed by a `Machine`.
///
/// The commands themselves are immutable but they can reference mutable state.  Given that
/// EndBASIC is not threaded, it is sufficient for those references to be behind a `RefCell`
/// and/or an `Rc`.
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
    fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()>;
}

/// Storage for all variables that exist at runtime.
#[derive(Default)]
pub struct Vars {
    /// Map of variable names (without type annotations) to their values.
    vars: HashMap<String, Value>,
}

impl Vars {
    /// Clears all variables.
    pub fn clear(&mut self) {
        self.vars.clear()
    }

    /// Obtains the value of a variable.
    ///
    /// Returns an error if the variable is not defined, or if the type annotation in the variable
    /// reference does not match the type of the value that the variable contains.
    pub fn get(&self, vref: &VarRef) -> Fallible<&Value> {
        let value = match self.vars.get(&vref.name().to_ascii_uppercase()) {
            Some(v) => v,
            None => bail!("Undefined variable {}", vref.name()),
        };
        ensure!(
            vref.accepts(&value),
            "Incompatible types in {} reference",
            vref
        );
        Ok(value)
    }

    /// Returns true if this contains no variables.
    pub fn is_empty(&self) -> bool {
        self.vars.is_empty()
    }

    /// Sets the value of a variable.
    ///
    /// If `vref` contains a type annotation, the type of the value must be compatible with that
    /// type annotation.
    ///
    /// If the variable is already defined, then the type of the new value must be compatible with
    /// the existing variable.  In other words: a variable cannot change types while it's alive.
    pub fn set(&mut self, vref: &VarRef, value: Value) -> Fallible<()> {
        let name = vref.name().to_ascii_uppercase();
        ensure!(
            vref.accepts(&value),
            "Incompatible types in {} assignment",
            vref
        );
        if let Some(old_value) = self.vars.get_mut(&name) {
            ensure!(
                mem::discriminant(&value) == mem::discriminant(old_value),
                "Incompatible types in {} assignment",
                vref
            );
            *old_value = value;
        } else {
            self.vars.insert(name, value);
        }
        Ok(())
    }
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
        Machine {
            builtins: self.builtins,
            vars: Vars::default(),
        }
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
    pub fn get_var_as_bool(&self, name: &str) -> Fallible<bool> {
        match self.vars.get(&VarRef::new(name, VarType::Boolean))? {
            Value::Boolean(b) => Ok(*b),
            _ => panic!("Invalid type check in get()"),
        }
    }

    /// Retrieves the variable `name` as an integer.  Fails if it is some other type or if it's not
    /// defined.
    pub fn get_var_as_int(&self, name: &str) -> Fallible<i32> {
        match self.vars.get(&VarRef::new(name, VarType::Integer))? {
            Value::Integer(i) => Ok(*i),
            _ => panic!("Invalid type check in get()"),
        }
    }

    /// Retrieves the variable `name` as a string.  Fails if it is some other type or if it's not
    /// defined.
    pub fn get_var_as_string(&self, name: &str) -> Fallible<&str> {
        match self.vars.get(&VarRef::new(name, VarType::Text))? {
            Value::Text(s) => Ok(s),
            _ => panic!("Invalid type check in get()"),
        }
    }

    /// Assigns the value of `expr` to the variable `vref`.
    fn assign(&mut self, vref: &VarRef, expr: &Expr) -> Fallible<()> {
        let value = expr.eval(&self.vars)?;
        self.vars.set(&vref, value)
    }

    /// Executes an `IF` statement.
    fn do_if(&mut self, branches: &[(Expr, Vec<Statement>)]) -> Fallible<()> {
        for (expr, stmts) in branches {
            match expr.eval(&self.vars)? {
                Value::Boolean(true) => {
                    for s in stmts {
                        self.exec_one(s)?;
                    }
                    break;
                }
                Value::Boolean(false) => (),
                _ => bail!("IF/ELSEIF require a boolean condition"),
            };
        }
        Ok(())
    }

    /// Executes a `WHILE` loop.
    fn do_while(&mut self, condition: &Expr, body: &[Statement]) -> Fallible<()> {
        loop {
            match condition.eval(&self.vars)? {
                Value::Boolean(true) => {
                    for s in body {
                        self.exec_one(s)?;
                    }
                }
                Value::Boolean(false) => break,
                _ => bail!("WHILE requires a boolean condition"),
            }
        }
        Ok(())
    }

    /// Executes a single statement.
    fn exec_one(&mut self, stmt: &Statement) -> Fallible<()> {
        match stmt {
            Statement::Assignment(vref, expr) => self.assign(vref, expr)?,
            Statement::BuiltinCall(name, args) => {
                let cmd = match self.builtins.get(name.as_str()) {
                    Some(cmd) => cmd.clone(),
                    None => bail!("Unknown builtin {}", name),
                };
                cmd.exec(&args, self)?
            }
            Statement::If(branches) => self.do_if(branches)?,
            Statement::While(condition, body) => self.do_while(condition, body)?,
        }
        Ok(())
    }

    /// Executes a program extracted from the `input` readable.
    ///
    /// Note that this does not consume `self`.  As a result, it is possible to execute multiple
    /// different programs on the same machine, all sharing state.
    pub fn exec<'b>(&mut self, input: &'b mut dyn io::Read) -> Fallible<()> {
        let mut parser = Parser::from(input);
        while let Some(stmt) = parser.parse()? {
            self.exec_one(&stmt)?;
        }
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

        fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
            ensure!(args.len() == 1, "IN only takes one argument");
            ensure!(args[0].1 == ArgSep::End, "Invalid separator");
            let vref = match &args[0].0 {
                Some(Expr::Symbol(vref)) => vref,
                _ => bail!("IN requires a variable reference"),
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

        fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
            let mut text = String::new();
            for arg in args.iter() {
                if let Some(expr) = arg.0.as_ref() {
                    text += &expr.eval(machine.get_vars())?.to_string();
                }
                match arg.1 {
                    ArgSep::End => break,
                    ArgSep::Short => text += " ",
                    ArgSep::Long => bail!("Cannot use the ',' separator"),
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
    use crate::ast::VarType;
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn test_vars_clear() {
        let mut raw_vars = HashMap::new();
        raw_vars.insert("FOO".to_owned(), Value::Boolean(true));
        let mut vars = Vars { vars: raw_vars };
        assert!(!vars.is_empty());
        vars.clear();
        assert!(vars.is_empty());
    }

    #[test]
    fn test_vars_get_ok_with_explicit_type() {
        let mut raw_vars = HashMap::new();
        raw_vars.insert("A_BOOLEAN".to_owned(), Value::Boolean(true));
        raw_vars.insert("AN_INTEGER".to_owned(), Value::Integer(3));
        raw_vars.insert("A_STRING".to_owned(), Value::Text("some text".to_owned()));
        let vars = Vars { vars: raw_vars };

        assert_eq!(
            Value::Boolean(true),
            *vars
                .get(&VarRef::new("a_boolean", VarType::Boolean))
                .unwrap()
        );
        assert_eq!(
            Value::Integer(3),
            *vars
                .get(&VarRef::new("an_integer", VarType::Integer))
                .unwrap()
        );
        assert_eq!(
            Value::Text("some text".to_owned()),
            *vars.get(&VarRef::new("a_string", VarType::Text)).unwrap()
        );
    }

    #[test]
    fn test_vars_get_ok_with_auto_type() {
        let mut raw_vars = HashMap::new();
        raw_vars.insert("A_BOOLEAN".to_owned(), Value::Boolean(true));
        raw_vars.insert("AN_INTEGER".to_owned(), Value::Integer(3));
        raw_vars.insert("A_STRING".to_owned(), Value::Text("some text".to_owned()));
        let vars = Vars { vars: raw_vars };

        assert_eq!(
            Value::Boolean(true),
            *vars.get(&VarRef::new("a_boolean", VarType::Auto)).unwrap()
        );
        assert_eq!(
            Value::Integer(3),
            *vars.get(&VarRef::new("an_integer", VarType::Auto)).unwrap()
        );
        assert_eq!(
            Value::Text("some text".to_owned()),
            *vars.get(&VarRef::new("a_string", VarType::Auto)).unwrap()
        );
    }

    #[test]
    fn test_vars_get_undefined_error() {
        let mut raw_vars = HashMap::new();
        raw_vars.insert("a_string".to_owned(), Value::Text("some text".to_owned()));
        let vars = Vars { vars: raw_vars };

        assert_eq!(
            "Undefined variable a_str",
            format!(
                "{}",
                vars.get(&VarRef::new("a_str", VarType::Integer))
                    .unwrap_err()
            )
        );
    }

    #[test]
    fn test_vars_get_mismatched_type_error() {
        let mut raw_vars = HashMap::new();
        raw_vars.insert("A_BOOLEAN".to_owned(), Value::Boolean(true));
        raw_vars.insert("AN_INTEGER".to_owned(), Value::Integer(3));
        raw_vars.insert("A_STRING".to_owned(), Value::Text("some text".to_owned()));
        let vars = Vars { vars: raw_vars };

        assert_eq!(
            "Incompatible types in a_boolean$ reference",
            format!(
                "{}",
                vars.get(&VarRef::new("a_boolean", VarType::Text))
                    .unwrap_err()
            )
        );

        assert_eq!(
            "Incompatible types in an_integer? reference",
            format!(
                "{}",
                vars.get(&VarRef::new("an_integer", VarType::Boolean))
                    .unwrap_err()
            )
        );

        assert_eq!(
            "Incompatible types in a_string% reference",
            format!(
                "{}",
                vars.get(&VarRef::new("a_string", VarType::Integer))
                    .unwrap_err()
            )
        );
    }

    #[test]
    fn test_vars_set_ok_with_explicit_type() {
        let mut vars = Vars::default();

        vars.set(
            &VarRef::new("a_boolean", VarType::Boolean),
            Value::Boolean(true),
        )
        .unwrap();
        assert_eq!(
            Value::Boolean(true),
            *vars.get(&VarRef::new("a_boolean", VarType::Auto)).unwrap()
        );

        vars.set(
            &VarRef::new("an_integer", VarType::Integer),
            Value::Integer(0),
        )
        .unwrap();
        assert_eq!(
            Value::Integer(0),
            *vars.get(&VarRef::new("an_integer", VarType::Auto)).unwrap()
        );

        vars.set(
            &VarRef::new("a_string", VarType::Text),
            Value::Text("x".to_owned()),
        )
        .unwrap();
        assert_eq!(
            Value::Text("x".to_owned()),
            *vars.get(&VarRef::new("a_string", VarType::Auto)).unwrap()
        );
    }

    #[test]
    fn test_vars_set_ok_with_auto_type() {
        let mut vars = Vars::default();

        vars.set(
            &VarRef::new("a_boolean", VarType::Auto),
            Value::Boolean(true),
        )
        .unwrap();
        assert_eq!(
            Value::Boolean(true),
            *vars.get(&VarRef::new("a_boolean", VarType::Auto)).unwrap()
        );

        vars.set(&VarRef::new("an_integer", VarType::Auto), Value::Integer(0))
            .unwrap();
        assert_eq!(
            Value::Integer(0),
            *vars.get(&VarRef::new("an_integer", VarType::Auto)).unwrap()
        );

        vars.set(
            &VarRef::new("a_string", VarType::Auto),
            Value::Text("x".to_owned()),
        )
        .unwrap();
        assert_eq!(
            Value::Text("x".to_owned()),
            *vars.get(&VarRef::new("a_string", VarType::Auto)).unwrap()
        );
    }

    #[test]
    fn test_vars_set_mismatched_type_with_existing_value() {
        let bool_ref = VarRef::new("a_boolean", VarType::Auto);
        let bool_val = Value::Boolean(true);
        let int_ref = VarRef::new("an_integer", VarType::Auto);
        let int_val = Value::Integer(0);
        let text_ref = VarRef::new("a_string", VarType::Auto);
        let text_val = Value::Text("x".to_owned());

        let mut vars = Vars::default();
        vars.set(&bool_ref, bool_val.clone()).unwrap();
        vars.set(&int_ref, int_val.clone()).unwrap();
        vars.set(&text_ref, text_val).unwrap();

        assert_eq!(
            "Incompatible types in a_boolean assignment",
            format!("{}", vars.set(&bool_ref, int_val.clone()).unwrap_err())
        );
        assert_eq!(
            "Incompatible types in an_integer assignment",
            format!("{}", vars.set(&int_ref, bool_val).unwrap_err())
        );
        assert_eq!(
            "Incompatible types in a_string assignment",
            format!("{}", vars.set(&text_ref, int_val).unwrap_err())
        );
    }

    #[test]
    fn test_vars_set_mismatched_type_for_annotation() {
        let bool_ref = VarRef::new("a_boolean", VarType::Boolean);
        let bool_val = Value::Boolean(true);
        let int_ref = VarRef::new("an_integer", VarType::Integer);
        let int_val = Value::Integer(0);
        let text_ref = VarRef::new("a_string", VarType::Text);
        let text_val = Value::Text("x".to_owned());

        let mut vars = Vars::default();
        assert_eq!(
            "Incompatible types in a_boolean? assignment",
            format!("{}", vars.set(&bool_ref, int_val).unwrap_err())
        );
        assert_eq!(
            "Incompatible types in an_integer% assignment",
            format!("{}", vars.set(&int_ref, text_val).unwrap_err())
        );
        assert_eq!(
            "Incompatible types in a_string$ assignment",
            format!("{}", vars.set(&text_ref, bool_val).unwrap_err())
        );
    }

    #[test]
    fn test_vars_get_set_case_insensitivity() {
        let mut vars = Vars::default();
        vars.set(&VarRef::new("SomeName", VarType::Auto), Value::Integer(6))
            .unwrap();
        assert_eq!(
            Value::Integer(6),
            *vars.get(&VarRef::new("somename", VarType::Auto)).unwrap()
        );
    }

    #[test]
    fn test_vars_get_set_replace_value() {
        let mut vars = Vars::default();
        vars.set(&VarRef::new("the_var", VarType::Auto), Value::Integer(100))
            .unwrap();
        assert_eq!(
            Value::Integer(100),
            *vars.get(&VarRef::new("the_var", VarType::Auto)).unwrap()
        );
        vars.set(&VarRef::new("the_var", VarType::Auto), Value::Integer(200))
            .unwrap();
        assert_eq!(
            Value::Integer(200),
            *vars.get(&VarRef::new("the_var", VarType::Auto)).unwrap()
        );
    }

    #[test]
    fn test_clear() {
        let mut machine = Machine::default();
        let mut cursor = io::Cursor::new("a = TRUE: b = 1");
        machine.exec(&mut cursor).expect("Execution failed");
        assert!(machine.get_var_as_bool("a").is_ok());
        assert!(machine.get_var_as_int("b").is_ok());
        machine.clear();
        assert!(machine.get_var_as_bool("a").is_err());
        assert!(machine.get_var_as_int("b").is_err());
    }

    #[test]
    fn test_get_var_as_bool() {
        let mut machine = Machine::default();
        let mut cursor = io::Cursor::new("a = TRUE: b = 1");
        machine.exec(&mut cursor).expect("Execution failed");
        assert!(machine.get_var_as_bool("a").expect("Failed to query a"));
        assert_eq!(
            "Incompatible types in b? reference",
            format!(
                "{}",
                machine
                    .get_var_as_bool("b")
                    .expect_err("Querying b succeeded")
            )
        );
        assert_eq!(
            "Undefined variable c",
            format!(
                "{}",
                machine
                    .get_var_as_bool("c")
                    .expect_err("Querying c succeeded")
            )
        );
    }

    #[test]
    fn test_get_var_as_int() {
        let mut machine = Machine::default();
        let mut cursor = io::Cursor::new("a = 1: b = \"foo\"");
        machine.exec(&mut cursor).expect("Execution failed");
        assert_eq!(1, machine.get_var_as_int("a").expect("Failed to query a"));
        assert_eq!(
            "Incompatible types in b% reference",
            format!(
                "{}",
                machine
                    .get_var_as_int("b")
                    .expect_err("Querying b succeeded")
            )
        );
        assert_eq!(
            "Undefined variable c",
            format!(
                "{}",
                machine
                    .get_var_as_int("c")
                    .expect_err("Querying c succeeded")
            )
        );
    }

    #[test]
    fn test_get_var_as_string() {
        let mut machine = Machine::default();
        let mut cursor = io::Cursor::new("a = \"foo\": b = FALSE");
        machine.exec(&mut cursor).expect("Execution failed");
        assert_eq!(
            "foo",
            machine.get_var_as_string("a").expect("Failed to query a")
        );
        assert_eq!(
            "Incompatible types in b$ reference",
            format!(
                "{}",
                machine
                    .get_var_as_string("b")
                    .expect_err("Querying b succeeded")
            )
        );
        assert_eq!(
            "Undefined variable c",
            format!(
                "{}",
                machine
                    .get_var_as_string("c")
                    .expect_err("Querying c succeeded")
            )
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
    ) -> Fallible<()> {
        let mut cursor = io::Cursor::new(input.as_bytes());
        let in_cmd = InCommand::from(Box::from(RefCell::from(golden_in.iter())));
        let out_cmd = OutCommand::from(captured_out);
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(in_cmd))
            .add_builtin(Rc::from(out_cmd))
            .build();
        machine.exec(&mut cursor)?;
        Ok(())
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

        do_ok_test(
            "a = \"some text\"\nOUT a; a$",
            &[],
            &["some text some text"],
        );
        do_ok_test(
            "a$ = \"some text\"\nOUT a; a$",
            &[],
            &["some text some text"],
        );

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
        do_error_test(
            "OUT \"a\"\nFOO BAR\nOUT \"b\"",
            &[],
            &["a"],
            "Unknown builtin FOO",
        );

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

        let mut cursor = io::Cursor::new("a = 10");
        machine.exec(&mut cursor).expect("Execution failed");

        let mut cursor = io::Cursor::new("b = a");
        machine.exec(&mut cursor).expect("Execution failed");
    }
}
