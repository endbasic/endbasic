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

use crate::ast::{ArgSep, Expr, Statement, Value, VarRef};
use crate::parser::Parser;
use failure::Fallible;
use std::collections::HashMap;
use std::io;
use std::mem;

/// Hooks to implement the `INPUT` and `PRINT` builtins.
pub trait Console {
    /// Writes `prompt` to the console and returns a single line of text input by the user.
    ///
    /// The text provided by the user should not be validated in any way before return, as type
    /// validation and conversions happen within the `Machine`.
    fn input(&mut self, prompt: &str) -> Fallible<String>;

    /// Writes `text` to the console.
    fn print(&mut self, text: &str) -> Fallible<()>;
}

/// Storage for all variables that exist at runtime.
#[derive(Default)]
pub struct Vars {
    /// Map of variable names (without type annotations) to their values.
    vars: HashMap<String, Value>,
}

impl Vars {
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

/// Executes an EndBASIC program and tracks its state.
pub struct Machine<'a> {
    console: &'a mut dyn Console,
    vars: Vars,
}

impl<'a> Machine<'a> {
    /// Creates a new machine attached to the given `console`.
    #[allow(clippy::redundant_field_names)]
    pub fn new(console: &'a mut dyn Console) -> Self {
        Self {
            console: console,
            vars: Vars::default(),
        }
    }

    /// Assigns the value of `expr` to the variable `vref`.
    fn assign(&mut self, vref: &VarRef, expr: &Expr) -> Fallible<()> {
        let value = expr.eval(&self.vars)?;
        self.vars.set(&vref, value)
    }

    /// Obtains user input from the console.
    ///
    /// The first expression to this function must be empty or evaluate to a string, and specifies
    /// the prompt to print.  If this first argument is followed by the short `;` separator, the
    /// prompt is extended with a question mark.
    ///
    /// The second expression to this function must be a bare variable reference and indicates the
    /// variable to update with the obtained input.
    fn builtin_input(&mut self, args: &[(Option<Expr>, ArgSep)]) -> Fallible<()> {
        if args.len() != 2 {
            bail!("INPUT requires two arguments");
        }

        let mut prompt = match &args[0].0 {
            Some(e) => match e.eval(&self.vars)? {
                Value::Text(t) => t,
                _ => bail!("INPUT prompt must be a string"),
            },
            None => "".to_owned(),
        };
        if let ArgSep::Short = args[0].1 {
            prompt += "? ";
        }

        let vref = match &args[1].0 {
            Some(Expr::Symbol(vref)) => vref,
            _ => bail!("INPUT requires a variable reference"),
        };

        loop {
            let answer = self.console.input(&prompt)?;
            match Value::parse_as(vref.ref_type(), answer) {
                Ok(value) => return self.vars.set(vref, value),
                Err(e) => self.console.print(&format!("Retry input: {}", e))?,
            }
        }
    }

    /// Prints a message to the console.
    ///
    /// The expressions given as arguments are all evaluated and converted to strings.  Arguments
    /// separated by the short `;` separator are concatenated with a single space, while arguments
    /// separated by the long `,` separator are concatenated with a tab character.
    fn builtin_print(&mut self, args: &[(Option<Expr>, ArgSep)]) -> Fallible<()> {
        let mut text = String::new();
        for arg in args.iter() {
            if let Some(expr) = arg.0.as_ref() {
                text += &expr.eval(&self.vars)?.to_string();
            }
            match arg.1 {
                ArgSep::End => break,
                ArgSep::Short => text += " ",
                ArgSep::Long => text += "\t",
            }
        }
        self.console.print(&text)
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
            Statement::BuiltinCall(name, args) if name == "INPUT" => self.builtin_input(&args)?,
            Statement::BuiltinCall(name, args) if name == "PRINT" => self.builtin_print(&args)?,
            Statement::BuiltinCall(name, _) => bail!("Unknown builtin {}", name),
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
mod tests {
    use super::*;
    use crate::ast::VarType;

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

    /// A console that supplies golden input and captures all output.
    struct MockConsole {
        /// Sequence of expected prompts and the responses to feed to them.
        golden_in: Box<dyn Iterator<Item = &'static (&'static str, &'static str)>>,

        /// Sequence of all messages printed.
        captured_out: Vec<String>,
    }

    impl MockConsole {
        /// Creates a new mock console with the given golden input.
        fn new(golden_in: &'static [(&'static str, &'static str)]) -> Self {
            Self {
                golden_in: Box::from(golden_in.iter()),
                captured_out: vec![],
            }
        }
    }

    impl Console for MockConsole {
        fn input(&mut self, prompt: &str) -> Fallible<String> {
            let (expected_prompt, answer) = self.golden_in.next().unwrap();
            assert_eq!(expected_prompt, &prompt);
            Ok((*answer).to_owned())
        }

        fn print(&mut self, text: &str) -> Fallible<()> {
            self.captured_out.push(text.to_owned());
            Ok(())
        }
    }

    /// Runs the `input` code on a new machine and verifies its output.
    ///
    /// `golden_in` is a sequence of pairs each containing an expected prompt printed by `INPUT`
    /// and the reply to feed to that prompt.
    ///
    /// `expected_out` is a sequence of expected calls to `PRINT`.
    fn do_ok_test(
        input: &str,
        golden_in: &'static [(&'static str, &'static str)],
        expected_out: &'static [&'static str],
    ) {
        let mut cursor = io::Cursor::new(input.as_bytes());
        let mut console = MockConsole::new(golden_in);
        let mut machine = Machine::new(&mut console);
        machine.exec(&mut cursor).expect("Execution failed");
        assert_eq!(expected_out, console.captured_out.as_slice());
    }

    /// Runs the `input` code on a new machine and verifies that it fails with `expected_err`.
    ///
    /// Given that the code has side-effects until it fails, this follows the same process as
    /// `do_ok_test` regarding `golden_in` and `expected_out`.
    fn do_error_test(
        input: &str,
        golden_in: &'static [(&'static str, &'static str)],
        expected_out: &'static [&'static str],
        expected_err: &str,
    ) {
        let mut cursor = io::Cursor::new(input.as_bytes());
        let mut console = MockConsole::new(golden_in);
        let mut machine = Machine::new(&mut console);
        assert_eq!(
            expected_err,
            format!(
                "{}",
                machine
                    .exec(&mut cursor)
                    .expect_err("Execution did not fail")
            )
        );
        assert_eq!(expected_out, console.captured_out.as_slice());
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
        do_ok_test("a = TRUE\nPRINT a; a?", &[], &["TRUE TRUE"]);
        do_ok_test("a? = FALSE\nPRINT a; a?", &[], &["FALSE FALSE"]);

        do_ok_test("a = 3\nPRINT a; a%", &[], &["3 3"]);
        do_ok_test("a% = 3\nPRINT a; a%", &[], &["3 3"]);

        do_ok_test(
            "a = \"some text\"\nPRINT a; a$",
            &[],
            &["some text some text"],
        );
        do_ok_test(
            "a$ = \"some text\"\nPRINT a; a$",
            &[],
            &["some text some text"],
        );

        do_ok_test("a = 1\na = a + 1\nPRINT a", &[], &["2"]);
    }

    #[test]
    fn test_assignment_ok_case_insensitive() {
        do_ok_test("foo = 32\nPRINT FOO", &[], &["32"]);
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
            INPUT ; n
            IF n = 3 THEN
                PRINT "match"
            END IF
            IF n <> 3 THEN
                PRINT "no match"
            END IF
        "#;
        do_ok_test(code, &[("? ", "3")], &["match"]);
        do_ok_test(code, &[("? ", "5")], &["no match"]);

        let code = r#"
            INPUT , n
            IF n = 1 THEN
                PRINT "first"
            ELSEIF n = 2 THEN
                PRINT "second"
            ELSEIF n = 3 THEN
                PRINT "third"
            ELSE
                PRINT "fourth"
            END IF
        "#;
        do_ok_test(code, &[("", "1")], &["first"]);
        do_ok_test(code, &[("", "2")], &["second"]);
        do_ok_test(code, &[("", "3")], &["third"]);
        do_ok_test(code, &[("", "4")], &["fourth"]);
    }

    #[test]
    fn test_if_ok_on_malformed_branch() {
        let code = r#"
            INPUT ; n
            IF n = 3 THEN
                PRINT "match"
            ELSEIF "foo" THEN 'Invalid expression type but not evaluated.
                PRINT "no match"
            END IF
        "#;
        do_ok_test(code, &[("? ", "3")], &["match"]);
        do_error_test(
            code,
            &[("? ", "5")],
            &[],
            "IF/ELSEIF require a boolean condition",
        );
    }

    #[test]
    fn test_if_errors() {
        do_simple_error_test("IF TRUE THEN END IF", "Expecting newline after THEN");
        do_simple_error_test(
            "IF TRUE THEN\nELSE IF TRUE THEN\nEND IF",
            "Expecting newline after ELSE",
        );
        do_simple_error_test("IF TRUE\nEND IF\nPRINT 3", "No THEN in IF statement");

        do_simple_error_test("IF 2\nEND IF", "No THEN in IF statement");
        do_simple_error_test("IF 2 THEN\nEND IF", "IF/ELSEIF require a boolean condition");
        do_simple_error_test(
            "IF FALSE THEN\nELSEIF 2 THEN\nEND IF",
            "IF/ELSEIF require a boolean condition",
        );
    }

    #[test]
    fn test_input_ok() {
        do_ok_test("INPUT ; foo\nPRINT foo", &[("? ", "9")], &["9"]);
        do_ok_test("INPUT ; foo\nPRINT foo", &[("? ", "-9")], &["-9"]);
        do_ok_test("INPUT , bar?\nPRINT bar", &[("", "true")], &["TRUE"]);
        do_ok_test("INPUT ; foo$\nPRINT foo", &[("? ", "")], &[""]);
        do_ok_test(
            "INPUT \"With question mark\"; a$\nPRINT a$",
            &[("With question mark? ", "some long text")],
            &["some long text"],
        );
        do_ok_test(
            "prompt$ = \"Indirectly without question mark\"\nINPUT prompt$, b\nPRINT b * 2",
            &[("Indirectly without question mark", "42")],
            &["84"],
        );
    }

    #[test]
    fn test_input_retry() {
        do_ok_test(
            "INPUT ; b?",
            &[("? ", ""), ("? ", "true")],
            &["Retry input: Invalid boolean literal "],
        );
        do_ok_test(
            "INPUT ; b?",
            &[("? ", "0"), ("? ", "true")],
            &["Retry input: Invalid boolean literal 0"],
        );
        do_ok_test(
            "a = 3\nINPUT ; a",
            &[("? ", ""), ("? ", "7")],
            &["Retry input: Invalid integer literal "],
        );
        do_ok_test(
            "a = 3\nINPUT ; a",
            &[("? ", "x"), ("? ", "7")],
            &["Retry input: Invalid integer literal x"],
        );
    }

    #[test]
    fn test_input_errors() {
        do_simple_error_test("INPUT", "INPUT requires two arguments");
        do_simple_error_test("INPUT ; ,", "INPUT requires two arguments");
        do_simple_error_test("INPUT ;", "INPUT requires a variable reference");
        do_simple_error_test("INPUT 3 ; a", "INPUT prompt must be a string");
        do_simple_error_test("INPUT ; a + 1", "INPUT requires a variable reference");
        do_simple_error_test(
            "INPUT \"a\" + TRUE; b?",
            "Cannot add Text(\"a\") and Boolean(true)",
        );
    }

    #[test]
    fn test_print_ok() {
        do_ok_test("PRINT", &[], &[""]);
        do_ok_test("PRINT ;", &[], &[" "]);
        do_ok_test("PRINT ,", &[], &["\t"]);
        do_ok_test("PRINT ;,;,", &[], &[" \t \t"]);

        do_ok_test("PRINT 3", &[], &["3"]);
        do_ok_test("PRINT 3 = 5", &[], &["FALSE"]);
        do_ok_test("PRINT true;123;\"foo bar\"", &[], &["TRUE 123 foo bar"]);
        do_ok_test("PRINT 6,1;3,5", &[], &["6\t1 3\t5"]);

        do_ok_test(
            "word = \"foo\"\nPRINT word, word\nPRINT word + \"s\"",
            &[],
            &["foo\tfoo", "foos"],
        );
    }

    #[test]
    fn test_print_errors() {
        // Ensure type errors from `Expr` and `Value` bubble up.
        do_simple_error_test("PRINT a b", "Unexpected value in expression");
        do_simple_error_test("PRINT 3 + TRUE", "Cannot add Integer(3) and Boolean(true)");
    }

    #[test]
    fn test_while_ok() {
        let code = r#"
            INPUT ; n
            WHILE n > 0
                PRINT "n is"; n
                n = n - 1
            END WHILE
        "#;
        do_ok_test(code, &[("? ", "0")], &[]);
        do_ok_test(code, &[("? ", "3")], &["n is 3", "n is 2", "n is 1"]);

        do_ok_test("WHILE FALSE\nPRINT 1\nEND WHILE", &[], &[]);
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

            PRINT "Hello" 'Some remark here.

            IF TRUE THEN

                PRINT "Bye" 'And another remark here after a blank line.
            END IF
        "#;
        do_ok_test(code, &[], &["Hello", "Bye"]);
    }

    #[test]
    fn test_top_level_errors() {
        do_simple_error_test("FOO BAR", "Unknown builtin FOO");
        do_error_test(
            "PRINT \"a\"\nFOO BAR\nPRINT \"b\"",
            &[],
            &["a"],
            "Unknown builtin FOO",
        );

        do_simple_error_test("+ b", "Unexpected token Plus in statement");
        do_error_test(
            "PRINT \"a\"\n+ b\nPRINT \"b\"",
            &[],
            &["a"],
            "Unexpected token Plus in statement",
        );
    }

    #[test]
    fn test_exec_shares_state() {
        let mut console = MockConsole::new(&[]);
        let mut machine = Machine::new(&mut console);

        let mut cursor = io::Cursor::new("a = 10");
        machine.exec(&mut cursor).expect("Execution failed");

        let mut cursor = io::Cursor::new("PRINT a");
        machine.exec(&mut cursor).expect("Execution failed");
        assert_eq!(&["10"], console.captured_out.as_slice());
    }
}
