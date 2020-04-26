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

use crate::ast::{ArgSep, Expr, Value};
use crate::exec::{BuiltinCommand, Machine};
use failure::Fallible;
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

/// Hooks to implement the `INPUT` and `PRINT` builtins.
pub trait Console {
    /// Writes `prompt` to the console and returns a single line of text input by the user.
    ///
    /// The text provided by the user should not be validated in any way before return, as type
    /// validation and conversions happen within the `Machine`.
    ///
    /// If validation fails, this method is called again with `previous` set to the invalid answer
    /// that caused the problem.  This can be used by the UI to pre-populate the new input field
    /// with that data.
    fn input(&mut self, prompt: &str, previous: &str) -> io::Result<String>;

    /// Writes `text` to the console.
    fn print(&mut self, text: &str) -> io::Result<()>;
}

/// The `INPUT` command.
pub struct InputCommand {
    console: Rc<RefCell<dyn Console>>,
}

impl InputCommand {
    /// Creates a new `INPUT` command that uses `console` to gather user input.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Self {
        Self { console }
    }
}

impl BuiltinCommand for InputCommand {
    fn name(&self) -> &'static str {
        "INPUT"
    }

    fn syntax(&self) -> &'static str {
        "[\"prompt\"] <;|,> variableref"
    }

    fn description(&self) -> &'static str {
        "Obtains user input from the console.
The first expression to this function must be empty or evaluate to a string, and specifies \
the prompt to print.  If this first argument is followed by the short `;` separator, the \
prompt is extended with a question mark.
The second expression to this function must be a bare variable reference and indicates the \
variable to update with the obtained input."
    }

    fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
        if args.len() != 2 {
            bail!("INPUT requires two arguments");
        }

        let mut prompt = match &args[0].0 {
            Some(e) => match e.eval(machine.get_vars())? {
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

        let mut console = self.console.borrow_mut();
        let mut previous_answer = String::new();
        loop {
            match console.input(&prompt, &previous_answer) {
                Ok(answer) => {
                    match Value::parse_as(vref.ref_type(), answer.trim_end()) {
                        Ok(value) => return machine.get_mut_vars().set(vref, value),
                        Err(e) => console.print(&format!("Retry input: {}", e))?,
                    }
                    previous_answer = answer;
                }
                Err(e) if e.kind() == io::ErrorKind::InvalidData => {
                    console.print(&format!("Retry input: {}", e))?
                }
                Err(e) => return Err(e.into()),
            }
        }
    }
}

/// The `PRINT` command.
pub struct PrintCommand {
    console: Rc<RefCell<dyn Console>>,
}

impl PrintCommand {
    /// Creates a new `PRINT` command that writes to `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Self {
        Self { console }
    }
}

impl BuiltinCommand for PrintCommand {
    fn name(&self) -> &'static str {
        "PRINT"
    }

    fn syntax(&self) -> &'static str {
        "[expr1 [<;|,> .. exprN]]"
    }

    fn description(&self) -> &'static str {
        "Prints a message to the console.
The expressions given as arguments are all evaluated and converted to strings.  Arguments \
separated by the short `;` separator are concatenated with a single space, while arguments \
separated by the long `,` separator are concatenated with a tab character."
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
                ArgSep::Long => text += "\t",
            }
        }
        self.console.borrow_mut().print(&text)?;
        Ok(())
    }
}

/// Adds all console-related commands for the given `console` to the `machine`.
pub fn all_commands(console: Rc<RefCell<dyn Console>>) -> Vec<Rc<dyn BuiltinCommand>> {
    vec![
        Rc::from(InputCommand::new(console.clone())),
        Rc::from(PrintCommand::new(console)),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exec::MachineBuilder;
    use std::io;

    /// A console that supplies golden input and captures all output.
    struct MockConsole {
        /// Sequence of expected prompts and previous values and the responses to feed to them.
        golden_in: Box<dyn Iterator<Item = &'static (&'static str, &'static str, &'static str)>>,

        /// Sequence of all messages printed.
        captured_out: Vec<String>,
    }

    impl MockConsole {
        /// Creates a new mock console with the given golden input.
        fn new(golden_in: &'static [(&'static str, &'static str, &'static str)]) -> Self {
            Self {
                golden_in: Box::from(golden_in.iter()),
                captured_out: vec![],
            }
        }
    }

    impl Console for MockConsole {
        fn input(&mut self, prompt: &str, previous: &str) -> io::Result<String> {
            let (expected_prompt, expected_previous, answer) = self.golden_in.next().unwrap();
            assert_eq!(expected_prompt, &prompt);
            assert_eq!(expected_previous, &previous);
            Ok((*answer).to_owned())
        }

        fn print(&mut self, text: &str) -> io::Result<()> {
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
        golden_in: &'static [(&'static str, &'static str, &'static str)],
        expected_out: &'static [&'static str],
    ) {
        let mut cursor = io::Cursor::new(input.as_bytes());
        let console = Rc::from(RefCell::from(MockConsole::new(golden_in)));
        let mut machine = MachineBuilder::default()
            .add_builtins(all_commands(console.clone()))
            .build();
        machine.exec(&mut cursor).expect("Execution failed");
        assert_eq!(expected_out, console.borrow().captured_out.as_slice());
    }

    /// Runs the `input` code on a new machine and verifies that it fails with `expected_err`.
    ///
    /// Given that the code has side-effects until it fails, this follows the same process as
    /// `do_ok_test` regarding `golden_in` and `expected_out`.
    fn do_error_test(
        input: &str,
        golden_in: &'static [(&'static str, &'static str, &'static str)],
        expected_out: &'static [&'static str],
        expected_err: &str,
    ) {
        let mut cursor = io::Cursor::new(input.as_bytes());
        let console = Rc::from(RefCell::from(MockConsole::new(golden_in)));
        let mut machine = MachineBuilder::default()
            .add_builtins(all_commands(console.clone()))
            .build();
        assert_eq!(
            expected_err,
            format!(
                "{}",
                machine
                    .exec(&mut cursor)
                    .expect_err("Execution did not fail")
            )
        );
        assert_eq!(expected_out, console.borrow().captured_out.as_slice());
    }

    /// Runs the `input` code on a new machine and verifies that it fails with `expected_err`.
    ///
    /// This is a syntactic wrapper over `do_error_test` to simplify those tests that are not
    /// expected to request any input nor generate any output.
    fn do_simple_error_test(input: &str, expected_err: &str) {
        do_error_test(input, &[], &[], expected_err);
    }

    #[test]
    fn test_input_ok() {
        do_ok_test("INPUT ; foo\nPRINT foo", &[("? ", "", "9")], &["9"]);
        do_ok_test("INPUT ; foo\nPRINT foo", &[("? ", "", "-9")], &["-9"]);
        do_ok_test("INPUT , bar?\nPRINT bar", &[("", "", "true")], &["TRUE"]);
        do_ok_test("INPUT ; foo$\nPRINT foo", &[("? ", "", "")], &[""]);
        do_ok_test(
            "INPUT \"With question mark\"; a$\nPRINT a$",
            &[("With question mark? ", "", "some long text")],
            &["some long text"],
        );
        do_ok_test(
            "prompt$ = \"Indirectly without question mark\"\nINPUT prompt$, b\nPRINT b * 2",
            &[("Indirectly without question mark", "", "42")],
            &["84"],
        );
    }

    #[test]
    fn test_input_retry() {
        do_ok_test(
            "INPUT ; b?",
            &[("? ", "", ""), ("? ", "", "true")],
            &["Retry input: Invalid boolean literal "],
        );
        do_ok_test(
            "INPUT ; b?",
            &[("? ", "", "0"), ("? ", "0", "true")],
            &["Retry input: Invalid boolean literal 0"],
        );
        do_ok_test(
            "a = 3\nINPUT ; a",
            &[("? ", "", ""), ("? ", "", "7")],
            &["Retry input: Invalid integer literal "],
        );
        do_ok_test(
            "a = 3\nINPUT ; a",
            &[("? ", "", "x"), ("? ", "x", "7")],
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
}
