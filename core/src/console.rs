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

//! Console representation and manipulation.

use crate::ast::{ArgSep, Expr, Value};
use crate::exec::{BuiltinCommand, Machine};
use async_trait::async_trait;
use failure::Fallible;
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

/// Hooks to implement the commands that manipulate the console.
#[async_trait(?Send)]
pub trait Console {
    /// Clears the console and moves the cursor to the top left.
    fn clear(&mut self) -> io::Result<()>;

    /// Sets the console's foreground and background colors to `fg` and `bg`.
    ///
    /// If any of the colors is `None`, the color is left unchanged.
    fn color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()>;

    /// Writes `prompt` to the console and returns a single line of text input by the user.
    ///
    /// The text provided by the user should not be validated in any way before return, as type
    /// validation and conversions happen within the `Machine`.
    ///
    /// If validation fails, this method is called again with `previous` set to the invalid answer
    /// that caused the problem.  This can be used by the UI to pre-populate the new input field
    /// with that data.
    async fn input(&mut self, prompt: &str, previous: &str) -> io::Result<String>;

    /// Moves the cursor to the given position, which must be within the screen.
    fn locate(&mut self, row: usize, column: usize) -> io::Result<()>;

    /// Writes `text` to the console.
    fn print(&mut self, text: &str) -> io::Result<()>;
}

/// The `CLS` command.
pub struct ClsCommand {
    console: Rc<RefCell<dyn Console>>,
}

#[async_trait(?Send)]
impl BuiltinCommand for ClsCommand {
    fn name(&self) -> &'static str {
        "CLS"
    }

    fn syntax(&self) -> &'static str {
        ""
    }

    fn description(&self) -> &'static str {
        "Clears the screen."
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], _machine: &mut Machine) -> Fallible<()> {
        ensure!(args.is_empty(), "CLS takes no arguments");
        self.console.borrow_mut().clear()?;
        Ok(())
    }
}

/// The `COLOR` command.
pub struct ColorCommand {
    console: Rc<RefCell<dyn Console>>,
}

#[async_trait(?Send)]
impl BuiltinCommand for ColorCommand {
    fn name(&self) -> &'static str {
        "COLOR"
    }

    fn syntax(&self) -> &'static str {
        "[fg%][, bg%]"
    }

    fn description(&self) -> &'static str {
        "Sets the foreground, the background, or both colors.
Color numbers are given as ANSI numbers and can be between 0 and 255.  If a color number is not \
specified, then the color is left unchanged."
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
        let (fg_expr, bg_expr): (&Option<Expr>, &Option<Expr>) = match args {
            [(fg, ArgSep::End)] => (fg, &None),
            [(fg, ArgSep::Long), (bg, ArgSep::End)] => (fg, bg),
            _ => bail!("COLOR takes one or two arguments separated by a comma"),
        };

        fn get_color(e: &Option<Expr>, machine: &Machine) -> Fallible<Option<u8>> {
            match e {
                Some(e) => match e.eval(machine.get_vars())? {
                    Value::Integer(i) if i >= 0 && i <= std::u8::MAX as i32 => Ok(Some(i as u8)),
                    Value::Integer(_) => bail!("Color out of range"),
                    _ => bail!("Color must be an integer"),
                },
                None => Ok(None),
            }
        }

        let fg = get_color(fg_expr, machine)?;
        let bg = get_color(bg_expr, machine)?;

        self.console.borrow_mut().color(fg, bg)?;
        Ok(())
    }
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

#[async_trait(?Send)]
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

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
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
            match console.input(&prompt, &previous_answer).await {
                Ok(answer) => {
                    match Value::parse_as(vref.ref_type(), answer.trim_end()) {
                        Ok(value) => {
                            machine.get_mut_vars().set(vref, value)?;
                            return Ok(());
                        }
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

/// The `LOCATE` command.
pub struct LocateCommand {
    console: Rc<RefCell<dyn Console>>,
}

#[async_trait(?Send)]
impl BuiltinCommand for LocateCommand {
    fn name(&self) -> &'static str {
        "LOCATE"
    }

    fn syntax(&self) -> &'static str {
        "row%, column%"
    }

    fn description(&self) -> &'static str {
        "Moves the cursor to the given position."
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
        ensure!(args.len() == 2, "LOCATE takes two arguments");
        let (row_arg, column_arg) = (&args[0], &args[1]);
        ensure!(row_arg.1 == ArgSep::Long, "LOCATE expects arguments separated by a comma");
        debug_assert!(column_arg.1 == ArgSep::End);

        let row = match &row_arg.0 {
            Some(arg) => match arg.eval(machine.get_vars())? {
                Value::Integer(i) => {
                    ensure!(i >= 0, "Row cannot be negative");
                    i as usize
                }
                _ => bail!("Row must be an integer"),
            },
            None => bail!("Row cannot be empty"),
        };

        let column = match &column_arg.0 {
            Some(arg) => match arg.eval(machine.get_vars())? {
                Value::Integer(i) => {
                    ensure!(i >= 0, "Column cannot be negative");
                    i as usize
                }
                _ => bail!("Column must be an integer"),
            },
            None => bail!("Column cannot be empty"),
        };

        self.console.borrow_mut().locate(row, column)?;
        Ok(())
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

#[async_trait(?Send)]
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

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
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
        Rc::from(ClsCommand { console: console.clone() }),
        Rc::from(ColorCommand { console: console.clone() }),
        Rc::from(InputCommand::new(console.clone())),
        Rc::from(LocateCommand { console: console.clone() }),
        Rc::from(PrintCommand::new(console)),
    ]
}

#[cfg(test)]
pub(crate) mod testutils {
    use super::*;
    use std::io;

    /// A captured command or messages sent to the mock console.
    #[derive(Debug, Eq, PartialEq)]
    pub(crate) enum CapturedOut {
        Clear,
        Color(Option<u8>, Option<u8>),
        Locate(usize, usize),
        Print(String),
    }

    /// A console that supplies golden input and captures all output.
    pub(crate) struct MockConsole {
        /// Sequence of expected prompts and previous values and the responses to feed to them.
        golden_in: Box<dyn Iterator<Item = &'static (&'static str, &'static str, &'static str)>>,

        /// Sequence of all messages printed.
        captured_out: Vec<CapturedOut>,
    }

    impl MockConsole {
        /// Creates a new mock console with the given golden input.
        pub(crate) fn new(
            golden_in: &'static [(&'static str, &'static str, &'static str)],
        ) -> Self {
            Self { golden_in: Box::from(golden_in.iter()), captured_out: vec![] }
        }

        /// Obtains a reference to the captured output.
        pub(crate) fn captured_out(&self) -> &[CapturedOut] {
            self.captured_out.as_slice()
        }
    }

    #[async_trait(?Send)]
    impl Console for MockConsole {
        fn clear(&mut self) -> io::Result<()> {
            self.captured_out.push(CapturedOut::Clear);
            Ok(())
        }

        fn color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()> {
            self.captured_out.push(CapturedOut::Color(fg, bg));
            Ok(())
        }

        async fn input(&mut self, prompt: &str, previous: &str) -> io::Result<String> {
            let (expected_prompt, expected_previous, answer) = self.golden_in.next().unwrap();
            assert_eq!(expected_prompt, &prompt);
            assert_eq!(expected_previous, &previous);
            Ok((*answer).to_owned())
        }

        fn locate(&mut self, row: usize, column: usize) -> io::Result<()> {
            self.captured_out.push(CapturedOut::Locate(row, column));
            Ok(())
        }

        fn print(&mut self, text: &str) -> io::Result<()> {
            self.captured_out.push(CapturedOut::Print(text.to_owned()));
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::testutils::*;
    use super::*;
    use crate::exec::MachineBuilder;

    /// Runs the `input` code on a new machine and verifies its output.
    ///
    /// `golden_in` is a sequence of pairs each containing an expected prompt printed by `INPUT`
    /// and the reply to feed to that prompt.
    ///
    /// `expected_out` is a sequence of expected commands or messages.
    fn do_control_ok_test(
        input: &str,
        golden_in: &'static [(&'static str, &'static str, &'static str)],
        expected_out: &[CapturedOut],
    ) {
        let console = Rc::from(RefCell::from(MockConsole::new(golden_in)));
        let mut machine =
            MachineBuilder::default().add_builtins(all_commands(console.clone())).build();
        machine.exec(&mut input.as_bytes()).expect("Execution failed");
        assert_eq!(expected_out, console.borrow().captured_out());
    }

    /// Same as `do_control_ok_test` but with `expected_out` being just a sequence of expected
    /// `PRINT` calls.
    fn do_ok_test(
        input: &str,
        golden_in: &'static [(&'static str, &'static str, &'static str)],
        expected_out: &'static [&'static str],
    ) {
        let expected_out: Vec<CapturedOut> =
            expected_out.iter().map(|x| CapturedOut::Print((*x).to_owned())).collect();
        do_control_ok_test(input, golden_in, &expected_out)
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
        let console = Rc::from(RefCell::from(MockConsole::new(golden_in)));
        let mut machine =
            MachineBuilder::default().add_builtins(all_commands(console.clone())).build();
        assert_eq!(
            expected_err,
            format!("{}", machine.exec(&mut input.as_bytes()).expect_err("Execution did not fail"))
        );
        let expected_out: Vec<CapturedOut> =
            expected_out.iter().map(|x| CapturedOut::Print((*x).to_owned())).collect();
        assert_eq!(expected_out, console.borrow().captured_out());
    }

    /// Runs the `input` code on a new machine and verifies that it fails with `expected_err`.
    ///
    /// This is a syntactic wrapper over `do_error_test` to simplify those tests that are not
    /// expected to request any input nor generate any output.
    fn do_simple_error_test(input: &str, expected_err: &str) {
        do_error_test(input, &[], &[], expected_err);
    }

    #[test]
    fn test_cls_ok() {
        do_control_ok_test("CLS", &[], &[CapturedOut::Clear]);
    }

    #[test]
    fn test_cls_errors() {
        do_simple_error_test("CLS 1", "CLS takes no arguments");
    }

    #[test]
    fn test_color_ok() {
        do_control_ok_test("COLOR ,", &[], &[CapturedOut::Color(None, None)]);
        do_control_ok_test("COLOR 1", &[], &[CapturedOut::Color(Some(1), None)]);
        do_control_ok_test("COLOR 1,", &[], &[CapturedOut::Color(Some(1), None)]);
        do_control_ok_test("COLOR , 1", &[], &[CapturedOut::Color(None, Some(1))]);
        do_control_ok_test("COLOR 10, 5", &[], &[CapturedOut::Color(Some(10), Some(5))]);
        do_control_ok_test("COLOR 0, 0", &[], &[CapturedOut::Color(Some(0), Some(0))]);
        do_control_ok_test("COLOR 255, 255", &[], &[CapturedOut::Color(Some(255), Some(255))]);
    }

    #[test]
    fn test_color_errors() {
        do_simple_error_test("COLOR", "COLOR takes one or two arguments separated by a comma");
        do_simple_error_test(
            "COLOR 1, 2, 3",
            "COLOR takes one or two arguments separated by a comma",
        );

        do_simple_error_test("COLOR 1000, 0", "Color out of range");
        do_simple_error_test("COLOR 0, 1000", "Color out of range");

        do_simple_error_test("COLOR TRUE, 0", "Color must be an integer");
        do_simple_error_test("COLOR 0, TRUE", "Color must be an integer");
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
        do_simple_error_test("INPUT \"a\" + TRUE; b?", "Cannot add Text(\"a\") and Boolean(true)");
    }

    #[test]
    fn test_locate_ok() {
        do_control_ok_test("LOCATE 0, 0", &[], &[CapturedOut::Locate(0, 0)]);
        do_control_ok_test("LOCATE 1000, 2000", &[], &[CapturedOut::Locate(1000, 2000)]);
    }

    #[test]
    fn test_locate_errors() {
        do_simple_error_test("LOCATE", "LOCATE takes two arguments");
        do_simple_error_test("LOCATE 1", "LOCATE takes two arguments");
        do_simple_error_test("LOCATE 1, 2, 3", "LOCATE takes two arguments");
        do_simple_error_test("LOCATE 1; 2", "LOCATE expects arguments separated by a comma");

        do_simple_error_test("LOCATE -1, 2", "Row cannot be negative");
        do_simple_error_test("LOCATE TRUE, 2", "Row must be an integer");
        do_simple_error_test("LOCATE , 2", "Row cannot be empty");

        do_simple_error_test("LOCATE 1, -2", "Column cannot be negative");
        do_simple_error_test("LOCATE 1, TRUE", "Column must be an integer");
        do_simple_error_test("LOCATE 1,", "Column cannot be empty");
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
