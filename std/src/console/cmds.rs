// EndBASIC
// Copyright 2021 Julio Merino
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

//! Commands for console interaction.

use crate::console::readline::read_line;
use crate::console::{CharsXY, ClearType, Console};
use async_trait::async_trait;
use endbasic_core::ast::{ArgSep, Expr, Value, VarType};
use endbasic_core::exec::Machine;
use endbasic_core::syms::{
    CallError, CallableMetadata, CallableMetadataBuilder, Command, CommandResult,
};
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

/// Category description for all symbols provided by this module.
const CATEGORY: &str = "Console
The EndBASIC console is the text-based display you are seeing: both the interpreter and the \
effects of all commands happen within the same console.  There is no separate output window as \
other didactical interpreters provide.
The console is a matrix of variable size.  The upper left position is row 0 and column 0.  \
Each position in this matrix contains a character and a color attribute.  The color attribute \
indicates the foreground and background colors of that character.  There is a default attribute \
to match the default settings of your terminal, which might not be a color: for example, in a \
terminal emulator configured with a black tint (aka a transparent terminal), the default color \
respects the transparency whereas color 0 (black) does not.
If you are writing a script and do not want the script to interfere with other parts of the \
console, you should restrict the script to using only the INPUT and PRINT commands.
Be aware that the console currently reacts poorly to size changes.  Avoid resizing your terminal \
or web browser.  If you do resize them, however, restart the interpreter.
Graphics are currently not supported but they are within the realm of possibility for a later \
version.";

/// The `CLS` command.
pub struct ClsCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl ClsCommand {
    /// Creates a new `CLS` command that clears the `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("CLS", VarType::Void)
                .with_syntax("")
                .with_category(CATEGORY)
                .with_description("Clears the screen.")
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Command for ClsCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], _machine: &mut Machine) -> CommandResult {
        if !args.is_empty() {
            return Err(CallError::ArgumentError("CLS takes no arguments".to_owned()));
        }
        self.console.borrow_mut().clear(ClearType::All)?;
        Ok(())
    }
}

/// The `COLOR` command.
pub struct ColorCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl ColorCommand {
    /// Creates a new `COLOR` command that changes the color of the `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("COLOR", VarType::Void)
                .with_syntax("[fg%][, [bg%]]")
                .with_category(CATEGORY)
                .with_description(
                    "Sets the foreground and background colors.
Color numbers are given as ANSI numbers and can be between 0 and 255.  If a color number is not \
specified, then the color is reset to the console's default.  The console default does not \
necessarily match any other color specifiable in the 0 to 255 range, as it might be transparent.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Command for ColorCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        let (fg_expr, bg_expr): (&Option<Expr>, &Option<Expr>) = match args {
            [] => (&None, &None),
            [(fg, ArgSep::End)] => (fg, &None),
            [(fg, ArgSep::Long), (bg, ArgSep::End)] => (fg, bg),
            _ => {
                return Err(CallError::ArgumentError(
                    "COLOR takes at most two arguments separated by a comma".to_owned(),
                ))
            }
        };

        fn get_color(e: &Option<Expr>, machine: &mut Machine) -> Result<Option<u8>, CallError> {
            match e {
                Some(e) => match e.eval(machine.get_mut_symbols())? {
                    Value::Integer(i) if i >= 0 && i <= std::u8::MAX as i32 => Ok(Some(i as u8)),
                    Value::Integer(_) => {
                        Err(CallError::ArgumentError("Color out of range".to_owned()))
                    }
                    _ => Err(CallError::ArgumentError("Color must be an integer".to_owned())),
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
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl InputCommand {
    /// Creates a new `INPUT` command that uses `console` to gather user input.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("INPUT", VarType::Void)
                .with_syntax("[\"prompt\"] <;|,> variableref")
                .with_category(CATEGORY)
                .with_description(
                    "Obtains user input from the console.
The first expression to this function must be empty or evaluate to a string, and specifies \
the prompt to print.  If this first argument is followed by the short `;` separator, the \
prompt is extended with a question mark.
The second expression to this function must be a bare variable reference and indicates the \
variable to update with the obtained input.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Command for InputCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        if args.len() != 2 {
            return Err(CallError::ArgumentError("INPUT requires two arguments".to_owned()));
        }

        let mut prompt = match &args[0].0 {
            Some(e) => match e.eval(machine.get_mut_symbols())? {
                Value::Text(t) => t,
                _ => {
                    return Err(CallError::ArgumentError(
                        "INPUT prompt must be a string".to_owned(),
                    ))
                }
            },
            None => "".to_owned(),
        };
        if let ArgSep::Short = args[0].1 {
            prompt += "? ";
        }

        let vref = match &args[1].0 {
            Some(Expr::Symbol(vref)) => vref,
            _ => {
                return Err(CallError::ArgumentError(
                    "INPUT requires a variable reference".to_owned(),
                ))
            }
        };
        let vref = machine.get_symbols().qualify_varref(vref)?;

        let mut console = self.console.borrow_mut();
        let mut previous_answer = String::new();
        loop {
            match read_line(&mut *console, &prompt, &previous_answer, None).await {
                Ok(answer) => match Value::parse_as(vref.ref_type(), answer.trim_end()) {
                    Ok(value) => {
                        machine.get_mut_symbols().set_var(&vref, value)?;
                        return Ok(());
                    }
                    Err(e) => {
                        console.print(&format!("Retry input: {}", e))?;
                        previous_answer = answer;
                    }
                },
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
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl LocateCommand {
    /// Creates a new `LOCATE` command that moves the cursor of the `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("LOCATE", VarType::Void)
                .with_syntax("row%, column%")
                .with_category(CATEGORY)
                .with_description("Moves the cursor to the given position.")
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Command for LocateCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        if args.len() != 2 {
            return Err(CallError::ArgumentError("LOCATE takes two arguments".to_owned()));
        }
        let (row_arg, column_arg) = (&args[0], &args[1]);
        if row_arg.1 != ArgSep::Long {
            return Err(CallError::ArgumentError(
                "LOCATE expects arguments separated by a comma".to_owned(),
            ));
        }
        debug_assert!(column_arg.1 == ArgSep::End);

        let row = match &row_arg.0 {
            Some(arg) => match arg.eval(machine.get_mut_symbols())? {
                Value::Integer(i) => {
                    if i < 0 {
                        return Err(CallError::ArgumentError("Row cannot be negative".to_owned()));
                    }
                    i as usize
                }
                _ => return Err(CallError::ArgumentError("Row must be an integer".to_owned())),
            },
            None => return Err(CallError::ArgumentError("Row cannot be empty".to_owned())),
        };

        let column = match &column_arg.0 {
            Some(arg) => match arg.eval(machine.get_mut_symbols())? {
                Value::Integer(i) => {
                    if i < 0 {
                        return Err(CallError::ArgumentError(
                            "Column cannot be negative".to_owned(),
                        ));
                    }
                    i as usize
                }
                _ => return Err(CallError::ArgumentError("Column must be an integer".to_owned())),
            },
            None => return Err(CallError::ArgumentError("Column cannot be empty".to_owned())),
        };

        self.console.borrow_mut().locate(CharsXY::new(column, row))?;
        Ok(())
    }
}

/// The `PRINT` command.
pub struct PrintCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl PrintCommand {
    /// Creates a new `PRINT` command that writes to `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("PRINT", VarType::Void)
                .with_syntax("[expr1 [<;|,> .. exprN]]")
                .with_category(CATEGORY)
                .with_description(
                    "Prints a message to the console.
The expressions given as arguments are all evaluated and converted to strings.  Arguments \
separated by the short `;` separator are concatenated with a single space, while arguments \
separated by the long `,` separator are concatenated with a tab character.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Command for PrintCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        let mut text = String::new();
        for arg in args.iter() {
            if let Some(expr) = arg.0.as_ref() {
                text += &expr.eval(machine.get_mut_symbols())?.to_string();
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
pub fn add_all(machine: &mut Machine, console: Rc<RefCell<dyn Console>>) {
    machine.add_command(ClsCommand::new(console.clone()));
    machine.add_command(ColorCommand::new(console.clone()));
    machine.add_command(InputCommand::new(console.clone()));
    machine.add_command(LocateCommand::new(console.clone()));
    machine.add_command(PrintCommand::new(console));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;

    #[test]
    fn test_cls_ok() {
        Tester::default().run("CLS").expect_output([CapturedOut::Clear(ClearType::All)]).check();
    }

    #[test]
    fn test_cls_errors() {
        check_stmt_err("CLS takes no arguments", "CLS 1");
    }

    #[test]
    fn test_color_ok() {
        fn t() -> Tester {
            Tester::default()
        }
        t().run("COLOR").expect_output([CapturedOut::Color(None, None)]).check();
        t().run("COLOR ,").expect_output([CapturedOut::Color(None, None)]).check();
        t().run("COLOR 1").expect_output([CapturedOut::Color(Some(1), None)]).check();
        t().run("COLOR 1,").expect_output([CapturedOut::Color(Some(1), None)]).check();
        t().run("COLOR , 1").expect_output([CapturedOut::Color(None, Some(1))]).check();
        t().run("COLOR 10, 5").expect_output([CapturedOut::Color(Some(10), Some(5))]).check();
        t().run("COLOR 0, 0").expect_output([CapturedOut::Color(Some(0), Some(0))]).check();
        t().run("COLOR 255, 255").expect_output([CapturedOut::Color(Some(255), Some(255))]).check();
    }

    #[test]
    fn test_color_errors() {
        check_stmt_err("COLOR takes at most two arguments separated by a comma", "COLOR 1, 2, 3");

        check_stmt_err("Color out of range", "COLOR 1000, 0");
        check_stmt_err("Color out of range", "COLOR 0, 1000");

        check_stmt_err("Color must be an integer", "COLOR TRUE, 0");
        check_stmt_err("Color must be an integer", "COLOR 0, TRUE");
    }

    #[test]
    fn test_input_ok() {
        fn t<V: Into<Value>>(stmt: &str, input: &str, output: &str, var: &str, value: V) {
            Tester::default()
                .add_input_chars(input)
                .run(stmt)
                .expect_prints([output])
                .expect_var(var, value)
                .check();
        }

        t("INPUT ; foo\nPRINT foo", "9\n", "9", "foo", 9);
        t("INPUT ; foo\nPRINT foo", "-9\n", "-9", "foo", -9);
        t("INPUT , bar?\nPRINT bar", "true\n", "TRUE", "bar", true);
        t("INPUT ; foo$\nPRINT foo", "\n", "", "foo", "");
        t(
            "INPUT \"With question mark\"; a$\nPRINT a$",
            "some long text\n",
            "some long text",
            "a",
            "some long text",
        );

        Tester::default()
            .add_input_chars("42\n")
            .run("prompt$ = \"Indirectly without question mark\"\nINPUT prompt$, b\nPRINT b * 2")
            .expect_prints(["84"])
            .expect_var("prompt", "Indirectly without question mark")
            .expect_var("b", 42)
            .check();
    }

    #[test]
    fn test_input_on_predefined_vars() {
        Tester::default()
            .add_input_chars("1.5\n")
            .run("d = 3.0\nINPUT ; d")
            .expect_var("d", 1.5)
            .check();

        Tester::default()
            .add_input_chars("foo bar\n")
            .run("DIM s AS STRING\nINPUT ; s")
            .expect_var("s", "foo bar")
            .check();

        Tester::default()
            .add_input_chars("5\ntrue\n")
            .run("DIM b AS BOOLEAN\nINPUT ; b")
            .expect_prints(["Retry input: Invalid boolean literal 5"])
            .expect_var("b", true)
            .check();
    }

    #[test]
    fn test_input_retry() {
        Tester::default()
            .add_input_chars("\ntrue\n")
            .run("INPUT ; b?")
            .expect_prints(["Retry input: Invalid boolean literal "])
            .expect_var("b", true)
            .check();

        Tester::default()
            .add_input_chars("0\ntrue\n")
            .run("INPUT ; b?")
            .expect_prints(["Retry input: Invalid boolean literal 0"])
            .expect_var("b", true)
            .check();

        Tester::default()
            .add_input_chars("\n7\n")
            .run("a = 3\nINPUT ; a")
            .expect_prints(["Retry input: Invalid integer literal "])
            .expect_var("a", 7)
            .check();

        Tester::default()
            .add_input_chars("x\n7\n")
            .run("a = 3\nINPUT ; a")
            .expect_prints(["Retry input: Invalid integer literal x"])
            .expect_var("a", 7)
            .check();
    }

    #[test]
    fn test_input_errors() {
        check_stmt_err("INPUT requires two arguments", "INPUT");
        check_stmt_err("INPUT requires two arguments", "INPUT ; ,");
        check_stmt_err("INPUT requires a variable reference", "INPUT ;");
        check_stmt_err("INPUT prompt must be a string", "INPUT 3 ; a");
        check_stmt_err("INPUT requires a variable reference", "INPUT ; a + 1");
        check_stmt_err("Cannot add Text(\"a\") and Boolean(true)", "INPUT \"a\" + TRUE; b?");
    }

    #[test]
    fn test_locate_ok() {
        Tester::default()
            .run("LOCATE 0, 0")
            .expect_output([CapturedOut::Locate(CharsXY::default())])
            .check();

        Tester::default()
            .run("LOCATE 1000, 2000")
            .expect_output([CapturedOut::Locate(CharsXY::new(2000, 1000))])
            .check();
    }

    #[test]
    fn test_locate_errors() {
        check_stmt_err("LOCATE takes two arguments", "LOCATE");
        check_stmt_err("LOCATE takes two arguments", "LOCATE 1");
        check_stmt_err("LOCATE takes two arguments", "LOCATE 1, 2, 3");
        check_stmt_err("LOCATE expects arguments separated by a comma", "LOCATE 1; 2");

        check_stmt_err("Row cannot be negative", "LOCATE -1, 2");
        check_stmt_err("Row must be an integer", "LOCATE TRUE, 2");
        check_stmt_err("Row cannot be empty", "LOCATE , 2");

        check_stmt_err("Column cannot be negative", "LOCATE 1, -2");
        check_stmt_err("Column must be an integer", "LOCATE 1, TRUE");
        check_stmt_err("Column cannot be empty", "LOCATE 1,");
    }

    #[test]
    fn test_print_ok() {
        Tester::default().run("PRINT").expect_prints([""]).check();
        Tester::default().run("PRINT ;").expect_prints([" "]).check();
        Tester::default().run("PRINT ,").expect_prints(["\t"]).check();
        Tester::default().run("PRINT ;,;,").expect_prints([" \t \t"]).check();

        Tester::default().run("PRINT 3").expect_prints(["3"]).check();
        Tester::default().run("PRINT 3 = 5").expect_prints(["FALSE"]).check();
        Tester::default()
            .run("PRINT true;123;\"foo bar\"")
            .expect_prints(["TRUE 123 foo bar"])
            .check();
        Tester::default().run("PRINT 6,1;3,5").expect_prints(["6\t1 3\t5"]).check();

        Tester::default()
            .run(r#"word = "foo": PRINT word, word: PRINT word + "s""#)
            .expect_prints(["foo\tfoo", "foos"])
            .expect_var("word", "foo")
            .check();
    }

    #[test]
    fn test_print_errors() {
        // Ensure type errors from `Expr` and `Value` bubble up.
        check_stmt_err("Unexpected value in expression", "PRINT a b");
        check_stmt_err("Cannot add Integer(3) and Boolean(true)", "PRINT 3 + TRUE");
    }
}
