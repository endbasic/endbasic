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
use crate::console::{CharsXY, ClearType, Console, ConsoleClearable, Key};
use async_trait::async_trait;
use endbasic_core::ast::{
    ArgSep, ArgSpan, BuiltinCallSpan, Expr, FunctionCallSpan, Value, VarType,
};
use endbasic_core::eval;
use endbasic_core::exec::Machine;
use endbasic_core::syms::{
    CallError, CallableMetadata, CallableMetadataBuilder, Command, CommandResult, Function,
    FunctionResult, Symbols,
};
use std::cell::RefCell;
use std::convert::TryFrom;
use std::io;
use std::rc::Rc;

/// Category description for all symbols provided by this module.
const CATEGORY: &str = "Console
The EndBASIC console is the display you are seeing: both the interpreter and the \
effects of all commands happen within the same console.  There is no separate output window as \
other didactical interpreters provide.  This unified console supports text and, depending on the \
output backend, graphics.  This help section focuses on the textual console; for information about \
graphics, run HELP GRAPHICS.
The text console is a matrix of variable size.  The upper left position is row 0 and column 0.  \
Each position in this matrix contains a character and a color attribute.  The color attribute \
indicates the foreground and background colors of that character.  There is a default attribute \
to match the default settings of your terminal, which might not be a color: for example, in a \
terminal emulator configured with a black tint (aka a transparent terminal), the default color \
respects the transparency whereas color 0 (black) does not.
If you are writing a script and do not want the script to interfere with other parts of the \
console, you should restrict the script to using only the INPUT and PRINT commands.
Be aware that the console currently reacts poorly to size changes.  Avoid resizing your terminal \
or web browser.  If you do resize them, however, restart the interpreter.";

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

    async fn exec(&self, span: &BuiltinCallSpan, _machine: &mut Machine) -> CommandResult {
        if !span.args.is_empty() {
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

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        let (fg_expr, bg_expr): (&Option<Expr>, &Option<Expr>) = match span.args.as_slice() {
            [] => (&None, &None),
            [ArgSpan { expr: fg, sep: ArgSep::End, .. }] => (fg, &None),
            [ArgSpan { expr: fg, sep: ArgSep::Long, .. }, ArgSpan { expr: bg, sep: ArgSep::End, .. }] => {
                (fg, bg)
            }
            _ => {
                return Err(CallError::ArgumentError(
                    "COLOR takes at most two arguments separated by a comma".to_owned(),
                ))
            }
        };

        async fn get_color(
            e: &Option<Expr>,
            machine: &mut Machine,
        ) -> Result<Option<u8>, CallError> {
            match e {
                Some(e) => match e.eval(machine.get_mut_symbols()).await? {
                    Value::Integer(i) if i >= 0 && i <= std::u8::MAX as i32 => Ok(Some(i as u8)),
                    Value::Integer(_) => {
                        Err(CallError::ArgumentError("Color out of range".to_owned()))
                    }
                    _ => Err(CallError::ArgumentError("Color must be an integer".to_owned())),
                },
                None => Ok(None),
            }
        }

        let fg = get_color(fg_expr, machine).await?;
        let bg = get_color(bg_expr, machine).await?;

        self.console.borrow_mut().color(fg, bg)?;
        Ok(())
    }
}

/// The `INKEY` function.
pub struct InKeyFunction {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl InKeyFunction {
    /// Creates a new `INKEY` function that waits for a key press.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("INKEY", VarType::Text)
                .with_syntax("")
                .with_category(CATEGORY)
                .with_description(
                    "Checks for an available key press and returns it.
If a key press is available to be read, returns its name.  Otherwise, returns the empty string.  \
The returned key matches its name, number, or symbol and maintains case.  In other words, \
pressing the X key will return 'x' or 'X' depending on the SHIFT modifier.
The following special keys are recognized: arrow keys (UP, DOWN, LEFT, RIGHT), backspace (BS), \
end or CTRL+E (END), enter (ENTER), CTRL+D (EOF), escape (ESC), home or CTRL+A (HOME), \
CTRL+C (INT), page up (PGUP), page down (PGDOWN), and tab (TAB).
This function never blocks.  To wait for a key press, you need to explicitly poll the keyboard.  \
For example, to wait until the escape key is pressed, you could do:
k$ = \"\": WHILE k$ <> \"ESC\": k = INKEY$(): SLEEP 0.01: WEND
This non-blocking design lets you to combine the reception of multiple evens, such as from \
GPIO_INPUT?, within the same loop.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Function for InKeyFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, _symbols: &mut Symbols) -> FunctionResult {
        if !span.args.is_empty() {
            return Err(CallError::ArgumentError("no arguments allowed".to_owned()));
        }

        let key = self.console.borrow_mut().poll_key().await?;
        Ok(match key {
            Some(Key::ArrowDown) => Value::Text("DOWN".to_owned()),
            Some(Key::ArrowLeft) => Value::Text("LEFT".to_owned()),
            Some(Key::ArrowRight) => Value::Text("RIGHT".to_owned()),
            Some(Key::ArrowUp) => Value::Text("UP".to_owned()),

            Some(Key::Backspace) => Value::Text("BS".to_owned()),
            Some(Key::CarriageReturn) => Value::Text("ENTER".to_owned()),
            Some(Key::Char(x)) => Value::Text(format!("{}", x)),
            Some(Key::End) => Value::Text("END".to_owned()),
            Some(Key::Eof) => Value::Text("EOF".to_owned()),
            Some(Key::Escape) => Value::Text("ESC".to_owned()),
            Some(Key::Home) => Value::Text("HOME".to_owned()),
            Some(Key::Interrupt) => Value::Text("INT".to_owned()),
            Some(Key::NewLine) => Value::Text("ENTER".to_owned()),
            Some(Key::PageDown) => Value::Text("PGDOWN".to_owned()),
            Some(Key::PageUp) => Value::Text("PGUP".to_owned()),
            Some(Key::Tab) => Value::Text("TAB".to_owned()),
            Some(Key::Unknown(_)) => Value::Text("".to_owned()),

            None => Value::Text("".to_owned()),
        })
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

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        if span.args.len() != 2 {
            return Err(CallError::ArgumentError("INPUT requires two arguments".to_owned()));
        }

        let mut prompt = match &span.args[0].expr {
            Some(e) => match e.eval(machine.get_mut_symbols()).await? {
                Value::Text(t) => t,
                _ => {
                    return Err(CallError::ArgumentError(
                        "INPUT prompt must be a string".to_owned(),
                    ))
                }
            },
            None => "".to_owned(),
        };
        if let ArgSep::Short = span.args[0].sep {
            prompt += "? ";
        }

        let (vref, pos) = match &span.args[1].expr {
            Some(Expr::Symbol(span)) => (&span.vref, span.pos),
            _ => {
                return Err(CallError::ArgumentError(
                    "INPUT requires a variable reference".to_owned(),
                ))
            }
        };
        let vref = machine
            .get_symbols()
            .qualify_varref(vref)
            .map_err(|e| eval::Error::from_value_error(e, pos))?;

        let mut console = self.console.borrow_mut();
        let mut previous_answer = String::new();
        loop {
            match read_line(&mut *console, &prompt, &previous_answer, None).await {
                Ok(answer) => match Value::parse_as(vref.ref_type(), answer.trim_end()) {
                    Ok(value) => {
                        machine
                            .get_mut_symbols()
                            .set_var(&vref, value)
                            .map_err(|e| eval::Error::from_value_error(e, pos))?;
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
                .with_syntax("column%, row%")
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

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        if span.args.len() != 2 {
            return Err(CallError::ArgumentError("LOCATE takes two arguments".to_owned()));
        }
        let (column_arg, row_arg) = (&span.args[0], &span.args[1]);
        if column_arg.sep != ArgSep::Long {
            return Err(CallError::ArgumentError(
                "LOCATE expects arguments separated by a comma".to_owned(),
            ));
        }
        debug_assert!(row_arg.sep == ArgSep::End);

        let column = match &column_arg.expr {
            Some(arg) => match arg.eval(machine.get_mut_symbols()).await? {
                Value::Integer(i) => match u16::try_from(i) {
                    Ok(v) => v,
                    Err(_) => {
                        return Err(CallError::ArgumentError("Column out of range".to_owned()))
                    }
                },
                _ => return Err(CallError::ArgumentError("Column must be an integer".to_owned())),
            },
            None => return Err(CallError::ArgumentError("Column cannot be empty".to_owned())),
        };

        let row = match &row_arg.expr {
            Some(arg) => match arg.eval(machine.get_mut_symbols()).await? {
                Value::Integer(i) => match u16::try_from(i) {
                    Ok(v) => v,
                    Err(_) => return Err(CallError::ArgumentError("Row out of range".to_owned())),
                },
                _ => return Err(CallError::ArgumentError("Row must be an integer".to_owned())),
            },
            None => return Err(CallError::ArgumentError("Row cannot be empty".to_owned())),
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

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        let mut text = String::new();
        for arg in span.args.iter() {
            if let Some(expr) = arg.expr.as_ref() {
                text += &expr.eval(machine.get_mut_symbols()).await?.to_output();
            }
            match arg.sep {
                ArgSep::End => break,
                ArgSep::Short => text += " ",
                ArgSep::Long => {
                    text += " ";
                    while text.len() % 8 != 0 {
                        text += " ";
                    }
                }
            }
        }
        self.console.borrow_mut().print(&text)?;
        Ok(())
    }
}

/// Adds all console-related commands for the given `console` to the `machine`.
pub fn add_all(machine: &mut Machine, console: Rc<RefCell<dyn Console>>) {
    machine.add_clearable(ConsoleClearable::new(console.clone()));
    machine.add_command(ClsCommand::new(console.clone()));
    machine.add_command(ColorCommand::new(console.clone()));
    machine.add_function(InKeyFunction::new(console.clone()));
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
    fn test_inkey_ok() {
        Tester::default()
            .run("result = INKEY()")
            .expect_var("result", Value::Text("".to_owned()))
            .check();

        Tester::default()
            .add_input_chars("x")
            .run("result = INKEY()")
            .expect_var("result", Value::Text("x".to_owned()))
            .check();

        Tester::default()
            .add_input_keys(&[Key::CarriageReturn, Key::Backspace, Key::NewLine])
            .run("r1 = INKEY(): r2 = INKEY(): r3 = INKEY()")
            .expect_var("r1", Value::Text("ENTER".to_owned()))
            .expect_var("r2", Value::Text("BS".to_owned()))
            .expect_var("r3", Value::Text("ENTER".to_owned()))
            .check();
    }

    #[test]
    fn test_inkey_errors() {
        check_expr_error("1:10: Syntax error in call to INKEY: no arguments allowed", "INKEY(1)");
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
        check_stmt_err("1:11: Cannot add \"a\" and TRUE", "INPUT \"a\" + TRUE; b?");
    }

    #[test]
    fn test_locate_ok() {
        Tester::default()
            .run("LOCATE 0, 0")
            .expect_output([CapturedOut::Locate(CharsXY::default())])
            .check();

        Tester::default()
            .run("LOCATE 63000, 64000")
            .expect_output([CapturedOut::Locate(CharsXY::new(63000, 64000))])
            .check();
    }

    #[test]
    fn test_locate_errors() {
        check_stmt_err("LOCATE takes two arguments", "LOCATE");
        check_stmt_err("LOCATE takes two arguments", "LOCATE 1");
        check_stmt_err("LOCATE takes two arguments", "LOCATE 1, 2, 3");
        check_stmt_err("LOCATE expects arguments separated by a comma", "LOCATE 1; 2");

        check_stmt_err("Column out of range", "LOCATE -1, 2");
        check_stmt_err("Column out of range", "LOCATE 70000, 2");
        check_stmt_err("Column must be an integer", "LOCATE TRUE, 2");
        check_stmt_err("Column cannot be empty", "LOCATE , 2");

        check_stmt_err("Row out of range", "LOCATE 1, -2");
        check_stmt_err("Row out of range", "LOCATE 1, 70000");
        check_stmt_err("Row must be an integer", "LOCATE 1, TRUE");
        check_stmt_err("Row cannot be empty", "LOCATE 1,");
    }

    #[test]
    fn test_print_ok() {
        Tester::default().run("PRINT").expect_prints([""]).check();
        Tester::default().run("PRINT ;").expect_prints([" "]).check();
        Tester::default().run("PRINT ,").expect_prints(["        "]).check();
        Tester::default().run("PRINT ;,;,").expect_prints(["                "]).check();
        Tester::default().run("PRINT \"abcdefg\", 1").expect_prints(["abcdefg 1"]).check();
        Tester::default().run("PRINT \"abcdefgh\", 1").expect_prints(["abcdefgh        1"]).check();

        Tester::default().run("PRINT 3").expect_prints(["3"]).check();
        Tester::default().run("PRINT 3 = 5").expect_prints(["FALSE"]).check();
        Tester::default()
            .run("PRINT true;123;\"foo bar\"")
            .expect_prints(["TRUE 123 foo bar"])
            .check();
        Tester::default().run("PRINT 6,1;3,5").expect_prints(["6       1 3     5"]).check();

        Tester::default()
            .run(r#"word = "foo": PRINT word, word: PRINT word + "s""#)
            .expect_prints(["foo     foo", "foos"])
            .expect_var("word", "foo")
            .check();
    }

    #[test]
    fn test_print_errors() {
        // Ensure type errors from `Expr` and `Value` bubble up.
        check_stmt_err("1:9: Unexpected value in expression", "PRINT a b");
        check_stmt_err("1:9: Cannot add 3 and TRUE", "PRINT 3 + TRUE");
    }
}
