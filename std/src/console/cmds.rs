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
use endbasic_core::ast::{ArgSep, Value, VarType};
use endbasic_core::exec::Machine;
use endbasic_core::syms::{
    CallError, CallResult, Callable, CallableMetadata, CallableMetadataBuilder,
};
use endbasic_core::LineCol;
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
graphics, run HELP \"GRAPHICS\".
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
impl Callable for ClsCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, _machine: &mut Machine) -> CallResult {
        if !args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        self.console.borrow_mut().clear(ClearType::All)?;
        Ok(Value::Void)
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
impl Callable for ColorCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, machine: &mut Machine) -> CallResult {
        let mut iter = machine.load_all(args)?.into_iter();

        fn get_color(value: Value, pos: LineCol) -> Result<Option<u8>, CallError> {
            let i = value.as_i32().map_err(|e| CallError::ArgumentError(pos, format!("{}", e)))?;
            if i >= 0 && i <= std::u8::MAX as i32 {
                Ok(Some(i as u8))
            } else {
                Err(CallError::ArgumentError(pos, "Color out of range".to_owned()))
            }
        }

        let fg = match iter.next() {
            None => None,
            Some((Value::Missing, _pos)) => None,
            Some((value, pos)) => get_color(value, pos)?,
        };

        let bg = match iter.next() {
            Some((Value::Separator(ArgSep::Long), _pos)) => match iter.next() {
                Some((Value::Missing, _pos)) => None,
                Some((value, pos)) => get_color(value, pos)?,
                None => return Err(CallError::SyntaxError),
            },
            Some((Value::Missing, _pos)) => {
                return Err(CallError::SyntaxError);
            }
            Some((_value, _pos)) => return Err(CallError::SyntaxError),
            None => None,
        };

        if iter.next().is_some() {
            return Err(CallError::SyntaxError);
        }

        self.console.borrow_mut().set_color(fg, bg)?;
        Ok(Value::Void)
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
    k$ = \"\": WHILE k$ <> \"ESC\": k = INKEY$: SLEEP 0.01: WEND
This non-blocking design lets you to combine the reception of multiple evens, such as from \
GPIO_INPUT?, within the same loop.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Callable for InKeyFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, _machine: &mut Machine) -> CallResult {
        if !args.is_empty() {
            return Err(CallError::SyntaxError);
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
                .with_syntax("[\"prompt\" <;|,>] variableref")
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
impl Callable for InputCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, machine: &mut Machine) -> CallResult {
        let mut iter = args.into_iter().rev();

        // Pay attention: we are iterating the arguments in reverse!

        let (vref, pos) = match iter.next() {
            None => return Err(CallError::SyntaxError),
            Some((Value::VarRef(vref), pos)) => (vref, pos),
            Some((Value::Missing, _pos)) => {
                return Err(CallError::SyntaxError);
            }
            Some((_value, pos)) => {
                return Err(CallError::ArgumentError(
                    pos,
                    "INPUT requires a variable reference".to_owned(),
                ))
            }
        };

        let prompt = match iter.next() {
            None => "? ".to_owned(),

            Some((Value::Separator(sep @ ArgSep::Long), _pos))
            | Some((Value::Separator(sep @ ArgSep::Short), _pos)) => {
                let (value, pos) = match iter.next() {
                    Some((Value::VarRef(vref), pos)) => (
                        machine
                            .get_symbols()
                            .get_var(&vref)
                            .map_err(|e| CallError::ArgumentError(pos, e.to_string()))?
                            .clone(),
                        pos,
                    ),
                    Some((value, pos)) => (value, pos),
                    None => return Err(CallError::SyntaxError),
                };
                let mut prompt = match value {
                    Value::Missing => "".to_owned(),
                    Value::Text(t) => t.to_owned(),
                    _ => {
                        return Err(CallError::ArgumentError(
                            pos,
                            "INPUT prompt must be a string".to_owned(),
                        ));
                    }
                };
                if sep == ArgSep::Short {
                    prompt += "? ";
                }
                prompt
            }

            Some((_value, _pos)) => return Err(CallError::SyntaxError),
        };

        if iter.next().is_some() {
            return Err(CallError::SyntaxError);
        }

        let vref = machine
            .get_symbols()
            .qualify_varref(&vref)
            .map_err(|e| CallError::EvalError(pos, format!("{}", e)))?;

        let mut console = self.console.borrow_mut();
        let mut previous_answer = String::new();
        loop {
            match read_line(&mut *console, &prompt, &previous_answer, None).await {
                Ok(answer) => match Value::parse_as(vref.ref_type(), answer.trim_end()) {
                    Ok(value) => {
                        machine
                            .get_mut_symbols()
                            .set_var(&vref, value)
                            .map_err(|e| CallError::EvalError(pos, format!("{}", e)))?;
                        return Ok(Value::Void);
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
impl Callable for LocateCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, machine: &mut Machine) -> CallResult {
        let mut iter = machine.load_all(args)?.into_iter();

        fn get_coord(value: Value, pos: LineCol, name: &str) -> Result<u16, CallError> {
            let i = value.as_i32().map_err(|e| CallError::ArgumentError(pos, format!("{}", e)))?;
            match u16::try_from(i) {
                Ok(v) => Ok(v),
                Err(_) => Err(CallError::ArgumentError(pos, format!("{} out of range", name))),
            }
        }

        let (column, column_pos) = match iter.next() {
            None => return Err(CallError::SyntaxError),
            Some((Value::Missing, _pos)) => {
                return Err(CallError::SyntaxError);
            }
            Some((value, pos)) => (get_coord(value, pos, "Column")?, pos),
        };

        match iter.next() {
            Some((Value::Separator(ArgSep::Long), _pos)) => (),
            _ => return Err(CallError::SyntaxError),
        }

        let (row, row_pos) = match iter.next() {
            None => return Err(CallError::SyntaxError),
            Some((Value::Missing, _pos)) => {
                return Err(CallError::SyntaxError);
            }
            Some((value, pos)) => (get_coord(value, pos, "Row")?, pos),
        };

        if iter.next().is_some() {
            return Err(CallError::SyntaxError);
        }

        let mut console = self.console.borrow_mut();
        let size = console.size_chars()?;

        if column >= size.x {
            return Err(CallError::ArgumentError(
                column_pos,
                format!("Column {} exceeds visible range of {}", column, size.x - 1),
            ));
        }
        if row >= size.y {
            return Err(CallError::ArgumentError(
                row_pos,
                format!("Row {} exceeds visible range of {}", row, size.y - 1),
            ));
        }

        console.locate(CharsXY::new(column, row))?;
        Ok(Value::Void)
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
                .with_syntax("[expr1 [<;|,> [.. exprN]]]")
                .with_category(CATEGORY)
                .with_description(
                    "Prints one or more values to the console.
The expressions given as arguments are all evaluated and converted to strings before they are \
printed.  See the documentation of STR$() for the conversion rules.
Using a `;` separator between arguments causes the two adjacent values to be displayed together.  \
For strings, this means that no space is added between them; for all other types, a space is added \
after the value on the left side.
Using a `,` separator between arguments works the same as `;` except that the fields are \
left-aligned to 14-character wide fields on the screen.
If the last expression is empty (i.e. if the statement ends in a semicolon or a comma), then \
the cursor position remains on the same line of the message right after what was printed.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Callable for PrintCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, machine: &mut Machine) -> CallResult {
        let iter = machine.load_all(args)?.into_iter();

        let mut text = String::new();
        let mut nl = true;
        let mut add_space = false;
        for (value, _pos) in iter {
            match value {
                Value::Missing => (),
                Value::Separator(ArgSep::Short) => {
                    if add_space {
                        text += " "
                    }
                    add_space = false;
                    nl = false;
                }
                Value::Separator(ArgSep::Long) => {
                    text += " ";
                    while text.len() % 14 != 0 {
                        text += " ";
                    }
                    add_space = false;
                    nl = false;
                }
                Value::Separator(_) => return Err(CallError::SyntaxError),
                Value::Text(t) => {
                    add_space = false;
                    text += &t;
                    nl = true;
                }
                value => {
                    add_space = true;
                    text += &value.to_text();
                    nl = true;
                }
            }
        }

        if nl {
            self.console.borrow_mut().print(&text)?;
        } else {
            self.console.borrow_mut().write(&text)?;
        }
        Ok(Value::Void)
    }
}

/// The `SCRCOLS` function.
pub struct ScrColsFunction {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl ScrColsFunction {
    /// Creates a new instance of the function.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("SCRCOLS", VarType::Integer)
                .with_syntax("")
                .with_category(CATEGORY)
                .with_description(
                    "Returns the number of columns in the text console.
See SCRROWS to query the other dimension.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Callable for ScrColsFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, _machine: &mut Machine) -> CallResult {
        if !args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        let size = self.console.borrow().size_chars()?;
        Ok(Value::Integer(i32::from(size.x)))
    }
}

/// The `SCRROWS` function.
pub struct ScrRowsFunction {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl ScrRowsFunction {
    /// Creates a new instance of the function.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("SCRROWS", VarType::Integer)
                .with_syntax("")
                .with_category(CATEGORY)
                .with_description(
                    "Returns the number of rows in the text console.
See SCRCOLS to query the other dimension.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Callable for ScrRowsFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, _machine: &mut Machine) -> CallResult {
        if !args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        let size = self.console.borrow().size_chars()?;
        Ok(Value::Integer(i32::from(size.y)))
    }
}

/// Adds all console-related commands for the given `console` to the `machine`.
pub fn add_all(machine: &mut Machine, console: Rc<RefCell<dyn Console>>) {
    machine.add_clearable(ConsoleClearable::new(console.clone()));
    machine.add_callable(ClsCommand::new(console.clone()));
    machine.add_callable(ColorCommand::new(console.clone()));
    machine.add_callable(InKeyFunction::new(console.clone()));
    machine.add_callable(InputCommand::new(console.clone()));
    machine.add_callable(LocateCommand::new(console.clone()));
    machine.add_callable(PrintCommand::new(console.clone()));
    machine.add_callable(ScrColsFunction::new(console.clone()));
    machine.add_callable(ScrRowsFunction::new(console));
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
        check_stmt_err("1:1: In call to CLS: expected no arguments", "CLS 1");
    }

    #[test]
    fn test_color_ok() {
        fn t() -> Tester {
            Tester::default()
        }
        t().run("COLOR").expect_output([CapturedOut::SetColor(None, None)]).check();
        t().run("COLOR ,").expect_output([CapturedOut::SetColor(None, None)]).check();
        t().run("COLOR 1").expect_output([CapturedOut::SetColor(Some(1), None)]).check();
        t().run("COLOR 1,").expect_output([CapturedOut::SetColor(Some(1), None)]).check();
        t().run("COLOR , 1").expect_output([CapturedOut::SetColor(None, Some(1))]).check();
        t().run("COLOR 10, 5").expect_output([CapturedOut::SetColor(Some(10), Some(5))]).check();
        t().run("COLOR 0, 0").expect_output([CapturedOut::SetColor(Some(0), Some(0))]).check();
        t().run("COLOR 255, 255")
            .expect_output([CapturedOut::SetColor(Some(255), Some(255))])
            .check();
    }

    #[test]
    fn test_color_errors() {
        check_stmt_err("1:1: In call to COLOR: expected [fg%][, [bg%]]", "COLOR 1, 2, 3");

        check_stmt_err("1:1: In call to COLOR: 1:7: Color out of range", "COLOR 1000, 0");
        check_stmt_err("1:1: In call to COLOR: 1:10: Color out of range", "COLOR 0, 1000");

        check_stmt_err("1:1: In call to COLOR: 1:7: TRUE is not a number", "COLOR TRUE, 0");
        check_stmt_err("1:1: In call to COLOR: 1:10: TRUE is not a number", "COLOR 0, TRUE");
    }

    #[test]
    fn test_inkey_ok() {
        Tester::default()
            .run("result = INKEY")
            .expect_var("result", Value::Text("".to_owned()))
            .check();

        Tester::default()
            .add_input_chars("x")
            .run("result = INKEY")
            .expect_var("result", Value::Text("x".to_owned()))
            .check();

        Tester::default()
            .add_input_keys(&[Key::CarriageReturn, Key::Backspace, Key::NewLine])
            .run("r1 = INKEY$: r2 = INKEY: r3 = INKEY$")
            .expect_var("r1", Value::Text("ENTER".to_owned()))
            .expect_var("r2", Value::Text("BS".to_owned()))
            .expect_var("r3", Value::Text("ENTER".to_owned()))
            .check();
    }

    #[test]
    fn test_inkey_errors() {
        check_expr_compilation_error(
            "1:10: In call to INKEY: expected no arguments nor parenthesis",
            "INKEY()",
        );
        check_expr_compilation_error(
            "1:10: In call to INKEY: expected no arguments nor parenthesis",
            "INKEY(1)",
        );
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

        t("INPUT foo\nPRINT foo", "9\n", " 9", "foo", 9);
        t("INPUT ; foo\nPRINT foo", "9\n", " 9", "foo", 9);
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
            .expect_prints([" 84"])
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
        check_stmt_err("1:1: In call to INPUT: expected [\"prompt\" <;|,>] variableref", "INPUT");
        check_stmt_err(
            "1:1: In call to INPUT: expected [\"prompt\" <;|,>] variableref",
            "INPUT ; ,",
        );
        check_stmt_err("1:1: In call to INPUT: expected [\"prompt\" <;|,>] variableref", "INPUT ;");
        check_stmt_err("1:1: In call to INPUT: 1:7: INPUT prompt must be a string", "INPUT 3 ; a");
        check_stmt_err(
            "1:1: In call to INPUT: expected [\"prompt\" <;|,>] variableref",
            "INPUT \"foo\" AS bar",
        );
        check_stmt_uncatchable_err("1:9: Undefined variable a", "INPUT ; a + 1");
        Tester::default()
            .run("a = 3: INPUT ; a + 1")
            .expect_err("1:8: In call to INPUT: 1:18: INPUT requires a variable reference")
            .expect_var("a", 3)
            .check();
        check_stmt_uncatchable_err("1:11: Cannot + STRING and BOOLEAN", "INPUT \"a\" + TRUE; b?");
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
        check_stmt_err("1:1: In call to LOCATE: expected column%, row%", "LOCATE");
        check_stmt_err("1:1: In call to LOCATE: expected column%, row%", "LOCATE 1");
        check_stmt_err("1:1: In call to LOCATE: expected column%, row%", "LOCATE 1, 2, 3");
        check_stmt_err("1:1: In call to LOCATE: expected column%, row%", "LOCATE 1; 2");

        check_stmt_err("1:1: In call to LOCATE: 1:8: Column out of range", "LOCATE -1, 2");
        check_stmt_err("1:1: In call to LOCATE: 1:8: Column out of range", "LOCATE 70000, 2");
        check_stmt_err("1:1: In call to LOCATE: 1:8: TRUE is not a number", "LOCATE TRUE, 2");
        check_stmt_err("1:1: In call to LOCATE: expected column%, row%", "LOCATE , 2");

        check_stmt_err("1:1: In call to LOCATE: 1:11: Row out of range", "LOCATE 1, -2");
        check_stmt_err("1:1: In call to LOCATE: 1:11: Row out of range", "LOCATE 1, 70000");
        check_stmt_err("1:1: In call to LOCATE: 1:11: TRUE is not a number", "LOCATE 1, TRUE");
        check_stmt_err("1:1: In call to LOCATE: expected column%, row%", "LOCATE 1,");

        let mut t = Tester::default();
        t.get_console().borrow_mut().set_size_chars(CharsXY { x: 30, y: 20 });
        t.run("LOCATE 30, 0")
            .expect_err("1:1: In call to LOCATE: 1:8: Column 30 exceeds visible range of 29")
            .check();
        t.run("LOCATE 31, 0")
            .expect_err("1:1: In call to LOCATE: 1:8: Column 31 exceeds visible range of 29")
            .check();
        t.run("LOCATE 0, 20")
            .expect_err("1:1: In call to LOCATE: 1:11: Row 20 exceeds visible range of 19")
            .check();
        t.run("LOCATE 0, 21")
            .expect_err("1:1: In call to LOCATE: 1:11: Row 21 exceeds visible range of 19")
            .check();
    }

    #[test]
    fn test_print_ok() {
        Tester::default().run("PRINT").expect_prints([""]).check();
        Tester::default().run("PRINT ;").expect_output([CapturedOut::Write("".to_owned())]).check();
        Tester::default()
            .run("PRINT ,")
            .expect_output([CapturedOut::Write("              ".to_owned())])
            .check();
        Tester::default()
            .run("PRINT ;,;,")
            .expect_output([CapturedOut::Write("                            ".to_owned())])
            .check();

        Tester::default()
            .run("PRINT \"1234567890123\", \"4\"")
            .expect_prints(["1234567890123 4"])
            .check();
        Tester::default()
            .run("PRINT \"12345678901234\", \"5\"")
            .expect_prints(["12345678901234              5"])
            .check();

        Tester::default().run("PRINT \"abcdefg\", 1").expect_prints(["abcdefg        1"]).check();
        Tester::default().run("PRINT \"abcdefgh\", 1").expect_prints(["abcdefgh       1"]).check();

        Tester::default().run("PRINT 3").expect_prints([" 3"]).check();
        Tester::default().run("PRINT -3").expect_prints(["-3"]).check();
        Tester::default().run("PRINT 3 = 5").expect_prints(["FALSE"]).check();

        Tester::default().run("PRINT 3; -1; 4").expect_prints([" 3 -1  4"]).check();
        Tester::default().run("PRINT \"foo\"; \"bar\"").expect_prints(["foobar"]).check();
        Tester::default()
            .run(r#"PRINT "foo";: PRINT "bar""#)
            .expect_output([
                CapturedOut::Write("foo".to_owned()),
                CapturedOut::Print("bar".to_owned()),
            ])
            .check();
        Tester::default()
            .run("PRINT true;123;\"foo bar\"")
            .expect_prints(["TRUE  123 foo bar"])
            .check();

        Tester::default()
            .run("PRINT 6,1;3,5")
            .expect_prints([" 6             1  3          5"])
            .check();

        Tester::default()
            .run(r#"word = "foo": PRINT word, word: PRINT word + "s""#)
            .expect_prints(["foo           foo", "foos"])
            .expect_var("word", "foo")
            .check();

        Tester::default()
            .run(r#"word = "foo": PRINT word,: PRINT word;: PRINT word + "s""#)
            .expect_output([
                CapturedOut::Write("foo           ".to_owned()),
                CapturedOut::Write("foo".to_owned()),
                CapturedOut::Print("foos".to_owned()),
            ])
            .expect_var("word", "foo")
            .check();
    }

    #[test]
    fn test_print_control_chars() {
        let mut found_any = false;
        for i in 0..1024 {
            let ch = char::from_u32(i).unwrap();
            let ch_var = format!("{}", ch);
            let exp_ch = if ch.is_control() {
                found_any = true;
                " "
            } else {
                &ch_var
            };
            Tester::default()
                .set_var("ch", Value::Text(ch_var.clone()))
                .run("PRINT ch")
                .expect_prints([exp_ch])
                .expect_var("ch", Value::Text(ch_var.clone()))
                .check();
        }
        assert!(found_any, "Test did not exercise what we wanted");
    }

    #[test]
    fn test_print_errors() {
        check_stmt_err(
            "1:1: In call to PRINT: expected [expr1 [<;|,> [.. exprN]]]",
            "PRINT 3 AS 4",
        );
        check_stmt_err(
            "1:1: In call to PRINT: expected [expr1 [<;|,> [.. exprN]]]",
            "PRINT 3, 4 AS 5",
        );
        // Ensure type errors from `Expr` and `Value` bubble up.
        check_stmt_uncatchable_err("1:9: Unexpected value in expression", "PRINT a b");
        check_stmt_uncatchable_err("1:9: Cannot + INTEGER and BOOLEAN", "PRINT 3 + TRUE");
    }

    #[test]
    fn test_scrcols() {
        let mut t = Tester::default();
        t.get_console().borrow_mut().set_size_chars(CharsXY { x: 12345, y: 0 });
        t.run("result = SCRCOLS").expect_var("result", 12345i32).check();

        check_expr_compilation_error(
            "1:10: In call to SCRCOLS: expected no arguments nor parenthesis",
            "SCRCOLS()",
        );
        check_expr_compilation_error(
            "1:10: In call to SCRCOLS: expected no arguments nor parenthesis",
            "SCRCOLS(1)",
        );
    }

    #[test]
    fn test_scrrows() {
        let mut t = Tester::default();
        t.get_console().borrow_mut().set_size_chars(CharsXY { x: 0, y: 768 });
        t.run("result = SCRROWS").expect_var("result", 768i32).check();

        check_expr_compilation_error(
            "1:10: In call to SCRROWS: expected no arguments nor parenthesis",
            "SCRROWS()",
        );
        check_expr_compilation_error(
            "1:10: In call to SCRROWS: expected no arguments nor parenthesis",
            "SCRROWS(1)",
        );
    }
}
