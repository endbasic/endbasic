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

/// Decoded key presses as returned by the console.
#[derive(Clone, Debug)]
pub enum Key {
    /// The cursor down key.
    ArrowDown,

    /// The cursor left key.
    ArrowLeft,

    /// The cursor right key.
    ArrowRight,

    /// The cursor up key.
    ArrowUp,

    /// Deletes the previous character.
    Backspace,

    /// Accepts the current line.
    CarriageReturn,

    /// A printable character.
    Char(char),

    /// Indicates a request for termination (e.g. `Ctrl-D`).
    Eof,

    /// The escape key.
    Escape,

    /// Indicates a request for interrupt (e.g. `Ctrl-C`).
    // TODO(jmmv): This (and maybe Eof too) should probably be represented as a more generic
    // Control(char) value so that we can represent other control sequences and allow the logic in
    // here to determine what to do with each.
    Interrupt,

    /// Accepts the current line.
    NewLine,

    /// An unknown character or sequence. The text describes what went wrong.
    Unknown(String),
}

/// Indicates what part of the console to clear on a `Console::clear()` call.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ClearType {
    /// Clears the whole console and moves the cursor to the top left corner.
    All,

    /// Clears only the current line without moving the cursor.
    CurrentLine,

    /// Clears from the cursor position to the end of the line without moving the cursor.
    UntilNewLine,
}

/// Represents a position in the console.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Position {
    /// The row number, starting from zero.
    pub row: usize,

    /// The column number, starting from zero.
    pub column: usize,
}

impl std::ops::Sub for Position {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        Position { row: self.row - other.row, column: self.column - other.column }
    }
}

/// Hooks to implement the commands that manipulate the console.
#[async_trait(?Send)]
pub trait Console {
    /// Clears the part of the console given by `how`.
    fn clear(&mut self, how: ClearType) -> io::Result<()>;

    /// Sets the console's foreground and background colors to `fg` and `bg`.
    ///
    /// If any of the colors is `None`, the color is left unchanged.
    fn color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()>;

    /// Enters the alternate console.
    // TODO(jmmv): This API leads to misuse as callers can forget to leave the alternate console.
    fn enter_alt(&mut self) -> io::Result<()>;

    /// Hides the cursor.
    // TODO(jmmv): This API leads to misuse as callers can forget to show the cursor again.
    fn hide_cursor(&mut self) -> io::Result<()>;

    /// Returns true if the console is attached to an interactive terminal.  This controls whether
    /// reading a line echoes back user input, for example.
    fn is_interactive(&self) -> bool;

    /// Leaves the alternate console.
    fn leave_alt(&mut self) -> io::Result<()>;

    /// Moves the cursor to the given position, which must be within the screen.
    fn locate(&mut self, pos: Position) -> io::Result<()>;

    /// Moves the cursor within the line.  Positive values move right, negative values move left.
    fn move_within_line(&mut self, off: i16) -> io::Result<()>;

    /// Writes `text` to the console, followed by a newline or CRLF pair depending on the needs of
    /// the console to advance a line.
    // TODO(jmmv): Remove this in favor of write?
    fn print(&mut self, text: &str) -> io::Result<()>;

    /// Waits for and returns the next key press.
    async fn read_key(&mut self) -> io::Result<Key>;

    /// Shows the cursor.
    fn show_cursor(&mut self) -> io::Result<()>;

    /// Queries the size of the console.
    ///
    /// The returned position represents the first row and column that lay *outside* of the console.
    fn size(&self) -> io::Result<Position>;

    /// Writes the raw `bytes` into the console.
    fn write(&mut self, bytes: &[u8]) -> io::Result<()>;
}

/// Reads a line of text interactively from the console, using the given `prompt` and pre-filling
/// the input with `previous`.
async fn read_line_interactive(
    console: &mut dyn Console,
    prompt: &str,
    previous: &str,
) -> io::Result<String> {
    let mut line = String::from(previous);
    console.clear(ClearType::UntilNewLine)?;
    if !prompt.is_empty() || !line.is_empty() {
        console.write(format!("{}{}", prompt, line).as_bytes())?;
    }

    let width = {
        // Assumes that the prompt was printed at column 0.  If that was not the case, line length
        // calculation does not work.
        let console_size = console.size()?;
        console_size.column - prompt.len()
    };

    // Insertion position *within* the line, without accounting for the prompt.
    let mut pos = line.len();

    loop {
        match console.read_key().await? {
            Key::ArrowUp | Key::ArrowDown => {
                // TODO(jmmv): Implement history tracking.
            }

            Key::ArrowLeft => {
                if pos > 0 {
                    console.move_within_line(-1)?;
                    pos -= 1;
                }
            }

            Key::ArrowRight => {
                if pos < line.len() {
                    console.move_within_line(1)?;
                    pos += 1;
                }
            }

            Key::Backspace => {
                if pos > 0 {
                    console.hide_cursor()?;
                    console.move_within_line(-1)?;
                    console.write(line[pos..].as_bytes())?;
                    console.write(&[b' '])?;
                    console.move_within_line(-((line.len() - pos) as i16 + 1))?;
                    console.show_cursor()?;
                    line.remove(pos - 1);
                    pos -= 1;
                }
            }

            Key::CarriageReturn => {
                // TODO(jmmv): This is here because the integration tests may be checked out with
                // CRLF line endings on Windows, which means we'd see two characters to end a line
                // instead of one.  Not sure if we should do this or if instead we should ensure
                // the golden data we feed to the tests has single-character line endings.
                if cfg!(not(target_os = "windows")) {
                    console.write(&[b'\r', b'\n'])?;
                    break;
                }
            }

            Key::Char(ch) => {
                debug_assert!(line.len() < width);
                if line.len() == width - 1 {
                    // TODO(jmmv): Implement support for lines that exceed the width of the input
                    // field (the width of the screen).
                    continue;
                }

                if pos < line.len() {
                    console.hide_cursor()?;
                    console.write(&[ch as u8])?;
                    console.write(line[pos..].as_bytes())?;
                    console.move_within_line(-((line.len() - pos) as i16))?;
                    console.show_cursor()?;
                } else {
                    console.write(&[ch as u8])?;
                }
                line.insert(pos, ch);
                pos += 1;
            }

            Key::Eof => return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "EOF")),

            Key::Escape => {
                // Intentionally ignored.
            }

            Key::Interrupt => return Err(io::Error::new(io::ErrorKind::Interrupted, "Ctrl+C")),

            Key::NewLine => {
                console.write(&[b'\r', b'\n'])?;
                break;
            }

            // TODO(jmmv): Should do something smarter with unknown keys.
            Key::Unknown(_) => (),
        }
    }
    Ok(line)
}

/// Reads a line of text interactively from the console, which is not expected to be a TTY.
async fn read_line_raw(console: &mut dyn Console) -> io::Result<String> {
    let mut line = String::new();
    loop {
        match console.read_key().await? {
            Key::ArrowUp | Key::ArrowDown | Key::ArrowLeft | Key::ArrowRight => (),
            Key::Backspace => {
                if !line.is_empty() {
                    line.pop();
                }
            }
            Key::CarriageReturn => {
                // TODO(jmmv): This is here because the integration tests may be checked out with
                // CRLF line endings on Windows, which means we'd see two characters to end a line
                // instead of one.  Not sure if we should do this or if instead we should ensure
                // the golden data we feed to the tests has single-character line endings.
                if cfg!(not(target_os = "windows")) {
                    break;
                }
            }
            Key::Char(ch) => line.push(ch),
            Key::Escape => (),
            Key::Eof => return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "EOF")),
            Key::Interrupt => return Err(io::Error::new(io::ErrorKind::Interrupted, "Ctrl+C")),
            Key::NewLine => break,
            Key::Unknown(bad_input) => line += &bad_input,
        }
    }
    Ok(line)
}

/// Reads a line from the console.  If the console is interactive, this does fancy line editing and
/// uses the given `prompt` and pre-fills the input with `previous`.
pub async fn read_line(
    console: &mut dyn Console,
    prompt: &str,
    previous: &str,
) -> io::Result<String> {
    if console.is_interactive() {
        read_line_interactive(console, prompt, previous).await
    } else {
        read_line_raw(console).await
    }
}

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
            match read_line(&mut *console, &prompt, &previous_answer).await {
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

        self.console.borrow_mut().locate(Position { row, column })?;
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
    use futures_lite::future::block_on;

    /// Builder pattern to construct a test for `read_line_interactive`.
    #[must_use]
    struct ReadLineInteractiveTest {
        keys: Vec<Key>,
        prompt: &'static str,
        previous: &'static str,
        exp_line: &'static str,
        exp_output: Vec<CapturedOut>,
    }

    impl Default for ReadLineInteractiveTest {
        /// Constructs a new test that feeds no input to the function, with no prompt or previous
        /// text, and expects an empty return line and no changes to the console.
        fn default() -> Self {
            Self {
                keys: vec![],
                prompt: "",
                previous: "",
                exp_line: "",
                exp_output: vec![CapturedOut::Clear(ClearType::UntilNewLine)],
            }
        }
    }

    impl ReadLineInteractiveTest {
        /// Adds `key` to the golden input.
        fn add_key(mut self, key: Key) -> Self {
            self.keys.push(key);
            self
        }

        /// Adds a bunch of `chars` as individual key presses to the golden input.
        fn add_key_chars(mut self, chars: &'static str) -> Self {
            for ch in chars.chars() {
                self.keys.push(Key::Char(ch));
            }
            self
        }

        /// Adds a single state change to the expected output.
        fn add_output(mut self, output: CapturedOut) -> Self {
            self.exp_output.push(output);
            self
        }

        /// Adds a bunch of `bytes` as separate console writes to the expected output.
        fn add_output_bytes(mut self, bytes: &'static [u8]) -> Self {
            if bytes.is_empty() {
                self.exp_output.push(CapturedOut::Write(vec![]))
            } else {
                for b in bytes.iter() {
                    self.exp_output.push(CapturedOut::Write(vec![*b]))
                }
            }
            self
        }

        /// Sets the expected resulting line for the test.
        fn set_line(mut self, line: &'static str) -> Self {
            self.exp_line = line;
            self
        }

        /// Sets the prompt to use for the test.
        fn set_prompt(mut self, prompt: &'static str) -> Self {
            self.prompt = prompt;
            self
        }

        /// Sets the previous text to use for the test.
        fn set_previous(mut self, previous: &'static str) -> Self {
            self.previous = previous;
            self
        }

        /// Adds a final return key to the golden input, a newline to the expected output, and
        /// executes the test.
        fn accept(mut self) {
            self.keys.push(Key::NewLine);
            self.exp_output.push(CapturedOut::Write(vec![b'\r', b'\n']));

            let mut console = MockConsole::default();
            console.add_input_keys(&self.keys);
            console.set_size(Position { row: 5, column: 15 });
            let line =
                block_on(read_line_interactive(&mut console, self.prompt, self.previous)).unwrap();
            assert_eq!(self.exp_line, &line);
            assert_eq!(self.exp_output.as_slice(), console.captured_out());
        }
    }

    #[test]
    fn test_read_line_interactive_empty() {
        ReadLineInteractiveTest::default().accept();
        ReadLineInteractiveTest::default().add_key(Key::Backspace).accept();
        ReadLineInteractiveTest::default().add_key(Key::ArrowLeft).accept();
        ReadLineInteractiveTest::default().add_key(Key::ArrowRight).accept();
    }

    #[test]
    fn test_read_line_with_prompt() {
        ReadLineInteractiveTest::default()
            .set_prompt("Ready> ")
            .add_output(CapturedOut::Write(b"Ready> ".to_vec()))
            // -
            .add_key_chars("hello")
            .add_output_bytes(b"hello")
            // -
            .set_line("hello")
            .accept();

        ReadLineInteractiveTest::default()
            .set_prompt("Cannot delete")
            .add_output(CapturedOut::Write(b"Cannot delete".to_vec()))
            // -
            .add_key(Key::Backspace)
            .accept();
    }

    #[test]
    fn test_read_line_interactive_trailing_input() {
        ReadLineInteractiveTest::default()
            .add_key_chars("hello")
            .add_output_bytes(b"hello")
            // -
            .set_line("hello")
            .accept();

        ReadLineInteractiveTest::default()
            .set_previous("123")
            .add_output(CapturedOut::Write(b"123".to_vec()))
            // -
            .add_key_chars("hello")
            .add_output_bytes(b"hello")
            // -
            .set_line("123hello")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_middle_input() {
        ReadLineInteractiveTest::default()
            .add_key_chars("some text")
            .add_output_bytes(b"some text")
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::ArrowRight)
            .add_output(CapturedOut::MoveWithinLine(1))
            // -
            .add_key_chars(" ")
            .add_output(CapturedOut::HideCursor)
            .add_output_bytes(b" ")
            .add_output(CapturedOut::Write(b"xt".to_vec()))
            .add_output(CapturedOut::MoveWithinLine(-2))
            .add_output(CapturedOut::ShowCursor)
            // -
            .add_key_chars(".")
            .add_output(CapturedOut::HideCursor)
            .add_output_bytes(b".")
            .add_output(CapturedOut::Write(b"xt".to_vec()))
            .add_output(CapturedOut::MoveWithinLine(-2))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("some te .xt")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_trailing_backspace() {
        ReadLineInteractiveTest::default()
            .add_key_chars("bar")
            .add_output_bytes(b"bar")
            // -
            .add_key(Key::Backspace)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output_bytes(b"")
            .add_output_bytes(b" ")
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::ShowCursor)
            // -
            .add_key_chars("zar")
            .add_output_bytes(b"zar")
            // -
            .set_line("bazar")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_middle_backspace() {
        ReadLineInteractiveTest::default()
            .add_key_chars("has a tYpo")
            .add_output_bytes(b"has a tYpo")
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::Backspace)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::Write(b"po".to_vec()))
            .add_output_bytes(b" ")
            .add_output(CapturedOut::MoveWithinLine(-3))
            .add_output(CapturedOut::ShowCursor)
            // -
            .add_key_chars("y")
            .add_output(CapturedOut::HideCursor)
            .add_output_bytes(b"y")
            .add_output(CapturedOut::Write(b"po".to_vec()))
            .add_output(CapturedOut::MoveWithinLine(-2))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("has a typo")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_test_move_bounds() {
        ReadLineInteractiveTest::default()
            .set_previous("12")
            .add_output(CapturedOut::Write(b"12".to_vec()))
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::ArrowLeft)
            .add_key(Key::ArrowLeft)
            .add_key(Key::ArrowLeft)
            .add_key(Key::ArrowLeft)
            // -
            .add_key(Key::ArrowRight)
            .add_output(CapturedOut::MoveWithinLine(1))
            // -
            .add_key(Key::ArrowRight)
            .add_output(CapturedOut::MoveWithinLine(1))
            // -
            .add_key(Key::ArrowRight)
            .add_key(Key::ArrowRight)
            // -
            .add_key_chars("3")
            .add_output_bytes(b"3")
            // -
            .set_line("123")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_horizontal_scrolling_not_implemented() {
        ReadLineInteractiveTest::default()
            .add_key_chars("1234567890123456789")
            .add_output_bytes(b"12345678901234")
            // -
            .set_line("12345678901234")
            .accept();

        ReadLineInteractiveTest::default()
            .add_key_chars("1234567890123456789")
            .add_output_bytes(b"12345678901234")
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key_chars("these will all be ignored")
            // -
            .set_line("12345678901234")
            .accept();

        ReadLineInteractiveTest::default()
            .set_prompt("12345")
            .set_previous("67890")
            .add_output(CapturedOut::Write(b"1234567890".to_vec()))
            // -
            .add_key_chars("1234567890")
            .add_output_bytes(b"1234")
            // -
            .set_line("678901234")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_history_not_implemented() {
        ReadLineInteractiveTest::default().add_key(Key::ArrowUp).accept();
        ReadLineInteractiveTest::default().add_key(Key::ArrowDown).accept();
    }

    #[test]
    fn test_read_line_ignored_keys() {
        ReadLineInteractiveTest::default()
            .add_key_chars("not ")
            .add_output_bytes(b"not ")
            // -
            .add_key(Key::Escape)
            // -
            .add_key_chars("affected")
            .add_output_bytes(b"affected")
            // -
            .set_line("not affected")
            .accept();
    }

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
            .expect_output([CapturedOut::Locate(Position { row: 0, column: 0 })])
            .check();

        Tester::default()
            .run("LOCATE 1000, 2000")
            .expect_output([CapturedOut::Locate(Position { row: 1000, column: 2000 })])
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
