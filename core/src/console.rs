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
use crate::exec::{self, BuiltinCommand, Machine};
use async_trait::async_trait;
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

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
#[derive(Debug, Eq, PartialEq)]
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

/// Hooks to implement the commands that manipulate the console.
#[async_trait(?Send)]
pub trait Console {
    /// Clears the part of the console given by `how`.
    fn clear(&mut self, how: ClearType) -> io::Result<()>;

    /// Sets the console's foreground and background colors to `fg` and `bg`.
    ///
    /// If any of the colors is `None`, the color is left unchanged.
    fn color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()>;

    /// Hides the cursor.
    // TODO(jmmv): This API leads to misuse as callers can forget to show the cursor again.
    fn hide_cursor(&mut self) -> io::Result<()>;

    /// Returns true if the console is attached to an interactive terminal.  This controls whether
    /// reading a line echoes back user input, for example.
    fn is_interactive(&self) -> bool;

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
                    console.write(&[10 as u8, 13 as u8])?;
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

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        _machine: &mut Machine,
    ) -> exec::Result<()> {
        if !args.is_empty() {
            return exec::new_usage_error("CLS takes no arguments");
        }
        self.console.borrow_mut().clear(ClearType::All)?;
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
        "[fg%][, [bg%]]"
    }

    fn description(&self) -> &'static str {
        "Sets the foreground and background colors.
Color numbers are given as ANSI numbers and can be between 0 and 255.  If a color number is not \
specified, then the color is reset to the console's default.  The console default does not \
necessarily match any other color specifiable in the 0 to 255 range, as it might be transparent."
    }

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        machine: &mut Machine,
    ) -> exec::Result<()> {
        let (fg_expr, bg_expr): (&Option<Expr>, &Option<Expr>) = match args {
            [] => (&None, &None),
            [(fg, ArgSep::End)] => (fg, &None),
            [(fg, ArgSep::Long), (bg, ArgSep::End)] => (fg, bg),
            _ => {
                return exec::new_usage_error(
                    "COLOR takes at most two arguments separated by a comma",
                )
            }
        };

        fn get_color(e: &Option<Expr>, machine: &Machine) -> exec::Result<Option<u8>> {
            match e {
                Some(e) => match e.eval(machine.get_vars())? {
                    Value::Integer(i) if i >= 0 && i <= std::u8::MAX as i32 => Ok(Some(i as u8)),
                    Value::Integer(_) => exec::new_usage_error("Color out of range"),
                    _ => exec::new_usage_error("Color must be an integer"),
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

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        machine: &mut Machine,
    ) -> exec::Result<()> {
        if args.len() != 2 {
            return exec::new_usage_error("INPUT requires two arguments");
        }

        let mut prompt = match &args[0].0 {
            Some(e) => match e.eval(machine.get_vars())? {
                Value::Text(t) => t,
                _ => return exec::new_usage_error("INPUT prompt must be a string"),
            },
            None => "".to_owned(),
        };
        if let ArgSep::Short = args[0].1 {
            prompt += "? ";
        }

        let vref = match &args[1].0 {
            Some(Expr::Symbol(vref)) => vref,
            _ => return exec::new_usage_error("INPUT requires a variable reference"),
        };

        let mut console = self.console.borrow_mut();
        let mut previous_answer = String::new();
        loop {
            match read_line(&mut *console, &prompt, &previous_answer).await {
                Ok(answer) => match Value::parse_as(vref.ref_type(), answer.trim_end()) {
                    Ok(value) => {
                        machine.get_mut_vars().set(vref, value)?;
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

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        machine: &mut Machine,
    ) -> exec::Result<()> {
        if args.len() != 2 {
            return exec::new_usage_error("LOCATE takes two arguments");
        }
        let (row_arg, column_arg) = (&args[0], &args[1]);
        if row_arg.1 != ArgSep::Long {
            return exec::new_usage_error("LOCATE expects arguments separated by a comma");
        }
        debug_assert!(column_arg.1 == ArgSep::End);

        let row = match &row_arg.0 {
            Some(arg) => match arg.eval(machine.get_vars())? {
                Value::Integer(i) => {
                    if i < 0 {
                        return exec::new_usage_error("Row cannot be negative");
                    }
                    i as usize
                }
                _ => return exec::new_usage_error("Row must be an integer"),
            },
            None => return exec::new_usage_error("Row cannot be empty"),
        };

        let column = match &column_arg.0 {
            Some(arg) => match arg.eval(machine.get_vars())? {
                Value::Integer(i) => {
                    if i < 0 {
                        return exec::new_usage_error("Column cannot be negative");
                    }
                    i as usize
                }
                _ => return exec::new_usage_error("Column must be an integer"),
            },
            None => return exec::new_usage_error("Column cannot be empty"),
        };

        self.console.borrow_mut().locate(Position { row, column })?;
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

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        machine: &mut Machine,
    ) -> exec::Result<()> {
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
    use std::collections::VecDeque;
    use std::io;

    /// A captured command or messages sent to the mock console.
    #[derive(Debug, Eq, PartialEq)]
    pub(crate) enum CapturedOut {
        Clear(ClearType),
        Color(Option<u8>, Option<u8>),
        HideCursor,
        Locate(Position),
        MoveWithinLine(i16),
        Print(String),
        ShowCursor,
        Write(Vec<u8>),
    }

    /// A console that supplies golden input and captures all output.
    pub(crate) struct MockConsole {
        /// Sequence of keys to yield on `read_key` calls.
        golden_in: VecDeque<Key>,

        /// Sequence of all messages printed.
        captured_out: Vec<CapturedOut>,
    }

    impl MockConsole {
        /// Creates a new mock console with the given golden input.
        pub(crate) fn new(golden_in: &'static str) -> Self {
            let mut keys = VecDeque::new();
            for ch in golden_in.chars() {
                match ch {
                    '\n' => keys.push_back(Key::NewLine),
                    '\r' => keys.push_back(Key::CarriageReturn),
                    ch => keys.push_back(Key::Char(ch)),
                }
            }
            Self { golden_in: keys, captured_out: vec![] }
        }

        /// Creates a new mock console with the given golden input.
        pub(crate) fn new_raw(keys: &[Key]) -> Self {
            Self { golden_in: VecDeque::from(keys.to_vec()), captured_out: vec![] }
        }

        /// Obtains a reference to the captured output.
        pub(crate) fn captured_out(&self) -> &[CapturedOut] {
            self.captured_out.as_slice()
        }
    }

    impl Drop for MockConsole {
        fn drop(&mut self) {
            assert!(
                self.golden_in.is_empty(),
                "Not all golden input chars were consumed; {} left",
                self.golden_in.len()
            );
        }
    }

    #[async_trait(?Send)]
    impl Console for MockConsole {
        fn clear(&mut self, how: ClearType) -> io::Result<()> {
            self.captured_out.push(CapturedOut::Clear(how));
            Ok(())
        }

        fn color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()> {
            self.captured_out.push(CapturedOut::Color(fg, bg));
            Ok(())
        }

        fn hide_cursor(&mut self) -> io::Result<()> {
            self.captured_out.push(CapturedOut::HideCursor);
            Ok(())
        }

        fn is_interactive(&self) -> bool {
            false
        }

        fn locate(&mut self, pos: Position) -> io::Result<()> {
            self.captured_out.push(CapturedOut::Locate(pos));
            Ok(())
        }

        fn move_within_line(&mut self, off: i16) -> io::Result<()> {
            self.captured_out.push(CapturedOut::MoveWithinLine(off));
            Ok(())
        }

        fn print(&mut self, text: &str) -> io::Result<()> {
            self.captured_out.push(CapturedOut::Print(text.to_owned()));
            Ok(())
        }

        async fn read_key(&mut self) -> io::Result<Key> {
            match self.golden_in.pop_front() {
                Some(ch) => Ok(ch),
                None => Ok(Key::Eof),
            }
        }

        fn show_cursor(&mut self) -> io::Result<()> {
            self.captured_out.push(CapturedOut::ShowCursor);
            Ok(())
        }

        fn size(&self) -> io::Result<Position> {
            // TODO(jmmv): Should probably make the console size configurable by the caller.
            Ok(Position { row: 5, column: 15 })
        }

        fn write(&mut self, bytes: &[u8]) -> io::Result<()> {
            self.captured_out.push(CapturedOut::Write(bytes.to_owned()));
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::testutils::*;
    use super::*;
    use crate::exec::MachineBuilder;
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

    impl ReadLineInteractiveTest {
        /// Constructs a new test that feeds no input to the function, with no prompt or previous
        /// text, and expects an empty return line and no changes to the console.
        fn new() -> Self {
            Self { keys: vec![], prompt: "", previous: "", exp_line: "", exp_output: vec![] }
        }

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

            let mut console = MockConsole::new_raw(&self.keys);
            let line =
                block_on(read_line_interactive(&mut console, self.prompt, self.previous)).unwrap();
            assert_eq!(self.exp_line, &line);
            assert_eq!(self.exp_output.as_slice(), console.captured_out());
        }
    }

    #[test]
    fn test_read_line_interactive_empty() {
        ReadLineInteractiveTest::new().accept();
        ReadLineInteractiveTest::new().add_key(Key::Backspace).accept();
        ReadLineInteractiveTest::new().add_key(Key::ArrowLeft).accept();
        ReadLineInteractiveTest::new().add_key(Key::ArrowRight).accept();
    }

    #[test]
    fn test_read_line_with_prompt() {
        ReadLineInteractiveTest::new()
            .set_prompt("Ready> ")
            .add_output(CapturedOut::Write(b"Ready> ".to_vec()))
            // -
            .add_key_chars("hello")
            .add_output_bytes(b"hello")
            // -
            .set_line("hello")
            .accept();

        ReadLineInteractiveTest::new()
            .set_prompt("Cannot delete")
            .add_output(CapturedOut::Write(b"Cannot delete".to_vec()))
            // -
            .add_key(Key::Backspace)
            .accept();
    }

    #[test]
    fn test_read_line_interactive_trailing_input() {
        ReadLineInteractiveTest::new()
            .add_key_chars("hello")
            .add_output_bytes(b"hello")
            // -
            .set_line("hello")
            .accept();

        ReadLineInteractiveTest::new()
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
        ReadLineInteractiveTest::new()
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
        ReadLineInteractiveTest::new()
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
        ReadLineInteractiveTest::new()
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
        ReadLineInteractiveTest::new()
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
        ReadLineInteractiveTest::new()
            .add_key_chars("1234567890123456789")
            .add_output_bytes(b"12345678901234")
            // -
            .set_line("12345678901234")
            .accept();

        ReadLineInteractiveTest::new()
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

        ReadLineInteractiveTest::new()
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
        ReadLineInteractiveTest::new().add_key(Key::ArrowUp).accept();
        ReadLineInteractiveTest::new().add_key(Key::ArrowDown).accept();
    }

    /// Runs the `input` code on a new machine and verifies its output.
    ///
    /// `golden_in` is a sequence of keys to feed to the commands that request console input.
    ///
    /// `expected_out` is a sequence of expected commands or messages.
    fn do_control_ok_test(input: &str, golden_in: &'static str, expected_out: &[CapturedOut]) {
        let console = Rc::from(RefCell::from(MockConsole::new(golden_in)));
        let mut machine =
            MachineBuilder::default().add_builtins(all_commands(console.clone())).build();
        block_on(machine.exec(&mut input.as_bytes())).expect("Execution failed");
        assert_eq!(expected_out, console.borrow().captured_out());
    }

    /// Same as `do_control_ok_test` but with `expected_out` being just a sequence of expected
    /// `PRINT` calls.
    fn do_ok_test(input: &str, golden_in: &'static str, expected_out: &'static [&'static str]) {
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
        golden_in: &'static str,
        expected_out: &'static [&'static str],
        expected_err: &str,
    ) {
        let console = Rc::from(RefCell::from(MockConsole::new(golden_in)));
        let mut machine =
            MachineBuilder::default().add_builtins(all_commands(console.clone())).build();
        assert_eq!(
            expected_err,
            format!(
                "{}",
                block_on(machine.exec(&mut input.as_bytes())).expect_err("Execution did not fail")
            )
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
        do_error_test(input, "", &[], expected_err);
    }

    #[test]
    fn test_cls_ok() {
        do_control_ok_test("CLS", "", &[CapturedOut::Clear(ClearType::All)]);
    }

    #[test]
    fn test_cls_errors() {
        do_simple_error_test("CLS 1", "CLS takes no arguments");
    }

    #[test]
    fn test_color_ok() {
        do_control_ok_test("COLOR", "", &[CapturedOut::Color(None, None)]);
        do_control_ok_test("COLOR ,", "", &[CapturedOut::Color(None, None)]);
        do_control_ok_test("COLOR 1", "", &[CapturedOut::Color(Some(1), None)]);
        do_control_ok_test("COLOR 1,", "", &[CapturedOut::Color(Some(1), None)]);
        do_control_ok_test("COLOR , 1", "", &[CapturedOut::Color(None, Some(1))]);
        do_control_ok_test("COLOR 10, 5", "", &[CapturedOut::Color(Some(10), Some(5))]);
        do_control_ok_test("COLOR 0, 0", "", &[CapturedOut::Color(Some(0), Some(0))]);
        do_control_ok_test("COLOR 255, 255", "", &[CapturedOut::Color(Some(255), Some(255))]);
    }

    #[test]
    fn test_color_errors() {
        do_simple_error_test(
            "COLOR 1, 2, 3",
            "COLOR takes at most two arguments separated by a comma",
        );

        do_simple_error_test("COLOR 1000, 0", "Color out of range");
        do_simple_error_test("COLOR 0, 1000", "Color out of range");

        do_simple_error_test("COLOR TRUE, 0", "Color must be an integer");
        do_simple_error_test("COLOR 0, TRUE", "Color must be an integer");
    }

    #[test]
    fn test_input_ok() {
        do_ok_test("INPUT ; foo\nPRINT foo", "9\n", &["9"]);
        do_ok_test("INPUT ; foo\nPRINT foo", "-9\n", &["-9"]);
        do_ok_test("INPUT , bar?\nPRINT bar", "true\n", &["TRUE"]);
        do_ok_test("INPUT ; foo$\nPRINT foo", "\n", &[""]);
        do_ok_test(
            "INPUT \"With question mark\"; a$\nPRINT a$",
            "some long text\n",
            &["some long text"],
        );
        do_ok_test(
            "prompt$ = \"Indirectly without question mark\"\nINPUT prompt$, b\nPRINT b * 2",
            "42\n",
            &["84"],
        );
    }

    #[test]
    fn test_input_retry() {
        do_ok_test("INPUT ; b?", "\ntrue\n", &["Retry input: Invalid boolean literal "]);
        do_ok_test("INPUT ; b?", "0\ntrue\n", &["Retry input: Invalid boolean literal 0"]);
        do_ok_test("a = 3\nINPUT ; a", "\n7\n", &["Retry input: Invalid integer literal "]);
        do_ok_test("a = 3\nINPUT ; a", "x\n7\n", &["Retry input: Invalid integer literal x"]);
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
        do_control_ok_test(
            "LOCATE 0, 0",
            "",
            &[CapturedOut::Locate(Position { row: 0, column: 0 })],
        );
        do_control_ok_test(
            "LOCATE 1000, 2000",
            "",
            &[CapturedOut::Locate(Position { row: 1000, column: 2000 })],
        );
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
        do_ok_test("PRINT", "", &[""]);
        do_ok_test("PRINT ;", "", &[" "]);
        do_ok_test("PRINT ,", "", &["\t"]);
        do_ok_test("PRINT ;,;,", "", &[" \t \t"]);

        do_ok_test("PRINT 3", "", &["3"]);
        do_ok_test("PRINT 3 = 5", "", &["FALSE"]);
        do_ok_test("PRINT true;123;\"foo bar\"", "", &["TRUE 123 foo bar"]);
        do_ok_test("PRINT 6,1;3,5", "", &["6\t1 3\t5"]);

        do_ok_test(
            "word = \"foo\"\nPRINT word, word\nPRINT word + \"s\"",
            "",
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
