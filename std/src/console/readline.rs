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

//! Interactive line reader.

use crate::console::{Console, Key};
use std::io;

/// Character to print when typing a secure string.
const SECURE_CHAR: u8 = b'*';

/// Refreshes the current input line to display `line` assuming that the cursor is currently
/// offset by `pos` characters from the beginning of the input and that the previous line was
/// `clear_len` characters long.
fn update_line(
    console: &mut dyn Console,
    pos: usize,
    clear_len: usize,
    line: &str,
) -> io::Result<()> {
    console.hide_cursor()?;
    if pos > 0 {
        console.move_within_line(-(pos as i16))?;
    }
    if !line.is_empty() {
        console.write(line.as_bytes())?;
    }
    if line.len() < clear_len {
        let diff = clear_len - line.len();
        console.write(&vec![b' '; diff])?;
        console.move_within_line(-(diff as i16))?;
    }
    console.show_cursor()
}

/// Reads a line of text interactively from the console, using the given `prompt` and pre-filling
/// the input with `previous`.  If `history` is not `None`, then this appends the newly entered line
/// into the history and allows navigating through it.
async fn read_line_interactive(
    console: &mut dyn Console,
    prompt: &str,
    previous: &str,
    mut history: Option<&mut Vec<String>>,
    echo: bool,
) -> io::Result<String> {
    let mut line = String::from(previous);
    if !prompt.is_empty() || !line.is_empty() {
        if echo {
            console.write(format!("{}{}", prompt, line).as_bytes())?;
        } else {
            console.write(format!("{}{}", prompt, "*".repeat(line.len())).as_bytes())?;
        }
        console.sync_now()?;
    }

    let width = {
        // Assumes that the prompt was printed at column 0.  If that was not the case, line length
        // calculation does not work.
        let console_size = console.size()?;
        usize::from(console_size.x) - prompt.len()
    };

    // Insertion position *within* the line, without accounting for the prompt.
    let mut pos = line.len();

    let mut history_pos;
    match history.as_mut() {
        Some(history) => {
            history.push(line.clone());
            history_pos = history.len() - 1;
        }
        None => history_pos = 0,
    }

    loop {
        match console.read_key().await? {
            Key::ArrowUp => {
                if let Some(history) = history.as_mut() {
                    if history_pos == 0 {
                        continue;
                    }

                    let clear_len = line.len();

                    history[history_pos] = line;
                    history_pos -= 1;
                    line = history[history_pos].clone();

                    update_line(console, pos, clear_len, &line)?;

                    pos = line.len();
                }
            }

            Key::ArrowDown => {
                if let Some(history) = history.as_mut() {
                    if history_pos == history.len() - 1 {
                        continue;
                    }

                    let clear_len = line.len();

                    history[history_pos] = line;
                    history_pos += 1;
                    line = history[history_pos].clone();

                    update_line(console, pos, clear_len, &line)?;

                    pos = line.len();
                }
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
                    if echo {
                        console.write(line[pos..].as_bytes())?;
                    } else {
                        console.write(&vec![SECURE_CHAR; line.len() - pos])?;
                    }
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
                    console.print("")?;
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
                    if echo {
                        console.write(&[ch as u8])?;
                        console.write(line[pos..].as_bytes())?;
                    } else {
                        console.write(&vec![SECURE_CHAR; line.len() - pos + 1])?;
                    }
                    console.move_within_line(-((line.len() - pos) as i16))?;
                    console.show_cursor()?;
                } else {
                    if echo {
                        console.write(&[ch as u8])?;
                    } else {
                        console.write(&[SECURE_CHAR])?;
                    }
                }
                line.insert(pos, ch);
                pos += 1;
            }

            Key::End => {
                let offset = line.len() - pos;
                if offset > 0 {
                    console.move_within_line(offset as i16)?;
                    pos += offset;
                }
            }

            Key::Eof => return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "EOF")),

            Key::Escape => {
                // Intentionally ignored.
            }

            Key::Home => {
                if pos > 0 {
                    console.move_within_line(-(pos as i16))?;
                    pos = 0;
                }
            }

            Key::Interrupt => return Err(io::Error::new(io::ErrorKind::Interrupted, "Ctrl+C")),

            Key::NewLine => {
                console.print("")?;
                break;
            }

            Key::PageDown | Key::PageUp => {
                // Intentionally ignored.
            }

            Key::Tab => {
                // TODO(jmmv): Would be nice to have some form of auto-completion.
            }

            // TODO(jmmv): Should do something smarter with unknown keys.
            Key::Unknown(_) => (),
        }
    }

    if let Some(history) = history.as_mut() {
        if line.is_empty() {
            history.pop();
        } else {
            let last = history.len() - 1;
            history[last] = line.clone();
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
            Key::End | Key::Home => (),
            Key::Escape => (),
            Key::Eof => return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "EOF")),
            Key::Interrupt => return Err(io::Error::new(io::ErrorKind::Interrupted, "Ctrl+C")),
            Key::NewLine => break,
            Key::PageDown | Key::PageUp => (),
            Key::Tab => (),
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
    history: Option<&mut Vec<String>>,
) -> io::Result<String> {
    if console.is_interactive() {
        read_line_interactive(console, prompt, previous, history, true).await
    } else {
        read_line_raw(console).await
    }
}

/// Reads a line from the console without echo using the given `prompt`.
///
/// The console must be interactive for this to work, as otherwise we do not have a mechanism to
/// suppress echo.
pub(crate) async fn read_line_secure(
    console: &mut dyn Console,
    prompt: &str,
) -> io::Result<String> {
    if !console.is_interactive() {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "Cannot read secure strings from a raw console".to_owned(),
        ));
    }
    read_line_interactive(console, prompt, "", None, false).await
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::console::CharsXY;
    use crate::testutils::*;
    use futures_lite::future::block_on;

    /// Builder pattern to construct a test for `read_line_interactive`.
    #[must_use]
    struct ReadLineInteractiveTest {
        keys: Vec<Key>,
        prompt: &'static str,
        previous: &'static str,
        history: Option<Vec<String>>,
        echo: bool,
        exp_line: &'static str,
        exp_output: Vec<CapturedOut>,
        exp_history: Option<Vec<String>>,
    }

    impl Default for ReadLineInteractiveTest {
        /// Constructs a new test that feeds no input to the function, with no prompt or previous
        /// text, and expects an empty return line and no changes to the console.
        fn default() -> Self {
            Self {
                keys: vec![],
                prompt: "",
                previous: "",
                history: None,
                echo: true,
                exp_line: "",
                exp_output: vec![],
                exp_history: None,
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

        /// Enables history tracking and sets the history to use for the test as `history` and
        /// expects that `history` matches `exp_history` upon test completion.
        fn set_history(mut self, history: Vec<String>, exp_history: Vec<String>) -> Self {
            self.history = Some(history);
            self.exp_history = Some(exp_history);
            self
        }

        /// Sets whether read_line echoes characters or not.
        fn set_echo(mut self, echo: bool) -> Self {
            self.echo = echo;
            self
        }

        /// Adds a final return key to the golden input, a newline to the expected output, and
        /// executes the test.
        fn accept(mut self) {
            self.keys.push(Key::NewLine);
            self.exp_output.push(CapturedOut::Print("".to_owned()));

            let mut console = MockConsole::default();
            console.add_input_keys(&self.keys);
            console.set_size(CharsXY::new(15, 5));
            let line = match self.history.as_mut() {
                Some(history) => block_on(read_line_interactive(
                    &mut console,
                    self.prompt,
                    self.previous,
                    Some(history),
                    self.echo,
                ))
                .unwrap(),
                None => block_on(read_line_interactive(
                    &mut console,
                    self.prompt,
                    self.previous,
                    None,
                    self.echo,
                ))
                .unwrap(),
            };
            assert_eq!(self.exp_line, &line);
            assert_eq!(self.exp_output.as_slice(), console.captured_out());
            assert_eq!(self.exp_history, self.history);
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
            .add_output(CapturedOut::SyncNow)
            // -
            .add_key_chars("hello")
            .add_output_bytes(b"hello")
            // -
            .set_line("hello")
            .accept();

        ReadLineInteractiveTest::default()
            .set_prompt("Cannot delete")
            .add_output(CapturedOut::Write(b"Cannot delete".to_vec()))
            .add_output(CapturedOut::SyncNow)
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
            .add_output(CapturedOut::SyncNow)
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
            .add_output(CapturedOut::SyncNow)
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
    fn test_read_line_interactive_test_home_end() {
        ReadLineInteractiveTest::default()
            .set_previous("sample text")
            .add_output(CapturedOut::Write(b"sample text".to_vec()))
            .add_output(CapturedOut::SyncNow)
            // -
            .add_key(Key::End)
            // -
            .add_key(Key::Home)
            .add_output(CapturedOut::MoveWithinLine(-11))
            // -
            .add_key(Key::Home)
            // -
            .add_key(Key::Char('>'))
            .add_output(CapturedOut::HideCursor)
            .add_output_bytes(b">")
            .add_output(CapturedOut::Write(b"sample text".to_vec()))
            .add_output(CapturedOut::MoveWithinLine(-11))
            .add_output(CapturedOut::ShowCursor)
            // -
            .add_key(Key::End)
            .add_output(CapturedOut::MoveWithinLine(11))
            // -
            .add_key(Key::Char('<'))
            .add_output_bytes(b"<")
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
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::Backspace)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::Write(b"text<".to_vec()))
            .add_output_bytes(b" ")
            .add_output(CapturedOut::MoveWithinLine(-6))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line(">sampletext<")
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
            .add_output(CapturedOut::SyncNow)
            // -
            .add_key_chars("1234567890")
            .add_output_bytes(b"1234")
            // -
            .set_line("678901234")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_history_not_enabled_by_default() {
        ReadLineInteractiveTest::default().add_key(Key::ArrowUp).accept();
        ReadLineInteractiveTest::default().add_key(Key::ArrowDown).accept();
    }

    #[test]
    fn test_read_line_interactive_history_empty() {
        ReadLineInteractiveTest::default()
            .set_history(vec![], vec!["foobarbaz".to_owned()])
            //
            .add_key_chars("foo")
            .add_output_bytes(b"foo")
            //
            .add_key(Key::ArrowUp)
            //
            .add_key_chars("bar")
            .add_output_bytes(b"bar")
            //
            .add_key(Key::ArrowDown)
            //
            .add_key_chars("baz")
            .add_output_bytes(b"baz")
            //
            .set_line("foobarbaz")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_skips_empty_lines() {
        ReadLineInteractiveTest::default()
            .set_history(vec!["first".to_owned()], vec!["first".to_owned()])
            // -
            .add_key_chars("x")
            .add_output(CapturedOut::Write(b"x".to_vec()))
            // -
            .add_key(Key::Backspace)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output_bytes(b"")
            .add_output_bytes(b" ")
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::ShowCursor)
            // -
            .accept();
    }

    #[test]
    fn test_read_line_interactive_history_navigate_up_down_end_of_line() {
        ReadLineInteractiveTest::default()
            .set_prompt("? ")
            .add_output(CapturedOut::Write(b"? ".to_vec()))
            .add_output(CapturedOut::SyncNow)
            //
            .set_history(
                vec!["first".to_owned(), "long second line".to_owned(), "last".to_owned()],
                vec!["first".to_owned(), "long second line".to_owned(), "last".to_owned()],
            )
            //
            .add_key(Key::ArrowUp)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::Write(b"last".to_vec()))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowUp)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-(b"last".len() as i16)))
            .add_output(CapturedOut::Write(b"long second line".to_vec()))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowUp)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-(b"long second line".len() as i16)))
            .add_output(CapturedOut::Write(b"first".to_vec()))
            .add_output(CapturedOut::Write(b"           ".to_vec()))
            .add_output(CapturedOut::MoveWithinLine(-(b"           ".len() as i16)))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowUp)
            //
            .add_key(Key::ArrowDown)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-(b"first".len() as i16)))
            .add_output(CapturedOut::Write(b"long second line".to_vec()))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowDown)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-(b"long second line".len() as i16)))
            .add_output(CapturedOut::Write(b"last".to_vec()))
            .add_output(CapturedOut::Write(b"            ".to_vec()))
            .add_output(CapturedOut::MoveWithinLine(-(b"            ".len() as i16)))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowDown)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-(b"last".len() as i16)))
            .add_output(CapturedOut::Write(b"    ".to_vec()))
            .add_output(CapturedOut::MoveWithinLine(-(b"    ".len() as i16)))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowDown)
            //
            .accept();
    }

    #[test]
    fn test_read_line_interactive_history_navigate_up_down_middle_of_line() {
        ReadLineInteractiveTest::default()
            .set_prompt("? ")
            .add_output(CapturedOut::Write(b"? ".to_vec()))
            .add_output(CapturedOut::SyncNow)
            //
            .set_history(
                vec!["a".to_owned(), "long-line".to_owned(), "zzzz".to_owned()],
                vec!["a".to_owned(), "long-line".to_owned(), "zzzz".to_owned()],
            )
            //
            .add_key(Key::ArrowUp)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::Write(b"zzzz".to_vec()))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowUp)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-(b"zzzz".len() as i16)))
            .add_output(CapturedOut::Write(b"long-line".to_vec()))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            //
            .add_key(Key::ArrowUp)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-(b"long-line".len() as i16) + 4))
            .add_output(CapturedOut::Write(b"a".to_vec()))
            .add_output(CapturedOut::Write(b"        ".to_vec()))
            .add_output(CapturedOut::MoveWithinLine(-(b"        ".len() as i16)))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowUp)
            //
            .add_key(Key::ArrowDown)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-(b"a".len() as i16)))
            .add_output(CapturedOut::Write(b"long-line".to_vec()))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            //
            .add_key(Key::ArrowDown)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-(b"long-line".len() as i16) + 6))
            .add_output(CapturedOut::Write(b"zzzz".to_vec()))
            .add_output(CapturedOut::Write(b"     ".to_vec()))
            .add_output(CapturedOut::MoveWithinLine(-(b"     ".len() as i16)))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowDown)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-(b"zzzz".len() as i16)))
            .add_output(CapturedOut::Write(b"    ".to_vec()))
            .add_output(CapturedOut::MoveWithinLine(-(b"    ".len() as i16)))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowDown)
            //
            .accept();
    }

    #[test]
    fn test_read_line_interactive_history_navigate_and_edit() {
        ReadLineInteractiveTest::default()
            .set_prompt("? ")
            .add_output(CapturedOut::Write(b"? ".to_vec()))
            .add_output(CapturedOut::SyncNow)
            //
            .set_history(
                vec!["first".to_owned(), "second".to_owned(), "third".to_owned()],
                vec![
                    "first".to_owned(),
                    "second".to_owned(),
                    "third".to_owned(),
                    "sec ond".to_owned(),
                ],
            )
            //
            .add_key(Key::ArrowUp)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::Write(b"third".to_vec()))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowUp)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-5))
            .add_output(CapturedOut::Write(b"second".to_vec()))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key_chars(" ")
            .add_output(CapturedOut::HideCursor)
            .add_output_bytes(b" ")
            .add_output(CapturedOut::Write(b"ond".to_vec()))
            .add_output(CapturedOut::MoveWithinLine(-3))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("sec ond")
            .accept();
    }

    #[test]
    fn test_read_line_ignored_keys() {
        ReadLineInteractiveTest::default()
            .add_key_chars("not ")
            .add_output_bytes(b"not ")
            // -
            .add_key(Key::Escape)
            .add_key(Key::PageDown)
            .add_key(Key::PageUp)
            .add_key(Key::Tab)
            // -
            .add_key_chars("affected")
            .add_output_bytes(b"affected")
            // -
            .set_line("not affected")
            .accept();
    }

    #[test]
    fn test_read_line_without_echo() {
        ReadLineInteractiveTest::default()
            .set_echo(false)
            .set_prompt("> ")
            .set_previous("pass1234")
            .add_output(CapturedOut::Write(b"> ********".to_vec()))
            .add_output(CapturedOut::SyncNow)
            // -
            .add_key_chars("56")
            .add_output_bytes(b"**")
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
            .add_output(CapturedOut::Write(b"**".to_vec()))
            .add_output_bytes(b" ")
            .add_output(CapturedOut::MoveWithinLine(-3))
            .add_output(CapturedOut::ShowCursor)
            // -
            .add_output(CapturedOut::HideCursor)
            .add_key_chars("7")
            .add_output(CapturedOut::Write(b"***".to_vec()))
            .add_output(CapturedOut::MoveWithinLine(-2))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("pass123756")
            .accept();
    }

    #[test]
    fn test_read_line_secure_trivial_test() {
        let mut console = MockConsole::default();
        console.set_interactive(true);
        console.add_input_keys(&[Key::Char('1'), Key::Char('5'), Key::NewLine]);
        console.set_size(CharsXY::new(15, 5));
        let line = block_on(read_line_secure(&mut console, "> ")).unwrap();
        assert_eq!("15", &line);
        assert_eq!(
            &[
                CapturedOut::Write(vec![b'>', b' ']),
                CapturedOut::SyncNow,
                CapturedOut::Write(vec![b'*']),
                CapturedOut::Write(vec![b'*']),
                CapturedOut::Print("".to_owned()),
            ],
            console.captured_out()
        );
    }

    #[test]
    fn test_read_line_secure_unsupported_in_noninteractive_console() {
        let mut console = MockConsole::default();
        let err = block_on(read_line_secure(&mut console, "> ")).unwrap_err();
        assert!(format!("{}", err).contains("Cannot read secure"));
    }
}
