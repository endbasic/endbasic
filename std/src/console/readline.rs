// EndBASIC
// Copyright 2021 Julio Merino
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

//! Interactive line reader.

use crate::console::{Console, Key, LineBuffer};
use std::borrow::Cow;
use std::io;

/// Character to print when typing a secure string.
const SECURE_CHAR: &str = "*";

/// Adjusts the viewport start to ensure `pos` is visible within `width` columns.
fn adjust_view(pos: usize, view_start: usize, width: usize) -> usize {
    if width == 0 {
        0
    } else if pos < view_start {
        pos
    } else if pos > view_start + width {
        pos - width
    } else {
        view_start
    }
}

/// Erases the character at `remove_pos` and redraws the remainder of the line.
fn erase_at(
    console: &mut dyn Console,
    cursor_pos: usize,
    remove_pos: usize,
    line: &mut LineBuffer,
    echo: bool,
) -> io::Result<()> {
    debug_assert!(remove_pos < line.len());
    debug_assert!(remove_pos <= cursor_pos);

    console.hide_cursor()?;
    let delta = cursor_pos - remove_pos;
    if delta > 0 {
        console.move_within_line(-(delta as i16))?;
    }
    let tail_len = line.len() - remove_pos - 1;
    if echo {
        console.write(&line.end(remove_pos + 1))?;
    } else {
        console.write(&SECURE_CHAR.repeat(tail_len))?;
    }
    console.write(" ")?;
    console.move_within_line(-((tail_len + 1) as i16))?;
    console.show_cursor()?;
    line.remove(remove_pos);
    Ok(())
}

/// Returns the text to render for the current viewport.
fn render_line(line: &LineBuffer, view_start: usize, width: usize, echo: bool) -> String {
    debug_assert!(view_start <= line.len());

    if !echo {
        SECURE_CHAR.repeat((line.len() - view_start).min(width))
    } else {
        line.range(view_start, view_start + width)
    }
}

/// Refreshes the current input line to display `text` assuming that the cursor is currently
/// offset by `old_pos` characters from the beginning of the rendered text, that the previous line
/// was `clear_len` characters long, and that the cursor should end at `new_pos`.
fn redraw_line(
    console: &mut dyn Console,
    old_pos: usize,
    clear_len: usize,
    new_pos: usize,
    text: &str,
) -> io::Result<()> {
    console.hide_cursor()?;
    if old_pos > 0 {
        console.move_within_line(-(old_pos as i16))?;
    }
    if !text.is_empty() {
        console.write(text)?;
    }
    let text_len = text.chars().count();
    let written_len = text_len.max(clear_len);
    if text_len < clear_len {
        let diff = clear_len - text_len;
        console.write(&" ".repeat(diff))?;
    }
    debug_assert!(new_pos <= written_len);
    let reset = written_len - new_pos;
    if reset > 0 {
        console.move_within_line(-(reset as i16))?;
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
    let console_width = {
        let console_size = console.size_chars()?;
        usize::from(console_size.x)
    };

    let mut prompt = Cow::from(prompt);
    let mut prompt_len = prompt.len();
    if prompt_len >= console_width {
        // TODO(jmmv): This slices by bytes and can split non-ASCII prompts.
        if console_width >= 5 {
            prompt = Cow::from(format!("{}...", &prompt[0..console_width - 5]));
        } else {
            prompt = Cow::from("");
        }
        prompt_len = prompt.len();
    }

    let mut line = LineBuffer::from(previous);
    let width = {
        // Assumes that the prompt was printed at column 0.  If that was not the case, line length
        // calculation does not work.
        console_width - prompt_len
    };
    let input_width = width.saturating_sub(1);

    // Insertion position *within* the line, without accounting for the prompt.
    // TODO(zenria): Handle UTF-8 graphemes.
    let mut pos = line.len();
    let render = |line: &LineBuffer, pos: usize, view_start: usize| {
        let view_start = adjust_view(pos, view_start, input_width);
        let rendered = render_line(line, view_start, input_width, echo);
        let rendered_len = rendered.chars().count();
        (view_start, rendered, rendered_len)
    };
    let mut view_start = if input_width == 0 { 0 } else { pos.saturating_sub(input_width) };
    let (new_view_start, mut rendered, mut rendered_len) = render(&line, pos, view_start);
    view_start = new_view_start;

    if !prompt.is_empty() || !rendered.is_empty() {
        console.write(&format!("{}{}", prompt, rendered))?;
        console.sync_now()?;
    }

    let mut history_pos = match history.as_mut() {
        Some(history) => {
            history.push(line.to_string());
            history.len() - 1
        }
        None => 0,
    };

    loop {
        match console.read_key().await? {
            Key::ArrowUp => {
                if let Some(history) = history.as_mut() {
                    if history_pos == 0 {
                        continue;
                    }

                    let old_pos = pos - view_start;
                    let clear_len = rendered_len;

                    history[history_pos] = line.into_inner();
                    history_pos -= 1;
                    line = LineBuffer::from(&history[history_pos]);
                    pos = line.len();
                    view_start = if input_width == 0 { 0 } else { pos.saturating_sub(input_width) };
                    (view_start, rendered, rendered_len) = render(&line, pos, view_start);
                    redraw_line(console, old_pos, clear_len, pos - view_start, &rendered)?;
                }
            }

            Key::ArrowDown => {
                if let Some(history) = history.as_mut() {
                    if history_pos == history.len() - 1 {
                        continue;
                    }

                    let old_pos = pos - view_start;
                    let clear_len = rendered_len;

                    history[history_pos] = line.to_string();
                    history_pos += 1;
                    line = LineBuffer::from(&history[history_pos]);
                    pos = line.len();
                    view_start = if input_width == 0 { 0 } else { pos.saturating_sub(input_width) };
                    (view_start, rendered, rendered_len) = render(&line, pos, view_start);
                    redraw_line(console, old_pos, clear_len, pos - view_start, &rendered)?;
                }
            }

            Key::ArrowLeft => {
                if pos > 0 {
                    let old_pos = pos - view_start;
                    pos -= 1;
                    let new_view_start = adjust_view(pos, view_start, input_width);
                    if new_view_start == view_start {
                        console.move_within_line(-1)?;
                    } else {
                        let clear_len = rendered_len;
                        view_start = new_view_start;
                        rendered = render_line(&line, view_start, input_width, echo);
                        rendered_len = rendered.chars().count();
                        redraw_line(console, old_pos, clear_len, pos - view_start, &rendered)?;
                    }
                }
            }

            Key::ArrowRight => {
                if pos < line.len() {
                    let old_pos = pos - view_start;
                    pos += 1;
                    let new_view_start = adjust_view(pos, view_start, input_width);
                    if new_view_start == view_start {
                        console.move_within_line(1)?;
                    } else {
                        let clear_len = rendered_len;
                        view_start = new_view_start;
                        rendered = render_line(&line, view_start, input_width, echo);
                        rendered_len = rendered.chars().count();
                        redraw_line(console, old_pos, clear_len, pos - view_start, &rendered)?;
                    }
                }
            }

            Key::Backspace => {
                if pos > 0 {
                    if view_start == 0 && line.len() <= input_width {
                        erase_at(console, pos, pos - 1, &mut line, echo)?;
                        pos -= 1;
                        rendered_len -= 1;
                    } else {
                        let old_pos = pos - view_start;
                        let clear_len = rendered_len;
                        line.remove(pos - 1);
                        pos -= 1;
                        (view_start, rendered, rendered_len) = render(&line, pos, view_start);
                        redraw_line(console, old_pos, clear_len, pos - view_start, &rendered)?;
                    }
                }
            }

            Key::Delete => {
                if pos < line.len() {
                    if view_start == 0 && line.len() <= input_width {
                        erase_at(console, pos, pos, &mut line, echo)?;
                        rendered_len -= 1;
                    } else {
                        let old_pos = pos - view_start;
                        let clear_len = rendered_len;
                        line.remove(pos);
                        (view_start, rendered, rendered_len) = render(&line, pos, view_start);
                        redraw_line(console, old_pos, clear_len, pos - view_start, &rendered)?;
                    }
                }
            }

            Key::EofOrDelete if !line.is_empty() => {
                if pos < line.len() {
                    if view_start == 0 && line.len() <= input_width {
                        erase_at(console, pos, pos, &mut line, echo)?;
                        rendered_len -= 1;
                    } else {
                        let old_pos = pos - view_start;
                        let clear_len = rendered_len;
                        line.remove(pos);
                        (view_start, rendered, rendered_len) = render(&line, pos, view_start);
                        redraw_line(console, old_pos, clear_len, pos - view_start, &rendered)?;
                    }
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
                if input_width == 0 {
                    continue;
                }

                let line_len = line.len();
                let new_view_start = adjust_view(pos + 1, view_start, input_width);
                if new_view_start == view_start && line_len < input_width {
                    if pos < line_len {
                        console.hide_cursor()?;
                        if echo {
                            let mut buf = [0u8; 4];
                            console.write(ch.encode_utf8(&mut buf))?;
                            console.write(&line.end(pos))?;
                        } else {
                            console.write(&SECURE_CHAR.repeat(line_len - pos + 1))?;
                        }
                        console.move_within_line(-((line_len - pos) as i16))?;
                        console.show_cursor()?;
                        line.insert(pos, ch);
                    } else {
                        if echo {
                            let mut buf = [0u8; 4];
                            console.write(ch.encode_utf8(&mut buf))?;
                        } else {
                            console.write(SECURE_CHAR)?;
                        }
                        line.insert(line_len, ch);
                    }
                    pos += 1;
                    rendered_len += 1;
                } else {
                    let old_pos = pos - view_start;
                    let clear_len = rendered_len;
                    line.insert(pos, ch);
                    pos += 1;
                    view_start = new_view_start;
                    rendered = render_line(&line, view_start, input_width, echo);
                    rendered_len = rendered.chars().count();
                    redraw_line(console, old_pos, clear_len, pos - view_start, &rendered)?;
                }
            }

            Key::End => {
                let offset = line.len() - pos;
                if offset > 0 {
                    let old_pos = pos - view_start;
                    pos += offset;
                    let new_view_start = adjust_view(pos, view_start, input_width);
                    if new_view_start == view_start {
                        console.move_within_line(offset as i16)?;
                    } else {
                        let clear_len = rendered_len;
                        view_start = new_view_start;
                        rendered = render_line(&line, view_start, input_width, echo);
                        rendered_len = rendered.chars().count();
                        redraw_line(console, old_pos, clear_len, pos - view_start, &rendered)?;
                    }
                }
            }

            Key::EofOrDelete => return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "EOF")),

            Key::Escape => {
                // Intentionally ignored.
            }

            Key::Home => {
                if pos > 0 {
                    let old_pos = pos - view_start;
                    pos = 0;
                    let new_view_start = adjust_view(pos, view_start, input_width);
                    if new_view_start == view_start {
                        console.move_within_line(-(old_pos as i16))?;
                    } else {
                        let clear_len = rendered_len;
                        view_start = new_view_start;
                        rendered = render_line(&line, view_start, input_width, echo);
                        rendered_len = rendered.chars().count();
                        redraw_line(console, old_pos, clear_len, 0, &rendered)?;
                    }
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
            Key::Unknown => (),
        }
    }

    if let Some(history) = history.as_mut() {
        if line.is_empty() {
            history.pop();
        } else {
            let last = history.len() - 1;
            history[last] = line.to_string();
        }
    }
    Ok(line.into_inner())
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
            Key::Delete => (),
            Key::End | Key::Home => (),
            Key::Escape => (),
            Key::EofOrDelete => return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "EOF")),
            Key::Interrupt => return Err(io::Error::new(io::ErrorKind::Interrupted, "Ctrl+C")),
            Key::NewLine => break,
            Key::PageDown | Key::PageUp => (),
            Key::Tab => (),
            Key::Unknown => line.push('?'),
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
pub async fn read_line_secure(console: &mut dyn Console, prompt: &str) -> io::Result<String> {
    if !console.is_interactive() {
        return Err(io::Error::other("Cannot read secure strings from a raw console".to_owned()));
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
        size_chars: CharsXY,
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
                size_chars: CharsXY::new(15, 5),
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
        fn add_output_bytes(mut self, bytes: &'static str) -> Self {
            if bytes.is_empty() {
                self.exp_output.push(CapturedOut::Write("".to_string()))
            } else {
                for b in bytes.chars() {
                    let mut buf = [0u8; 4];
                    self.exp_output.push(CapturedOut::Write(b.encode_utf8(&mut buf).to_string()));
                }
            }
            self
        }

        /// Sets the size of the console.
        fn set_size_chars(mut self, size: CharsXY) -> Self {
            self.size_chars = size;
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
            console.set_size_chars(self.size_chars);
            let line = block_on(read_line_interactive(
                &mut console,
                self.prompt,
                self.previous,
                self.history.as_mut(),
                self.echo,
            ))
            .unwrap();
            assert_eq!(self.exp_line, &line);
            assert_eq!(self.exp_output.as_slice(), console.captured_out());
            assert_eq!(self.exp_history, self.history);
        }

        /// Executes the test and expects the given error kind.
        fn expect_err(mut self, exp_kind: io::ErrorKind) {
            let mut console = MockConsole::default();
            console.add_input_keys(&self.keys);
            console.set_size_chars(self.size_chars);
            let err = block_on(read_line_interactive(
                &mut console,
                self.prompt,
                self.previous,
                self.history.as_mut(),
                self.echo,
            ))
            .expect_err("read_line_interactive should fail");
            assert_eq!(exp_kind, err.kind());
            assert_eq!(self.exp_output.as_slice(), console.captured_out());
            assert_eq!(self.exp_history, self.history);
        }
    }

    #[test]
    fn test_read_line_interactive_empty() {
        ReadLineInteractiveTest::default().accept();
        ReadLineInteractiveTest::default().add_key(Key::Backspace).accept();
        ReadLineInteractiveTest::default().add_key(Key::Delete).accept();
        ReadLineInteractiveTest::default()
            .add_key(Key::EofOrDelete)
            .expect_err(io::ErrorKind::UnexpectedEof);
        ReadLineInteractiveTest::default().add_key(Key::ArrowLeft).accept();
        ReadLineInteractiveTest::default().add_key(Key::ArrowRight).accept();
    }

    #[test]
    fn test_read_line_with_prompt() {
        ReadLineInteractiveTest::default()
            .set_prompt("Ready> ")
            .add_output(CapturedOut::Write("Ready> ".to_string()))
            .add_output(CapturedOut::SyncNow)
            // -
            .add_key_chars("hello")
            .add_output_bytes("hello")
            // -
            .set_line("hello")
            .accept();

        ReadLineInteractiveTest::default()
            .set_prompt("Cannot delete")
            .add_output(CapturedOut::Write("Cannot delete".to_string()))
            .add_output(CapturedOut::SyncNow)
            // -
            .add_key(Key::Backspace)
            .accept();
    }

    #[test]
    fn test_read_line_with_prompt_larger_than_screen() {
        ReadLineInteractiveTest::default()
            .set_size_chars(CharsXY::new(15, 5))
            .set_prompt("This is larger than the screen> ")
            .add_output(CapturedOut::Write("This is la...".to_string()))
            .add_output(CapturedOut::SyncNow)
            // -
            .add_key_chars("hello")
            .add_output_bytes("h")
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::Write("e".to_string()))
            .add_output(CapturedOut::ShowCursor)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::Write("l".to_string()))
            .add_output(CapturedOut::ShowCursor)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::Write("l".to_string()))
            .add_output(CapturedOut::ShowCursor)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::Write("o".to_string()))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("hello")
            .accept();
    }

    #[test]
    fn test_read_line_with_prompt_equal_to_screen() {
        ReadLineInteractiveTest::default()
            .set_size_chars(CharsXY::new(10, 5))
            .set_prompt("0123456789")
            .add_output(CapturedOut::Write("01234...".to_string()))
            .add_output(CapturedOut::SyncNow)
            // -
            .add_key_chars("hello")
            .add_output_bytes("h")
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::Write("e".to_string()))
            .add_output(CapturedOut::ShowCursor)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::Write("l".to_string()))
            .add_output(CapturedOut::ShowCursor)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::Write("l".to_string()))
            .add_output(CapturedOut::ShowCursor)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::Write("o".to_string()))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("hello")
            .accept();
    }

    #[test]
    fn test_read_line_with_prompt_larger_than_tiny_screen() {
        ReadLineInteractiveTest::default()
            .set_size_chars(CharsXY::new(3, 5))
            .set_prompt("This is larger than the screen> ")
            // -
            .add_key_chars("hello")
            .add_output_bytes("he")
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-2))
            .add_output(CapturedOut::Write("el".to_string()))
            .add_output(CapturedOut::ShowCursor)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-2))
            .add_output(CapturedOut::Write("ll".to_string()))
            .add_output(CapturedOut::ShowCursor)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-2))
            .add_output(CapturedOut::Write("lo".to_string()))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("hello")
            .accept();
    }

    #[test]
    fn test_read_line_with_prompt_shorter_than_tiny_screen() {
        ReadLineInteractiveTest::default()
            .set_size_chars(CharsXY::new(3, 5))
            .set_prompt("?")
            .add_output(CapturedOut::Write("?".to_string()))
            .add_output(CapturedOut::SyncNow)
            // -
            .add_key_chars("hello")
            .add_output_bytes("h")
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::Write("e".to_string()))
            .add_output(CapturedOut::ShowCursor)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::Write("l".to_string()))
            .add_output(CapturedOut::ShowCursor)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::Write("l".to_string()))
            .add_output(CapturedOut::ShowCursor)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::Write("o".to_string()))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("hello")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_trailing_input() {
        ReadLineInteractiveTest::default()
            .add_key_chars("hello")
            .add_output_bytes("hello")
            // -
            .set_line("hello")
            .accept();

        ReadLineInteractiveTest::default()
            .set_previous("123")
            .add_output(CapturedOut::Write("123".to_string()))
            .add_output(CapturedOut::SyncNow)
            // -
            .add_key_chars("hello")
            .add_output_bytes("hello")
            // -
            .set_line("123hello")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_middle_input() {
        ReadLineInteractiveTest::default()
            .add_key_chars("some text")
            .add_output_bytes("some text")
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
            .add_output_bytes(" ")
            .add_output(CapturedOut::Write("xt".to_string()))
            .add_output(CapturedOut::MoveWithinLine(-2))
            .add_output(CapturedOut::ShowCursor)
            // -
            .add_key_chars(".")
            .add_output(CapturedOut::HideCursor)
            .add_output_bytes(".")
            .add_output(CapturedOut::Write("xt".to_string()))
            .add_output(CapturedOut::MoveWithinLine(-2))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("some te .xt")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_utf8_basic() {
        ReadLineInteractiveTest::default()
            .add_key_chars("é")
            .add_output(CapturedOut::Write("é".to_string()))
            // -
            .set_line("é")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_utf8_remove_2byte_char() {
        ReadLineInteractiveTest::default()
            .add_key_chars("é")
            .add_output(CapturedOut::Write("é".to_string()))
            // -
            .add_key(Key::Backspace)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output_bytes("")
            .add_output_bytes(" ")
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_utf8_add_and_remove_last() {
        ReadLineInteractiveTest::default()
            .add_key_chars("àé")
            .add_output(CapturedOut::Write("à".to_string()))
            .add_output(CapturedOut::Write("é".to_string()))
            // -
            .add_key(Key::Backspace)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output_bytes("")
            .add_output_bytes(" ")
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("à")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_utf8_navigate_2byte_chars() {
        ReadLineInteractiveTest::default()
            .add_key_chars("àé")
            .add_output(CapturedOut::Write("à".to_string()))
            .add_output(CapturedOut::Write("é".to_string()))
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::ArrowLeft)
            // -
            .add_key(Key::ArrowRight)
            .add_output(CapturedOut::MoveWithinLine(1))
            // -
            .add_key(Key::Backspace)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::Write("é".to_string()))
            .add_output_bytes(" ")
            .add_output(CapturedOut::MoveWithinLine(-2))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("é")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_trailing_backspace() {
        ReadLineInteractiveTest::default()
            .add_key_chars("bar")
            .add_output_bytes("bar")
            // -
            .add_key(Key::Backspace)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output_bytes("")
            .add_output_bytes(" ")
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::ShowCursor)
            // -
            .add_key_chars("zar")
            .add_output_bytes("zar")
            // -
            .set_line("bazar")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_middle_backspace() {
        ReadLineInteractiveTest::default()
            .add_key_chars("has a tYpo")
            .add_output_bytes("has a tYpo")
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
            .add_output(CapturedOut::Write("po".to_string()))
            .add_output_bytes(" ")
            .add_output(CapturedOut::MoveWithinLine(-3))
            .add_output(CapturedOut::ShowCursor)
            // -
            .add_key_chars("y")
            .add_output(CapturedOut::HideCursor)
            .add_output_bytes("y")
            .add_output(CapturedOut::Write("po".to_string()))
            .add_output(CapturedOut::MoveWithinLine(-2))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("has a typo")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_middle_delete() {
        ReadLineInteractiveTest::default()
            .add_key_chars("has a typo")
            .add_output_bytes("has a typo")
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::Delete)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::Write("o".to_string()))
            .add_output_bytes(" ")
            .add_output(CapturedOut::MoveWithinLine(-2))
            .add_output(CapturedOut::ShowCursor)
            // -
            .add_key_chars("e")
            .add_output(CapturedOut::HideCursor)
            .add_output_bytes("e")
            .add_output(CapturedOut::Write("o".to_string()))
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("has a tyeo")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_middle_ctrl_d_deletes() {
        ReadLineInteractiveTest::default()
            .add_key_chars("has a typo")
            .add_output_bytes("has a typo")
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::EofOrDelete)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::Write("o".to_string()))
            .add_output_bytes(" ")
            .add_output(CapturedOut::MoveWithinLine(-2))
            .add_output(CapturedOut::ShowCursor)
            // -
            .add_key_chars("e")
            .add_output(CapturedOut::HideCursor)
            .add_output_bytes("e")
            .add_output(CapturedOut::Write("o".to_string()))
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("has a tyeo")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_utf8_delete_2byte_char() {
        ReadLineInteractiveTest::default()
            .add_key_chars("àé")
            .add_output(CapturedOut::Write("à".to_string()))
            .add_output(CapturedOut::Write("é".to_string()))
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::Delete)
            .add_output(CapturedOut::HideCursor)
            .add_output_bytes("")
            .add_output_bytes(" ")
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("à")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_delete_at_end_is_ignored() {
        ReadLineInteractiveTest::default()
            .set_previous("sample")
            .add_output(CapturedOut::Write("sample".to_string()))
            .add_output(CapturedOut::SyncNow)
            // -
            .add_key(Key::Delete)
            // -
            .set_line("sample")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_ctrl_d_at_end_is_ignored() {
        ReadLineInteractiveTest::default()
            .set_previous("sample")
            .add_output(CapturedOut::Write("sample".to_string()))
            .add_output(CapturedOut::SyncNow)
            // -
            .add_key(Key::EofOrDelete)
            // -
            .set_line("sample")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_test_move_bounds() {
        ReadLineInteractiveTest::default()
            .set_previous("12")
            .add_output(CapturedOut::Write("12".to_string()))
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
            .add_output_bytes("3")
            // -
            .set_line("123")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_test_home_end() {
        ReadLineInteractiveTest::default()
            .set_previous("sample text")
            .add_output(CapturedOut::Write("sample text".to_string()))
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
            .add_output_bytes(">")
            .add_output(CapturedOut::Write("sample text".to_string()))
            .add_output(CapturedOut::MoveWithinLine(-11))
            .add_output(CapturedOut::ShowCursor)
            // -
            .add_key(Key::End)
            .add_output(CapturedOut::MoveWithinLine(11))
            // -
            .add_key(Key::Char('<'))
            .add_output_bytes("<")
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
            .add_output(CapturedOut::Write("text<".to_string()))
            .add_output_bytes(" ")
            .add_output(CapturedOut::MoveWithinLine(-6))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line(">sampletext<")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_horizontal_scrolling_while_appending() {
        ReadLineInteractiveTest::default()
            .add_key_chars("12345678901234")
            .add_output_bytes("12345678901234")
            // -
            .add_key_chars("5")
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-14))
            .add_output(CapturedOut::Write("23456789012345".to_string()))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("123456789012345")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_horizontal_scrolling_while_navigating() {
        ReadLineInteractiveTest::default()
            .set_size_chars(CharsXY::new(6, 5))
            .set_previous("abcdef")
            .add_output(CapturedOut::Write("bcdef".to_string()))
            .add_output(CapturedOut::SyncNow)
            // -
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
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::Write("abcde".to_string()))
            .add_output(CapturedOut::MoveWithinLine(-5))
            .add_output(CapturedOut::ShowCursor)
            // -
            .add_key(Key::ArrowRight)
            .add_output(CapturedOut::MoveWithinLine(1))
            .add_key(Key::ArrowRight)
            .add_output(CapturedOut::MoveWithinLine(1))
            .add_key(Key::ArrowRight)
            .add_output(CapturedOut::MoveWithinLine(1))
            .add_key(Key::ArrowRight)
            .add_output(CapturedOut::MoveWithinLine(1))
            .add_key(Key::ArrowRight)
            .add_output(CapturedOut::MoveWithinLine(1))
            .add_key(Key::ArrowRight)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-5))
            .add_output(CapturedOut::Write("bcdef".to_string()))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("abcdef")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_horizontal_scrolling_with_prompt_and_previous() {
        ReadLineInteractiveTest::default()
            .set_prompt("12345")
            .set_previous("67890")
            .add_output(CapturedOut::Write("1234567890".to_string()))
            .add_output(CapturedOut::SyncNow)
            // -
            .add_key_chars("1234567890")
            .add_output_bytes("1234")
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-9))
            .add_output(CapturedOut::Write("789012345".to_string()))
            .add_output(CapturedOut::ShowCursor)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-9))
            .add_output(CapturedOut::Write("890123456".to_string()))
            .add_output(CapturedOut::ShowCursor)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-9))
            .add_output(CapturedOut::Write("901234567".to_string()))
            .add_output(CapturedOut::ShowCursor)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-9))
            .add_output(CapturedOut::Write("012345678".to_string()))
            .add_output(CapturedOut::ShowCursor)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-9))
            .add_output(CapturedOut::Write("123456789".to_string()))
            .add_output(CapturedOut::ShowCursor)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-9))
            .add_output(CapturedOut::Write("234567890".to_string()))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("678901234567890")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_horizontal_scrolling_secure() {
        ReadLineInteractiveTest::default()
            .set_size_chars(CharsXY::new(6, 5))
            .set_echo(false)
            .add_key_chars("abcdef")
            .add_output_bytes("*****")
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-5))
            .add_output(CapturedOut::Write("*****".to_string()))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("abcdef")
            .accept();
    }

    #[test]
    fn test_read_line_interactive_horizontal_scrolling_delete() {
        ReadLineInteractiveTest::default()
            .set_size_chars(CharsXY::new(6, 5))
            .set_previous("abcdef")
            .add_output(CapturedOut::Write("bcdef".to_string()))
            .add_output(CapturedOut::SyncNow)
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_key(Key::Delete)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-4))
            .add_output(CapturedOut::Write("bcde".to_string()))
            .add_output(CapturedOut::Write(" ".to_string()))
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("abcde")
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
            .add_output_bytes("foo")
            //
            .add_key(Key::ArrowUp)
            //
            .add_key_chars("bar")
            .add_output_bytes("bar")
            //
            .add_key(Key::ArrowDown)
            //
            .add_key_chars("baz")
            .add_output_bytes("baz")
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
            .add_output(CapturedOut::Write("x".to_string()))
            // -
            .add_key(Key::Backspace)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output_bytes("")
            .add_output_bytes(" ")
            .add_output(CapturedOut::MoveWithinLine(-1))
            .add_output(CapturedOut::ShowCursor)
            // -
            .accept();
    }

    #[test]
    fn test_read_line_interactive_history_navigate_up_down_end_of_line() {
        ReadLineInteractiveTest::default()
            .set_prompt("? ")
            .add_output(CapturedOut::Write("? ".to_string()))
            .add_output(CapturedOut::SyncNow)
            //
            .set_history(
                vec!["first".to_owned(), "long second line".to_owned(), "last".to_owned()],
                vec!["first".to_owned(), "long second line".to_owned(), "last".to_owned()],
            )
            //
            .add_key(Key::ArrowUp)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::Write("last".to_string()))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowUp)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-("last".len() as i16)))
            .add_output(CapturedOut::Write(" second line".to_string()))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowUp)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-(" second line".len() as i16)))
            .add_output(CapturedOut::Write("first".to_string()))
            .add_output(CapturedOut::Write("       ".to_string()))
            .add_output(CapturedOut::MoveWithinLine(-("       ".len() as i16)))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowUp)
            //
            .add_key(Key::ArrowDown)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-("first".len() as i16)))
            .add_output(CapturedOut::Write(" second line".to_string()))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowDown)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-(" second line".len() as i16)))
            .add_output(CapturedOut::Write("last".to_string()))
            .add_output(CapturedOut::Write("        ".to_string()))
            .add_output(CapturedOut::MoveWithinLine(-("        ".len() as i16)))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowDown)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-("last".len() as i16)))
            .add_output(CapturedOut::Write("    ".to_string()))
            .add_output(CapturedOut::MoveWithinLine(-("    ".len() as i16)))
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
            .add_output(CapturedOut::Write("? ".to_string()))
            .add_output(CapturedOut::SyncNow)
            //
            .set_history(
                vec!["a".to_owned(), "long-line".to_owned(), "zzzz".to_owned()],
                vec!["a".to_owned(), "long-line".to_owned(), "zzzz".to_owned()],
            )
            //
            .add_key(Key::ArrowUp)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::Write("zzzz".to_string()))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowUp)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-("zzzz".len() as i16)))
            .add_output(CapturedOut::Write("long-line".to_string()))
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
            .add_output(CapturedOut::MoveWithinLine(-("long-line".len() as i16) + 4))
            .add_output(CapturedOut::Write("a".to_string()))
            .add_output(CapturedOut::Write("        ".to_string()))
            .add_output(CapturedOut::MoveWithinLine(-("        ".len() as i16)))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowUp)
            //
            .add_key(Key::ArrowDown)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-("a".len() as i16)))
            .add_output(CapturedOut::Write("long-line".to_string()))
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
            .add_output(CapturedOut::MoveWithinLine(-("long-line".len() as i16) + 6))
            .add_output(CapturedOut::Write("zzzz".to_string()))
            .add_output(CapturedOut::Write("     ".to_string()))
            .add_output(CapturedOut::MoveWithinLine(-("     ".len() as i16)))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowDown)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-("zzzz".len() as i16)))
            .add_output(CapturedOut::Write("    ".to_string()))
            .add_output(CapturedOut::MoveWithinLine(-("    ".len() as i16)))
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
            .add_output(CapturedOut::Write("? ".to_string()))
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
            .add_output(CapturedOut::Write("third".to_string()))
            .add_output(CapturedOut::ShowCursor)
            //
            .add_key(Key::ArrowUp)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::MoveWithinLine(-5))
            .add_output(CapturedOut::Write("second".to_string()))
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
            .add_output_bytes(" ")
            .add_output(CapturedOut::Write("ond".to_string()))
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
            .add_output_bytes("not ")
            // -
            .add_key(Key::Escape)
            .add_key(Key::PageDown)
            .add_key(Key::PageUp)
            .add_key(Key::Tab)
            // -
            .add_key_chars("affected")
            .add_output_bytes("affected")
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
            .add_output(CapturedOut::Write("> ********".to_string()))
            .add_output(CapturedOut::SyncNow)
            // -
            .add_key_chars("56")
            .add_output_bytes("**")
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
            .add_output(CapturedOut::Write("**".to_string()))
            .add_output_bytes(" ")
            .add_output(CapturedOut::MoveWithinLine(-3))
            .add_output(CapturedOut::ShowCursor)
            // -
            .add_output(CapturedOut::HideCursor)
            .add_key_chars("7")
            .add_output(CapturedOut::Write("***".to_string()))
            .add_output(CapturedOut::MoveWithinLine(-2))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("pass123756")
            .accept();

        ReadLineInteractiveTest::default()
            .set_echo(false)
            .set_prompt("> ")
            .set_previous("pass1234")
            .add_output(CapturedOut::Write("> ********".to_string()))
            .add_output(CapturedOut::SyncNow)
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::ArrowLeft)
            .add_output(CapturedOut::MoveWithinLine(-1))
            // -
            .add_key(Key::Delete)
            .add_output(CapturedOut::HideCursor)
            .add_output(CapturedOut::Write("*".to_string()))
            .add_output_bytes(" ")
            .add_output(CapturedOut::MoveWithinLine(-2))
            .add_output(CapturedOut::ShowCursor)
            // -
            .set_line("pass124")
            .accept();
    }

    #[test]
    fn test_read_line_secure_trivial_test() {
        let mut console = MockConsole::default();
        console.set_interactive(true);
        console.add_input_keys(&[Key::Char('1'), Key::Char('5'), Key::NewLine]);
        console.set_size_chars(CharsXY::new(15, 5));
        let line = block_on(read_line_secure(&mut console, "> ")).unwrap();
        assert_eq!("15", &line);
        assert_eq!(
            &[
                CapturedOut::Write("> ".to_string()),
                CapturedOut::SyncNow,
                CapturedOut::Write("*".to_string()),
                CapturedOut::Write("*".to_string()),
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
