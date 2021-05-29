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

//! Console representation and manipulation.

use crate::console::{ClearType, Console, Key, Position};
use async_trait::async_trait;
use crossterm::{cursor, event, execute, style, terminal, tty::IsTty, QueueableCommand};
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::env;
use std::io::{self, Write};

/// Converts a `crossterm::ErrorKind` to an `io::Error`.
fn crossterm_error_to_io_error(e: crossterm::ErrorKind) -> io::Error {
    match e {
        crossterm::ErrorKind::IoError(e) => e,
        crossterm::ErrorKind::Utf8Error(e) => {
            io::Error::new(io::ErrorKind::InvalidData, format!("{}", e))
        }
        _ => io::Error::new(io::ErrorKind::Other, format!("{}", e)),
    }
}

/// Gets the value of the environment variable `name` and interprets it as a `usize`.  Returns
/// `None` if the variable is not set or if its contents are invalid.
fn get_env_var_as_usize(name: &str) -> Option<usize> {
    match env::var_os(name) {
        Some(value) => {
            value.as_os_str().to_string_lossy().parse::<usize>().map(Some).unwrap_or(None)
        }
        None => None,
    }
}

/// Implementation of the EndBASIC console to interact with stdin and stdout.
pub struct TerminalConsole {
    /// Whether stdin and stdout are attached to a TTY.  When this is true, the console is put in
    /// raw mode for finer-grained control.
    is_tty: bool,

    /// Line-oriented buffer to hold input when not operating in raw mode.
    buffer: VecDeque<Key>,

    /// Whether a background color is active.  If so, we need to flush the contents of every line
    /// we print so that the color applies to the whole line.
    need_line_flush: bool,
}

impl Drop for TerminalConsole {
    fn drop(&mut self) {
        if self.is_tty {
            terminal::disable_raw_mode().unwrap();
        }
    }
}

impl TerminalConsole {
    /// Creates a new console based on the properties of stdin/stdout.
    pub fn from_stdio() -> io::Result<Self> {
        let is_tty = io::stdin().is_tty() && io::stdout().is_tty();
        if is_tty {
            terminal::enable_raw_mode().map_err(crossterm_error_to_io_error)?;
        }
        Ok(Self { is_tty, buffer: VecDeque::default(), need_line_flush: false })
    }

    /// Converts a line of text read from stdin into a sequence of key presses.
    fn line_to_keys(s: String) -> VecDeque<Key> {
        let mut keys = VecDeque::default();
        for ch in s.chars() {
            if ch == '\x1b' {
                keys.push_back(Key::Escape);
            } else if ch == '\n' {
                keys.push_back(Key::NewLine);
            } else if ch == '\r' {
                // Ignore.  When we run under Windows and use golden test input files, we end up
                // seeing two separate characters to terminate a newline (CRLF) and these confuse
                // our tests.  I am not sure why this doesn't seem to be a problem for interactive
                // usage though, but it might just be that crossterm hides this from us.
            } else if !ch.is_control() {
                keys.push_back(Key::Char(ch));
            } else {
                keys.push_back(Key::Unknown(format!("{}", ch)));
            }
        }
        keys
    }

    /// Reads a single key from stdin when not attached to a TTY.  Because characters are not
    /// visible to us until a newline is received, this reads complete lines and buffers them in
    /// memory.
    fn read_key_from_stdin(&mut self) -> io::Result<Key> {
        if self.buffer.is_empty() {
            let mut line = String::new();
            if io::stdin().read_line(&mut line)? == 0 {
                return Ok(Key::Eof);
            }
            self.buffer = TerminalConsole::line_to_keys(line);
        }
        match self.buffer.pop_front() {
            Some(key) => Ok(key),
            None => Ok(Key::Eof),
        }
    }

    /// Reads a single key from the connected TTY.  This assumes the TTY is in raw mode.
    fn read_key_from_tty(&mut self) -> io::Result<Key> {
        loop {
            if let event::Event::Key(ev) = event::read().map_err(crossterm_error_to_io_error)? {
                match ev.code {
                    event::KeyCode::Backspace => return Ok(Key::Backspace),
                    event::KeyCode::Esc => return Ok(Key::Escape),
                    event::KeyCode::Up => return Ok(Key::ArrowUp),
                    event::KeyCode::Down => return Ok(Key::ArrowDown),
                    event::KeyCode::Left => return Ok(Key::ArrowLeft),
                    event::KeyCode::Right => return Ok(Key::ArrowRight),
                    event::KeyCode::Char('c') if ev.modifiers == event::KeyModifiers::CONTROL => {
                        return Ok(Key::Interrupt)
                    }
                    event::KeyCode::Char('d') if ev.modifiers == event::KeyModifiers::CONTROL => {
                        return Ok(Key::Eof)
                    }
                    event::KeyCode::Char('j') if ev.modifiers == event::KeyModifiers::CONTROL => {
                        return Ok(Key::NewLine)
                    }
                    event::KeyCode::Char('m') if ev.modifiers == event::KeyModifiers::CONTROL => {
                        return Ok(Key::NewLine)
                    }
                    event::KeyCode::Char(ch) => return Ok(Key::Char(ch)),
                    event::KeyCode::Enter => return Ok(Key::NewLine),
                    _ => return Ok(Key::Unknown(format!("{:?}", ev))),
                }
            }
        }
    }
}

#[async_trait(?Send)]
impl Console for TerminalConsole {
    fn clear(&mut self, how: ClearType) -> io::Result<()> {
        let how = match how {
            ClearType::All => terminal::ClearType::All,
            ClearType::CurrentLine => terminal::ClearType::CurrentLine,
            ClearType::UntilNewLine => terminal::ClearType::UntilNewLine,
        };
        let mut output = io::stdout();
        output.queue(terminal::Clear(how)).map_err(crossterm_error_to_io_error)?;
        if how == terminal::ClearType::All {
            output.queue(cursor::MoveTo(0, 0)).map_err(crossterm_error_to_io_error)?;
        }
        output.flush()
    }

    fn color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()> {
        let mut output = io::stdout();
        let fg = match fg {
            None => style::Color::Reset,
            Some(color) => style::Color::AnsiValue(color),
        };
        let bg = match bg {
            None => style::Color::Reset,
            Some(color) => style::Color::AnsiValue(color),
        };
        output.queue(style::SetForegroundColor(fg)).map_err(crossterm_error_to_io_error)?;
        output.queue(style::SetBackgroundColor(bg)).map_err(crossterm_error_to_io_error)?;
        output.flush()?;
        self.need_line_flush = bg != style::Color::Reset;
        Ok(())
    }

    fn enter_alt(&mut self) -> io::Result<()> {
        execute!(io::stdout(), terminal::EnterAlternateScreen).map_err(crossterm_error_to_io_error)
    }

    fn hide_cursor(&mut self) -> io::Result<()> {
        execute!(io::stdout(), cursor::Hide).map_err(crossterm_error_to_io_error)
    }

    fn is_interactive(&self) -> bool {
        self.is_tty
    }

    fn leave_alt(&mut self) -> io::Result<()> {
        execute!(io::stdout(), terminal::LeaveAlternateScreen).map_err(crossterm_error_to_io_error)
    }

    fn locate(&mut self, pos: Position) -> io::Result<()> {
        if pos.row > std::u16::MAX as usize {
            return Err(io::Error::new(io::ErrorKind::Other, "Row out of range"));
        }
        let row = pos.row as u16;

        if pos.column > std::u16::MAX as usize {
            return Err(io::Error::new(io::ErrorKind::Other, "Column out of range"));
        }
        let column = pos.column as u16;

        execute!(io::stdout(), cursor::MoveTo(column, row)).map_err(crossterm_error_to_io_error)
    }

    fn move_within_line(&mut self, off: i16) -> io::Result<()> {
        match off.cmp(&0) {
            Ordering::Less => execute!(io::stdout(), cursor::MoveLeft(-off as u16)),
            Ordering::Equal => Ok(()),
            Ordering::Greater => execute!(io::stdout(), cursor::MoveRight(off as u16)),
        }
        .map_err(crossterm_error_to_io_error)
    }

    fn print(&mut self, text: &str) -> io::Result<()> {
        let stdout = io::stdout();
        let mut stdout = stdout.lock();
        stdout.write_all(text.as_bytes())?;
        if self.need_line_flush {
            execute!(stdout, terminal::Clear(terminal::ClearType::UntilNewLine))
                .map_err(crossterm_error_to_io_error)?;
        }
        if self.is_tty {
            stdout.write_all(b"\r\n")?;
        } else {
            stdout.write_all(b"\n")?;
        }
        Ok(())
    }

    async fn read_key(&mut self) -> io::Result<Key> {
        if self.is_tty {
            self.read_key_from_tty()
        } else {
            self.read_key_from_stdin()
        }
    }

    fn show_cursor(&mut self) -> io::Result<()> {
        execute!(io::stdout(), cursor::Show).map_err(crossterm_error_to_io_error)
    }

    fn size(&self) -> io::Result<Position> {
        // Must be careful to not query the terminal size if both LINES and COLUMNS are set, because
        // the query fails when we don't have a PTY and we still need to run under these conditions
        // for testing purposes.
        let lines = get_env_var_as_usize("LINES");
        let columns = get_env_var_as_usize("COLUMNS");
        let size = match (lines, columns) {
            (Some(l), Some(c)) => Position { row: l, column: c },
            (l, c) => {
                let (actual_columns, actual_lines) =
                    terminal::size().map_err(crossterm_error_to_io_error)?;
                Position {
                    row: l.unwrap_or(actual_lines as usize),
                    column: c.unwrap_or(actual_columns as usize),
                }
            }
        };
        Ok(size)
    }

    fn write(&mut self, bytes: &[u8]) -> io::Result<()> {
        let stdout = io::stdout();
        let mut stdout = stdout.lock();
        stdout.write_all(bytes)?;
        stdout.flush()
    }
}
