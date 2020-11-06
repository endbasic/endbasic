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

//! Interactive interpreter for the EndBASIC language.

// Keep these in sync with other top-level files.
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(unused, unused_extern_crates, unused_import_braces, unused_qualifications)]
#![warn(unsafe_code)]

mod store;

use async_trait::async_trait;
use crossterm::{cursor, event, execute, style, terminal, tty::IsTty, QueueableCommand};
use endbasic_core::console;
use futures_lite::future::block_on;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::io::{self, Write};
use std::path::Path;
use std::rc::Rc;
use store::FileStore;

//// Converts a `crossterm::ErrorKind` to an `io::Error`.
fn crossterm_error_to_io_error(e: crossterm::ErrorKind) -> io::Error {
    match e {
        crossterm::ErrorKind::IoError(e) => e,
        crossterm::ErrorKind::Utf8Error(e) => {
            io::Error::new(io::ErrorKind::InvalidData, format!("{}", e))
        }
        _ => io::Error::new(io::ErrorKind::Other, format!("{}", e)),
    }
}

/// Implementation of the EndBASIC console to interact with stdin and stdout.
pub struct TextConsole {
    /// Whether stdin and stdout are attached to a TTY.  When this is true, the console is put in
    /// raw mode for finer-grained control.
    is_tty: bool,

    /// Line-oriented buffer to hold input when not operating in raw mode.
    buffer: VecDeque<console::Key>,
}

impl TextConsole {
    /// Creates a new console based on the properties of stdin/stdout.
    pub fn from_stdio() -> io::Result<Self> {
        let is_tty = io::stdin().is_tty() && io::stdout().is_tty();
        if is_tty {
            terminal::enable_raw_mode().map_err(crossterm_error_to_io_error)?;
        }
        Ok(Self { is_tty, buffer: VecDeque::default() })
    }
}

impl Drop for TextConsole {
    fn drop(&mut self) {
        if self.is_tty {
            terminal::disable_raw_mode().unwrap();
        }
    }
}

impl TextConsole {
    /// Converts a line of text read from stdin into a sequence of key presses.
    fn line_to_keys(s: String) -> VecDeque<console::Key> {
        let mut keys = VecDeque::default();
        for ch in s.chars() {
            if ch == '\n' {
                keys.push_back(console::Key::NewLine);
            } else if ch == '\r' {
                keys.push_back(console::Key::CarriageReturn);
            } else if !ch.is_control() {
                keys.push_back(console::Key::Char(ch));
            } else {
                keys.push_back(console::Key::Unknown(format!("{}", ch)));
            }
        }
        keys
    }

    /// Reads a single key from stdin when not attached to a TTY.  Because characters are not
    /// visible to us until a newline is received, this reads complete lines and buffers them in
    /// memory.
    fn read_key_from_stdin(&mut self) -> io::Result<console::Key> {
        if self.buffer.is_empty() {
            let mut line = String::new();
            if io::stdin().read_line(&mut line)? == 0 {
                return Ok(console::Key::Eof);
            }
            self.buffer = TextConsole::line_to_keys(line);
        }
        match self.buffer.pop_front() {
            Some(key) => Ok(key),
            None => Ok(console::Key::Eof),
        }
    }

    /// Reads a single key from the connected TTY.  This assumes the TTY is in raw mode.
    fn read_key_from_tty(&mut self) -> io::Result<console::Key> {
        loop {
            if let event::Event::Key(ev) = event::read().map_err(crossterm_error_to_io_error)? {
                match ev.code {
                    event::KeyCode::Backspace => return Ok(console::Key::Backspace),
                    event::KeyCode::Up => return Ok(console::Key::ArrowUp),
                    event::KeyCode::Down => return Ok(console::Key::ArrowDown),
                    event::KeyCode::Left => return Ok(console::Key::ArrowLeft),
                    event::KeyCode::Right => return Ok(console::Key::ArrowRight),
                    event::KeyCode::Char('c') if ev.modifiers == event::KeyModifiers::CONTROL => {
                        return Ok(console::Key::Interrupt)
                    }
                    event::KeyCode::Char('d') if ev.modifiers == event::KeyModifiers::CONTROL => {
                        return Ok(console::Key::Eof)
                    }
                    event::KeyCode::Char(ch) => return Ok(console::Key::Char(ch)),
                    event::KeyCode::Enter => return Ok(console::Key::NewLine),
                    _ => return Ok(console::Key::Unknown(format!("{:?}", ev))),
                }
            }
        }
    }
}

#[async_trait(?Send)]
impl console::Console for TextConsole {
    fn clear(&mut self, how: console::ClearType) -> io::Result<()> {
        let how = match how {
            console::ClearType::All => terminal::ClearType::All,
            console::ClearType::CurrentLine => terminal::ClearType::CurrentLine,
            console::ClearType::UntilNewLine => terminal::ClearType::UntilNewLine,
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
        Ok(())
    }

    fn hide_cursor(&mut self) -> io::Result<()> {
        execute!(io::stdout(), cursor::Hide).map_err(crossterm_error_to_io_error)
    }

    fn is_interactive(&self) -> bool {
        self.is_tty
    }

    fn locate(&mut self, pos: console::Position) -> io::Result<()> {
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
        if self.is_tty {
            print!("{}\r\n", text);
        } else {
            println!("{}", text);
        }
        Ok(())
    }

    async fn read_key(&mut self) -> io::Result<console::Key> {
        if self.is_tty {
            self.read_key_from_tty()
        } else {
            self.read_key_from_stdin()
        }
    }

    fn show_cursor(&mut self) -> io::Result<()> {
        execute!(io::stdout(), cursor::Show).map_err(crossterm_error_to_io_error)
    }

    fn size(&self) -> io::Result<console::Position> {
        let (cols, rows) = terminal::size().map_err(crossterm_error_to_io_error)?;
        Ok(console::Position { row: rows as usize, column: cols as usize })
    }

    fn write(&mut self, bytes: &[u8]) -> io::Result<()> {
        let stdout = io::stdout();
        let mut stdout = stdout.lock();
        stdout.write_all(bytes)?;
        stdout.flush()
    }
}

/// Enters the interactive interpreter.
///
/// `dir` specifies the directory that the interpreter will use for any commands that manipulate
/// files.
pub fn run_repl_loop(dir: &Path) -> io::Result<i32> {
    let console = Rc::from(RefCell::from(TextConsole::from_stdio()?));
    let store = Rc::from(RefCell::from(FileStore::new(dir)));
    block_on(endbasic_core::repl::run_repl_loop(console, store))
}
