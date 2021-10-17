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

use crate::console::{CharsXY, ClearType, Console, Key};
use async_trait::async_trait;
use crossterm::{cursor, event, execute, style, terminal, tty::IsTty, QueueableCommand};
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::env;
use std::io::{self, StdoutLock, Write};
use std::time::Duration;

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

/// Gets the value of the environment variable `name` and interprets it as a `u16`.  Returns
/// `None` if the variable is not set or if its contents are invalid.
fn get_env_var_as_u16(name: &str) -> Option<u16> {
    match env::var_os(name) {
        Some(value) => value.as_os_str().to_string_lossy().parse::<u16>().map(Some).unwrap_or(None),
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

    /// Current foreground color.
    fg_color: Option<u8>,

    /// Current background color.
    bg_color: Option<u8>,

    /// Whether the cursor is visible or not.
    cursor_visible: bool,

    /// Whether we are in the alternate console or not.
    alt_active: bool,

    /// Whether video syncing is enabled or not.
    sync_enabled: bool,
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
        Ok(Self {
            is_tty,
            buffer: VecDeque::default(),
            fg_color: None,
            bg_color: None,
            cursor_visible: true,
            alt_active: false,
            sync_enabled: true,
        })
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
    ///
    /// If the next event extracted from the terminal is *not* a key press, returns None.  The
    /// caller should then retry until it gets a key.
    fn try_read_key_from_tty(&mut self) -> io::Result<Option<Key>> {
        let ev = event::read().map_err(crossterm_error_to_io_error)?;
        match ev {
            event::Event::Key(ev) => {
                let key = match ev.code {
                    event::KeyCode::Backspace => Key::Backspace,
                    event::KeyCode::Esc => Key::Escape,
                    event::KeyCode::Up => Key::ArrowUp,
                    event::KeyCode::Down => Key::ArrowDown,
                    event::KeyCode::Left => Key::ArrowLeft,
                    event::KeyCode::Right => Key::ArrowRight,
                    event::KeyCode::Char('c') if ev.modifiers == event::KeyModifiers::CONTROL => {
                        Key::Interrupt
                    }
                    event::KeyCode::Char('d') if ev.modifiers == event::KeyModifiers::CONTROL => {
                        Key::Eof
                    }
                    event::KeyCode::Char('j') if ev.modifiers == event::KeyModifiers::CONTROL => {
                        Key::NewLine
                    }
                    event::KeyCode::Char('m') if ev.modifiers == event::KeyModifiers::CONTROL => {
                        Key::NewLine
                    }
                    event::KeyCode::Char(ch) => Key::Char(ch),
                    event::KeyCode::Enter => Key::NewLine,
                    _ => Key::Unknown(format!("{:?}", ev)),
                };
                Ok(Some(key))
            }
            _ => Ok(None),
        }
    }

    /// Flushes the console, which has already been written to via `lock`, if syncing is enabled.
    fn maybe_flush(&self, mut lock: StdoutLock<'_>) -> io::Result<()> {
        if self.sync_enabled {
            lock.flush()
        } else {
            Ok(())
        }
    }
}

#[async_trait(?Send)]
impl Console for TerminalConsole {
    fn clear(&mut self, how: ClearType) -> io::Result<()> {
        let how = match how {
            ClearType::All => terminal::ClearType::All,
            ClearType::CurrentLine => terminal::ClearType::CurrentLine,
            ClearType::PreviousChar => {
                let stdout = io::stdout();
                let mut stdout = stdout.lock();
                stdout.write_all(b"\x08 \x08")?;
                return self.maybe_flush(stdout);
            }
            ClearType::UntilNewLine => terminal::ClearType::UntilNewLine,
        };
        let stdout = io::stdout();
        let mut stdout = stdout.lock();
        stdout.queue(terminal::Clear(how)).map_err(crossterm_error_to_io_error)?;
        if how == terminal::ClearType::All {
            stdout.queue(cursor::MoveTo(0, 0)).map_err(crossterm_error_to_io_error)?;
        }
        self.maybe_flush(stdout)
    }

    fn color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()> {
        if fg == self.fg_color && bg == self.bg_color {
            return Ok(());
        }

        let stdout = io::stdout();
        let mut stdout = stdout.lock();
        if fg != self.fg_color {
            let ct_fg = match fg {
                None => style::Color::Reset,
                Some(color) => style::Color::AnsiValue(color),
            };
            stdout.queue(style::SetForegroundColor(ct_fg)).map_err(crossterm_error_to_io_error)?;
            self.fg_color = fg;
        }
        if bg != self.bg_color {
            let ct_bg = match bg {
                None => style::Color::Reset,
                Some(color) => style::Color::AnsiValue(color),
            };
            stdout.queue(style::SetBackgroundColor(ct_bg)).map_err(crossterm_error_to_io_error)?;
            self.bg_color = bg;
        }
        self.maybe_flush(stdout)
    }

    fn enter_alt(&mut self) -> io::Result<()> {
        if !self.alt_active {
            execute!(io::stdout(), terminal::EnterAlternateScreen)
                .map_err(crossterm_error_to_io_error)?;
            self.alt_active = true;
        }
        Ok(())
    }

    fn hide_cursor(&mut self) -> io::Result<()> {
        if self.cursor_visible {
            execute!(io::stdout(), cursor::Hide).map_err(crossterm_error_to_io_error)?;
            self.cursor_visible = false;
        }
        Ok(())
    }

    fn is_interactive(&self) -> bool {
        self.is_tty
    }

    fn leave_alt(&mut self) -> io::Result<()> {
        if self.alt_active {
            execute!(io::stdout(), terminal::LeaveAlternateScreen)
                .map_err(crossterm_error_to_io_error)?;
            self.alt_active = false;
        }
        Ok(())
    }

    fn locate(&mut self, pos: CharsXY) -> io::Result<()> {
        execute!(io::stdout(), cursor::MoveTo(pos.x, pos.y)).map_err(crossterm_error_to_io_error)
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
        debug_assert!(!crate::console::has_control_chars_str(text));

        let stdout = io::stdout();
        let mut stdout = stdout.lock();
        stdout.write_all(text.as_bytes())?;
        if self.is_tty {
            stdout.write_all(b"\r\n")?;
        } else {
            stdout.write_all(b"\n")?;
        }
        Ok(())
    }

    async fn poll_key(&mut self) -> io::Result<Option<Key>> {
        if self.is_tty {
            loop {
                if !event::poll(Duration::default()).map_err(crossterm_error_to_io_error)? {
                    return Ok(None);
                }

                let key = self.try_read_key_from_tty()?;
                if key.is_some() {
                    return Ok(key);
                }
                // Non-key event; try again.
            }
        } else {
            Err(io::Error::new(io::ErrorKind::Other, "Cannot poll keys from stdin"))
        }
    }

    async fn read_key(&mut self) -> io::Result<Key> {
        if self.is_tty {
            loop {
                if let Some(key) = self.try_read_key_from_tty()? {
                    return Ok(key);
                }
                // Non-key event; try again.
            }
        } else {
            self.read_key_from_stdin()
        }
    }

    fn show_cursor(&mut self) -> io::Result<()> {
        if !self.cursor_visible {
            execute!(io::stdout(), cursor::Show).map_err(crossterm_error_to_io_error)?;
            self.cursor_visible = true;
        }
        Ok(())
    }

    fn size(&self) -> io::Result<CharsXY> {
        // Must be careful to not query the terminal size if both LINES and COLUMNS are set, because
        // the query fails when we don't have a PTY and we still need to run under these conditions
        // for testing purposes.
        let lines = get_env_var_as_u16("LINES");
        let columns = get_env_var_as_u16("COLUMNS");
        let size = match (lines, columns) {
            (Some(l), Some(c)) => CharsXY::new(c, l),
            (l, c) => {
                let (actual_columns, actual_lines) =
                    terminal::size().map_err(crossterm_error_to_io_error)?;
                CharsXY::new(c.unwrap_or(actual_columns), l.unwrap_or(actual_lines))
            }
        };
        Ok(size)
    }

    fn write(&mut self, bytes: &[u8]) -> io::Result<()> {
        debug_assert!(!crate::console::has_control_chars_u8(bytes));

        let stdout = io::stdout();
        let mut stdout = stdout.lock();
        stdout.write_all(bytes)?;
        self.maybe_flush(stdout)
    }

    fn sync_now(&mut self) -> io::Result<()> {
        if self.sync_enabled {
            Ok(())
        } else {
            io::stdout().flush()
        }
    }

    fn set_sync(&mut self, enabled: bool) -> io::Result<()> {
        if !self.sync_enabled {
            io::stdout().flush()?;
        }
        self.sync_enabled = enabled;
        Ok(())
    }
}
