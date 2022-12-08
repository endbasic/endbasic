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

//! Crossterm-based console for terminal interaction.

// Keep these in sync with other top-level files.
#![allow(clippy::await_holding_refcell_ref)]
#![allow(clippy::collapsible_else_if)]
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(unused, unused_extern_crates, unused_import_braces, unused_qualifications)]
#![warn(unsafe_code)]

use async_channel::{Receiver, Sender, TryRecvError};
use async_trait::async_trait;
use crossterm::{cursor, event, execute, style, terminal, tty::IsTty, QueueableCommand};
use endbasic_core::exec::Signal;
use endbasic_std::console::{
    get_env_var_as_u16, read_key_from_stdin, remove_control_chars, CharsXY, ClearType, Console, Key,
};
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::io::{self, StdoutLock, Write};

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

/// Implementation of the EndBASIC console to interact with stdin and stdout.
pub struct TerminalConsole {
    /// Whether stdin and stdout are attached to a TTY.  When this is true, the console is put in
    /// raw mode for finer-grained control.
    is_tty: bool,

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

    /// Channel to receive key presses from the terminal.
    on_key_rx: Receiver<Key>,
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
    ///
    /// This spawns a background task to handle console input so this must be run in the context of
    /// an Tokio runtime.
    pub fn from_stdio(signals_tx: Sender<Signal>) -> io::Result<Self> {
        let (on_key_tx, on_key_rx) = async_channel::unbounded();

        let is_tty = io::stdin().is_tty() && io::stdout().is_tty();

        if is_tty {
            terminal::enable_raw_mode().map_err(crossterm_error_to_io_error)?;
            tokio::task::spawn(TerminalConsole::raw_key_handler(on_key_tx, signals_tx));
        } else {
            tokio::task::spawn(TerminalConsole::stdio_key_handler(on_key_tx));
        }

        Ok(Self {
            is_tty,
            fg_color: None,
            bg_color: None,
            cursor_visible: true,
            alt_active: false,
            sync_enabled: true,
            on_key_rx,
        })
    }

    /// Async task to wait for key events on a raw terminal and translate them into events for the
    /// console or the machine.
    async fn raw_key_handler(on_key_tx: Sender<Key>, signals_tx: Sender<Signal>) {
        use event::{KeyCode, KeyModifiers};

        let mut done = false;
        while !done {
            let key = match event::read().map_err(crossterm_error_to_io_error) {
                Ok(event::Event::Key(ev)) => match ev.code {
                    KeyCode::Backspace => Key::Backspace,
                    KeyCode::End => Key::End,
                    KeyCode::Esc => Key::Escape,
                    KeyCode::Home => Key::Home,
                    KeyCode::Tab => Key::Tab,
                    KeyCode::Up => Key::ArrowUp,
                    KeyCode::Down => Key::ArrowDown,
                    KeyCode::Left => Key::ArrowLeft,
                    KeyCode::Right => Key::ArrowRight,
                    KeyCode::PageDown => Key::PageDown,
                    KeyCode::PageUp => Key::PageUp,
                    KeyCode::Char('a') if ev.modifiers == KeyModifiers::CONTROL => Key::Home,
                    KeyCode::Char('b') if ev.modifiers == KeyModifiers::CONTROL => Key::ArrowLeft,
                    KeyCode::Char('c') if ev.modifiers == KeyModifiers::CONTROL => Key::Interrupt,
                    KeyCode::Char('d') if ev.modifiers == KeyModifiers::CONTROL => Key::Eof,
                    KeyCode::Char('e') if ev.modifiers == KeyModifiers::CONTROL => Key::End,
                    KeyCode::Char('f') if ev.modifiers == KeyModifiers::CONTROL => Key::ArrowRight,
                    KeyCode::Char('j') if ev.modifiers == KeyModifiers::CONTROL => Key::NewLine,
                    KeyCode::Char('m') if ev.modifiers == KeyModifiers::CONTROL => Key::NewLine,
                    KeyCode::Char('n') if ev.modifiers == KeyModifiers::CONTROL => Key::ArrowDown,
                    KeyCode::Char('p') if ev.modifiers == KeyModifiers::CONTROL => Key::ArrowUp,
                    KeyCode::Char(ch) => Key::Char(ch),
                    KeyCode::Enter => Key::NewLine,
                    _ => Key::Unknown(format!("{:?}", ev)),
                },
                Ok(_) => {
                    // Not a key event; ignore and try again.
                    continue;
                }
                Err(e) => {
                    // There is not much we can do if we get an error from crossterm.  Try to funnel
                    // the error somehow to the caller so that we can display that something went
                    // wrong... and continue anyhow.
                    Key::Unknown(format!("{:?}", e))
                }
            };

            done = key == Key::Eof;
            if key == Key::Interrupt {
                // Handling CTRL+C in this way isn't great because this is not the same as handling
                // SIGINT on Unix builds.  First, we are unable to stop long-running operations like
                // sleeps; and second, a real SIGINT will kill the interpreter completely instead of
                // coming this way.  We need a real signal handler and we probably should not be
                // running in raw mode all the time.
                signals_tx
                    .send(Signal::Break)
                    .await
                    .expect("Send to unbounded channel should not have failed")
            }

            // This should never fail but can if the receiver outruns the console because we
            // don't await for the handler to terminate (which we cannot do safely because
            // `Drop` is not async).
            let _ = on_key_tx.send(key).await;
        }

        signals_tx.close();
        on_key_tx.close();
    }

    /// Async task to wait for key events on a non-raw terminal and translate them into events for
    /// the console or the machine.
    async fn stdio_key_handler(on_key_tx: Sender<Key>) {
        // TODO(jmmv): We should probably install a signal handler here to capture SIGINT and
        // funnel it to the Machine via signals_rx, as we do in the raw_key_handler.  This would
        // help ensure both consoles behave in the same way, but there is strictly no need for this
        // because, when we do not configure the terminal in raw mode, we aren't capturing CTRL+C
        // and the default system handler will work.

        let mut buffer = VecDeque::default();

        let mut done = false;
        while !done {
            let key = match read_key_from_stdin(&mut buffer) {
                Ok(key) => key,
                Err(e) => {
                    // There is not much we can do if we get an error from stdin.  Try to funnel
                    // the error somehow to the caller so that we can display that something went
                    // wrong... and continue anyhow.
                    Key::Unknown(format!("{:?}", e))
                }
            };

            done = key == Key::Eof;

            // This should never fail but can if the receiver outruns the console because we don't
            // await for the handler to terminate (which we cannot do safely because `Drop` is not
            // async).
            let _ = on_key_tx.send(key).await;
        }

        on_key_tx.close();
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

    fn color(&self) -> (Option<u8>, Option<u8>) {
        (self.fg_color, self.bg_color)
    }

    fn set_color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()> {
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
        let text = remove_control_chars(text.to_owned());

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
        match self.on_key_rx.try_recv() {
            Ok(k) => Ok(Some(k)),
            Err(TryRecvError::Empty) => Ok(None),
            Err(TryRecvError::Closed) => Ok(Some(Key::Eof)),
        }
    }

    async fn read_key(&mut self) -> io::Result<Key> {
        match self.on_key_rx.recv().await {
            Ok(k) => Ok(k),
            Err(_) => Ok(Key::Eof),
        }
    }

    fn show_cursor(&mut self) -> io::Result<()> {
        if !self.cursor_visible {
            execute!(io::stdout(), cursor::Show).map_err(crossterm_error_to_io_error)?;
            self.cursor_visible = true;
        }
        Ok(())
    }

    fn size_chars(&self) -> io::Result<CharsXY> {
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

    fn write(&mut self, text: &str) -> io::Result<()> {
        let text = remove_control_chars(text.to_owned());

        let stdout = io::stdout();
        let mut stdout = stdout.lock();
        stdout.write_all(text.as_bytes())?;
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
