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

//! xterm.js-based console implementation.

use crate::input::WebInput;
use async_trait::async_trait;
use endbasic_std::console::{CharsXY, ClearType, Console, Key};
use std::cmp::Ordering;
use std::convert::TryFrom;
use std::io;
use xterm_js_rs::Terminal;

/// Implementation of a console that talks directly to an xterm.js terminal.
pub(crate) struct XtermJsConsole {
    terminal: Terminal,
    input: WebInput,
    alt_active: bool,
}

impl XtermJsConsole {
    pub(crate) fn new(terminal: Terminal, input: WebInput) -> Self {
        Self { terminal, input, alt_active: false }
    }
}

#[async_trait(?Send)]
impl Console for XtermJsConsole {
    fn clear(&mut self, how: ClearType) -> io::Result<()> {
        match how {
            ClearType::All => {
                self.terminal.write("\u{001b}[2J");
                self.terminal.write("\u{001b}[0;0H");
            }
            ClearType::CurrentLine => {
                self.terminal.write("\u{001b}[2K");
            }
            ClearType::PreviousChar => {
                self.terminal.write("\x08 \x08");
            }
            ClearType::UntilNewLine => {
                self.terminal.write("\u{001b}[K");
            }
        }
        Ok(())
    }

    fn color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()> {
        match fg {
            None => self.terminal.write("\u{001b}[39m"),
            Some(color) => self.terminal.write(&format!("\u{001b}[38;5;{}m", color)),
        };
        match bg {
            None => self.terminal.write("\u{001b}[49m"),
            Some(color) => self.terminal.write(&format!("\u{001b}[48;5;{}m", color)),
        };
        self.terminal.write("\u{001b}[0K");
        Ok(())
    }

    fn enter_alt(&mut self) -> io::Result<()> {
        if !self.alt_active {
            self.terminal.write("\u{001b}[?1049h");
            self.alt_active = true;
        }
        Ok(())
    }

    fn hide_cursor(&mut self) -> io::Result<()> {
        self.terminal.write("\u{001b}[?25l");
        Ok(())
    }

    fn is_interactive(&self) -> bool {
        true
    }

    fn leave_alt(&mut self) -> io::Result<()> {
        if self.alt_active {
            self.terminal.write("\u{001b}[?1049l");
            self.alt_active = false;
        }
        Ok(())
    }

    fn locate(&mut self, pos: CharsXY) -> io::Result<()> {
        self.terminal.write(&format!("\u{001b}[{};{}H", pos.y + 1, pos.x + 1));
        Ok(())
    }

    fn move_within_line(&mut self, off: i16) -> io::Result<()> {
        match off.cmp(&0) {
            Ordering::Less => self.terminal.write(&format!("\u{001b}[{}D", -off)),
            Ordering::Equal => (),
            Ordering::Greater => self.terminal.write(&format!("\u{001b}[{}C", off)),
        }
        Ok(())
    }

    fn print(&mut self, text: &str) -> io::Result<()> {
        debug_assert!(!endbasic_std::console::has_control_chars_str(text));

        self.terminal.write(text);
        self.terminal.write("\r\n");
        Ok(())
    }

    async fn poll_key(&mut self) -> io::Result<Option<Key>> {
        self.input.try_recv().await
    }

    async fn read_key(&mut self) -> io::Result<Key> {
        self.input.recv().await
    }

    fn show_cursor(&mut self) -> io::Result<()> {
        self.terminal.write("\u{001b}[?25h");
        Ok(())
    }

    fn size(&self) -> io::Result<CharsXY> {
        Ok(CharsXY::new(
            u16::try_from(self.terminal.get_cols()).unwrap(),
            u16::try_from(self.terminal.get_rows()).unwrap(),
        ))
    }

    fn write(&mut self, bytes: &[u8]) -> io::Result<()> {
        debug_assert!(!endbasic_std::console::has_control_chars_u8(bytes));

        // TODO(jmmv): Should not have to convert to UTF-8 here because it might not be and the
        // terminal should not care (?).
        self.terminal.write(&String::from_utf8_lossy(bytes));
        Ok(())
    }

    fn sync_now(&mut self) -> io::Result<()> {
        Ok(())
    }

    fn set_sync(&mut self, _enabled: bool) -> io::Result<()> {
        Ok(())
    }
}
