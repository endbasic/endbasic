// EndBASIC
// Copyright 2024 Julio Merino
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

//! A simple paginator for commands that produce long outputs

use super::{is_narrow, CharsXY, Console, Key};
use std::io;

/// Message to print on a narrow console when the screen is full.
const MORE_MESSAGE_NARROW: &str = " << More >> ";

/// Message to print on a wide console when the screen is full.
const MORE_MESSAGE_WIDE: &str = " << Press any key for more; ESC or Ctrl+C to stop >> ";

/// Wraps a console to offer pagination features.
pub(crate) struct Pager<'a> {
    /// The wrapped console.
    console: &'a mut dyn Console,

    /// Cached size of the console.
    size: CharsXY,

    /// The message to print when the screen is full.
    more_message: &'static str,

    /// Number of columns printed so far on the current line.
    cur_columns: usize,

    /// Number of lines printed so far.
    cur_lines: usize,
}

impl<'a> Pager<'a> {
    /// Wraps `console` to offer pagination features.
    pub(crate) fn new(console: &'a mut dyn Console) -> io::Result<Self> {
        let size = console.size_chars()?;
        let more_message = if is_narrow(console) { MORE_MESSAGE_NARROW } else { MORE_MESSAGE_WIDE };
        Ok(Self { console, size, more_message, cur_columns: 0, cur_lines: 0 })
    }

    /// Returns the maximum number of columns of the console.
    pub(crate) fn columns(&self) -> u16 {
        self.size.x
    }

    /// Gets the console's current foreground and background colors.
    pub(crate) fn color(&self) -> (Option<u8>, Option<u8>) {
        self.console.color()
    }

    /// Sets the console's foreground and background colors to `fg` and `bg`.
    ///
    /// If any of the colors is `None`, the color is left unchanged.
    pub(crate) fn set_color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()> {
        self.console.set_color(fg, bg)
    }

    /// Writes `text` to the console, followed by a newline or CRLF pair depending on the needs of
    /// the console to advance a line.
    ///
    /// The input `text` is not supposed to contain any control characters, such as CR or LF.
    pub(crate) async fn print(&mut self, text: &str) -> io::Result<()> {
        self.console.print(text)?;
        if self.console.is_interactive() {
            self.cur_columns += text.len();
            self.cur_lines += (self.cur_columns / usize::from(self.size.x)) + 1;

            if self.cur_lines >= usize::from(self.size.y) - 1 {
                let previous_color = self.console.color();
                if previous_color != (None, None) {
                    self.console.set_color(None, None)?;
                }
                self.console.print(self.more_message)?;
                if previous_color != (None, None) {
                    self.console.set_color(previous_color.0, previous_color.1)?;
                }
                if matches!(self.console.read_key().await?, Key::Escape | Key::Interrupt) {
                    return Err(io::Error::new(io::ErrorKind::Interrupted, "Interrupted"));
                }

                self.cur_lines = 0;
            }

            self.cur_columns = 0;
        }
        Ok(())
    }

    /// Writes the text into the console at the position of the cursor.
    ///
    pub(crate) fn write(&mut self, text: &str) -> io::Result<()> {
        self.console.write(text)?;
        if self.console.is_interactive() {
            self.cur_columns += text.len();
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;

    #[tokio::test]
    async fn test_no_paging_if_not_interactive() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(CharsXY { x: 10, y: 3 });
        cb.set_interactive(false);

        let mut pager = Pager::new(&mut cb).unwrap();
        pager.print("line 1").await.unwrap();
        pager.print("line 2").await.unwrap();
        pager.print("line 3").await.unwrap();
        pager.print("line 4").await.unwrap();
        pager.print("line 5").await.unwrap();

        assert_eq!(
            [
                CapturedOut::Print("line 1".to_owned()),
                CapturedOut::Print("line 2".to_owned()),
                CapturedOut::Print("line 3".to_owned()),
                CapturedOut::Print("line 4".to_owned()),
                CapturedOut::Print("line 5".to_owned()),
            ],
            cb.captured_out()
        );
    }

    #[tokio::test]
    async fn test_paging_short_columns() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(CharsXY { x: 10, y: 3 });
        cb.set_interactive(true);
        cb.add_input_keys(&[Key::NewLine, Key::Char('a')]);

        let mut pager = Pager::new(&mut cb).unwrap();
        pager.print("line 1").await.unwrap();
        pager.print("line 2").await.unwrap();
        pager.print("line 3").await.unwrap();
        pager.print("line 4").await.unwrap();
        pager.print("line 5").await.unwrap();

        assert_eq!(
            [
                CapturedOut::Print("line 1".to_owned()),
                CapturedOut::Print("line 2".to_owned()),
                CapturedOut::Print(MORE_MESSAGE_NARROW.to_owned()),
                CapturedOut::Print("line 3".to_owned()),
                CapturedOut::Print("line 4".to_owned()),
                CapturedOut::Print(MORE_MESSAGE_NARROW.to_owned()),
                CapturedOut::Print("line 5".to_owned()),
            ],
            cb.captured_out()
        );
    }

    #[tokio::test]
    async fn test_paging_long_columns() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(CharsXY { x: 10, y: 3 });
        cb.set_interactive(true);
        cb.add_input_keys(&[Key::NewLine]);

        let mut pager = Pager::new(&mut cb).unwrap();
        pager.print("this line is long").await.unwrap();
        pager.print("line 2").await.unwrap();

        assert_eq!(
            [
                CapturedOut::Print("this line is long".to_owned()),
                CapturedOut::Print(MORE_MESSAGE_NARROW.to_owned()),
                CapturedOut::Print("line 2".to_owned()),
            ],
            cb.captured_out()
        );
    }

    #[tokio::test]
    async fn test_paging_wide_message() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(CharsXY { x: 60, y: 3 });
        cb.set_interactive(true);
        cb.add_input_keys(&[Key::NewLine]);

        let mut pager = Pager::new(&mut cb).unwrap();
        pager.print("line 1").await.unwrap();
        pager.print("line 2").await.unwrap();
        pager.print("line 3").await.unwrap();

        assert_eq!(
            [
                CapturedOut::Print("line 1".to_owned()),
                CapturedOut::Print("line 2".to_owned()),
                CapturedOut::Print(MORE_MESSAGE_WIDE.to_owned()),
                CapturedOut::Print("line 3".to_owned()),
            ],
            cb.captured_out()
        );
    }

    #[tokio::test]
    async fn test_paging_pause_if_output_is_multiple_of_size() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(CharsXY { x: 10, y: 3 });
        cb.set_interactive(true);
        cb.add_input_keys(&[Key::NewLine, Key::NewLine]);

        let mut pager = Pager::new(&mut cb).unwrap();
        pager.print("line 1").await.unwrap();
        pager.print("line 2").await.unwrap();
        pager.print("line 3").await.unwrap();
        pager.print("line 4").await.unwrap();

        assert_eq!(
            [
                CapturedOut::Print("line 1".to_owned()),
                CapturedOut::Print("line 2".to_owned()),
                CapturedOut::Print(MORE_MESSAGE_NARROW.to_owned()),
                CapturedOut::Print("line 3".to_owned()),
                CapturedOut::Print("line 4".to_owned()),
                // Pausing at the end of the output like this can be considered as not desirable,
                // but this helps ensure that no lines get lost when we print the prompt after a
                // command returns.
                CapturedOut::Print(MORE_MESSAGE_NARROW.to_owned()),
            ],
            cb.captured_out()
        );
    }

    #[tokio::test]
    async fn test_paging_build_long_line_slowly() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(CharsXY { x: 10, y: 3 });
        cb.set_interactive(true);
        cb.add_input_keys(&[Key::NewLine]);

        let mut pager = Pager::new(&mut cb).unwrap();
        pager.write("this line").unwrap();
        pager.print("is long").await.unwrap();
        pager.print("line 2").await.unwrap();

        assert_eq!(
            [
                CapturedOut::Write("this line".to_owned()),
                CapturedOut::Print("is long".to_owned()),
                CapturedOut::Print(MORE_MESSAGE_NARROW.to_owned()),
                CapturedOut::Print("line 2".to_owned()),
            ],
            cb.captured_out()
        );
    }

    #[tokio::test]
    async fn test_paging_use_default_color_for_message() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(CharsXY { x: 10, y: 3 });
        cb.set_interactive(true);
        cb.add_input_keys(&[Key::NewLine]);

        let mut pager = Pager::new(&mut cb).unwrap();
        pager.set_color(Some(3), Some(5)).unwrap();
        pager.print("line 1").await.unwrap();
        pager.print("line 2").await.unwrap();
        pager.print("line 3").await.unwrap();

        assert_eq!(
            [
                CapturedOut::SetColor(Some(3), Some(5)),
                CapturedOut::Print("line 1".to_owned()),
                CapturedOut::Print("line 2".to_owned()),
                CapturedOut::SetColor(None, None),
                CapturedOut::Print(MORE_MESSAGE_NARROW.to_owned()),
                CapturedOut::SetColor(Some(3), Some(5)),
                CapturedOut::Print("line 3".to_owned()),
            ],
            cb.captured_out()
        );
    }

    #[tokio::test]
    async fn test_paging_interrupt() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(CharsXY { x: 60, y: 3 });
        cb.set_interactive(true);
        cb.add_input_keys(&[Key::Escape]);

        let mut pager = Pager::new(&mut cb).unwrap();
        pager.print("line 1").await.unwrap();
        match pager.print("line 2").await {
            Ok(()) => panic!("Should have been interrupted"),
            Err(e) => assert_eq!(io::ErrorKind::Interrupted, e.kind()),
        }

        assert_eq!(
            [
                CapturedOut::Print("line 1".to_owned()),
                CapturedOut::Print("line 2".to_owned()),
                CapturedOut::Print(MORE_MESSAGE_WIDE.to_owned()),
            ],
            cb.captured_out()
        );
    }
}
