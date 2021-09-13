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

//! Interactive console-based text editor.

use crate::console::{CharsXY, ClearType, Console, Key};
use crate::program::Program;
use async_trait::async_trait;
use std::cmp;
use std::io;

/// The color of the main editor window.
const TEXT_COLOR: (Option<u8>, Option<u8>) = (Some(15), None);

/// The color of the editor status bar.
const STATUS_COLOR: (Option<u8>, Option<u8>) = (Some(15), Some(4));

/// Returns the indentation of a given string as a new string.
fn copy_indent(line: &str) -> String {
    let mut indent = String::new();
    for ch in line.chars() {
        if !ch.is_whitespace() {
            break;
        }
        indent.push(ch);
    }
    indent
}

/// An interactive console-based text editor.
///
/// The text editor owns the textual contents it is editing.
pub struct Editor {
    /// Owned contents of the file being edited.
    content: Vec<String>,

    /// Position of the top-left character of the file visible in the console.
    viewport_pos: CharsXY,

    /// Insertion position within the file.
    file_pos: CharsXY,

    /// Last edited column, used when moving vertically to preserve the insertion point even when
    /// traversing shorter lines.
    insert_col: usize,
}

impl Default for Editor {
    /// Creates a new editor without any stored contents.
    fn default() -> Self {
        Self {
            content: vec![],
            viewport_pos: CharsXY::default(),
            file_pos: CharsXY::default(),
            insert_col: 0,
        }
    }
}

impl Editor {
    /// Rewrites the status line at the bottom of the `console`, using the previously queried
    /// `console_size`.
    ///
    /// It is the responsibility of the caller to move the cursor back to the appropriate location
    /// after calling this function, and the caller should also hide the cursor before calling this
    /// function.
    fn refresh_status(&self, console: &mut dyn Console, console_size: CharsXY) -> io::Result<()> {
        let keys = " ESC Finish editing ";
        // Even though we track file positions as 0-indexed, display them as 1-indexed for a better
        // user experience given that this is what all other editor seem to do.
        let pos = format!(" | Ln {}, Col {} ", self.file_pos.y + 1, self.file_pos.x + 1);

        let mut status = String::with_capacity(console_size.x);
        status.push_str(keys);
        while status.len() < console_size.x - pos.len() {
            status.push(' ');
        }
        status.push_str(&pos);
        status.truncate(console_size.x);

        console.locate(CharsXY::new(0, console_size.y - 1))?;
        console.color(STATUS_COLOR.0, STATUS_COLOR.1)?;
        console.write(status.as_bytes())?;
        Ok(())
    }

    /// Refreshes the contents of the whole `console`, using the previously queried `console_size`.
    ///
    /// It is the responsibility of the caller to move the cursor back to the appropriate location
    /// after calling this function, and the caller should also hide the cursor before calling this
    /// function.
    fn refresh(&self, console: &mut dyn Console, console_size: CharsXY) -> io::Result<()> {
        console.color(TEXT_COLOR.0, TEXT_COLOR.1)?;
        console.clear(ClearType::All)?;
        self.refresh_status(console, console_size)?;
        console.color(TEXT_COLOR.0, TEXT_COLOR.1)?;
        console.locate(CharsXY::default())?;

        let mut row = self.viewport_pos.y;
        let mut printed_rows = 0;
        while row < self.content.len() && printed_rows < console_size.y - 1 {
            let line = &self.content[row];
            if line.len() >= self.viewport_pos.x {
                let last = cmp::min(line.len(), self.viewport_pos.x + console_size.x);
                let view = &line[self.viewport_pos.x..last];
                console.print(view)?;
            } else {
                console.print("")?;
            }
            row += 1;
            printed_rows += 1;
        }
        Ok(())
    }

    /// Internal implementation of the interactive editor, which interacts with the `console`.
    async fn edit_interactively(&mut self, console: &mut dyn Console) -> io::Result<()> {
        let console_size = console.size()?;

        if self.content.is_empty() {
            self.content.push(String::new());
        }

        let mut need_refresh = true;
        loop {
            // The key handling below only deals with moving the insertion position within the file
            // but does not bother to update the viewport. Adjust it now, if necessary.
            if self.file_pos.y < self.viewport_pos.y {
                self.viewport_pos.y -= 1;
                need_refresh = true;
            } else if self.file_pos.y > self.viewport_pos.y + console_size.y - 2 {
                self.viewport_pos.y += 1;
                need_refresh = true;
            }
            if self.file_pos.x < self.viewport_pos.x {
                self.viewport_pos.x = self.file_pos.x;
                need_refresh = true;
            } else if self.file_pos.x >= self.viewport_pos.x + console_size.x {
                self.viewport_pos.x = self.file_pos.x - console_size.x + 1;
                need_refresh = true;
            }

            console.hide_cursor()?;
            if need_refresh {
                self.refresh(console, console_size)?;
                need_refresh = false;
            } else {
                self.refresh_status(console, console_size)?;
                console.color(TEXT_COLOR.0, TEXT_COLOR.1)?;
            }
            let cursor_pos = self.file_pos - self.viewport_pos;
            console.locate(cursor_pos)?;
            console.show_cursor()?;

            match console.read_key().await? {
                Key::Escape | Key::Eof | Key::Interrupt => break,

                Key::ArrowUp => {
                    if self.file_pos.y > 0 {
                        self.file_pos.y -= 1;
                    }

                    let line = &self.content[self.file_pos.y];
                    self.file_pos.x = cmp::min(self.insert_col, line.len());
                }

                Key::ArrowDown => {
                    if self.file_pos.y < self.content.len() - 1 {
                        self.file_pos.y += 1;
                    }

                    let line = &self.content[self.file_pos.y];
                    self.file_pos.x = cmp::min(self.insert_col, line.len());
                }

                Key::ArrowLeft => {
                    if self.file_pos.x > 0 {
                        self.file_pos.x -= 1;
                        self.insert_col = self.file_pos.x;
                    }
                }

                Key::ArrowRight => {
                    if self.file_pos.x < self.content[self.file_pos.y].len() {
                        self.file_pos.x += 1;
                        self.insert_col = self.file_pos.x;
                    }
                }

                Key::Backspace => {
                    if self.file_pos.x > 0 {
                        let line = &mut self.content[self.file_pos.y];
                        if self.file_pos.x == line.len() {
                            console.clear(ClearType::PreviousChar)?;
                        } else {
                            // TODO(jmmv): Refresh only the affected line.
                            need_refresh = true;
                        }
                        line.remove(self.file_pos.x - 1);
                        self.file_pos.x -= 1;
                    } else if self.file_pos.y > 0 {
                        let line = self.content.remove(self.file_pos.y);
                        let prev = &mut self.content[self.file_pos.y - 1];
                        self.file_pos.x = prev.len();
                        prev.push_str(&line);
                        self.file_pos.y -= 1;
                        need_refresh = true;
                    }
                    self.insert_col = self.file_pos.x;
                }

                Key::Char(ch) => {
                    let mut buf = [0; 4];

                    let line = &mut self.content[self.file_pos.y];
                    if self.file_pos.x + 1 < line.len() {
                        // TODO(jmmv): Refresh only the affected line.
                        need_refresh = true;
                    }
                    line.insert(self.file_pos.x, ch);
                    self.file_pos.x += 1;
                    self.insert_col = self.file_pos.x;

                    if cursor_pos.x < console_size.x - 1 && !need_refresh {
                        console.write(ch.encode_utf8(&mut buf).as_bytes())?;
                    }
                }

                Key::NewLine | Key::CarriageReturn => {
                    let indent = copy_indent(&self.content[self.file_pos.y]);
                    let indent_len = indent.len();
                    if self.file_pos.y < self.content.len() - 1 {
                        let new = self.content[self.file_pos.y].split_off(self.file_pos.x);
                        self.content.insert(self.file_pos.y + 1, indent + &new);
                        need_refresh = true;
                    } else {
                        self.content.insert(self.file_pos.y + 1, indent);
                    }
                    self.file_pos.x = indent_len;
                    self.file_pos.y += 1;
                    self.insert_col = self.file_pos.x;
                }

                // TODO(jmmv): Should do something smarter with unknown keys.
                Key::Unknown(_) => (),
            }
        }

        Ok(())
    }
}

#[async_trait(?Send)]
impl Program for Editor {
    async fn edit(&mut self, console: &mut dyn Console) -> io::Result<()> {
        console.enter_alt()?;
        let result = self.edit_interactively(console).await;
        console.leave_alt()?;
        result
    }

    fn load(&mut self, text: &str) {
        self.content = text.lines().map(|l| l.to_owned()).collect();
        self.viewport_pos = CharsXY::default();
        self.file_pos = CharsXY::default();
        self.insert_col = 0;
    }

    fn text(&self) -> String {
        self.content.iter().fold(String::new(), |contents, line| contents + line + "\n")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;
    use futures_lite::future::block_on;

    /// Syntactic sugar to easily instantiate a `CharsXY` at `row` plus `column`.
    fn rowcol(row: usize, column: usize) -> CharsXY {
        CharsXY::new(column, row)
    }

    /// Builder pattern to construct the expected sequence of side-effects on the console.
    #[must_use]
    struct OutputBuilder {
        console_size: CharsXY,
        output: Vec<CapturedOut>,
    }

    impl OutputBuilder {
        /// Constructs a new output builder with just the command to enter the alternate screen.
        /// `console_size` holds the size of the mock console, which is used to determine where to
        /// print the status bar.
        fn new(console_size: CharsXY) -> Self {
            Self { console_size, output: vec![CapturedOut::EnterAlt] }
        }

        /// Records the console changes needed to update the status line to reflect a new `file_pos`
        /// position.  Should not be used directly by tests.
        ///
        /// Note that, although `file_pos` is 0-indexed (to make it easier to reason about where
        /// file changes actually happen in the internal buffers), we display the position as
        /// 1-indexed here as the code under test does.
        fn refresh_status(mut self, file_pos: CharsXY) -> Self {
            let row = file_pos.y + 1;
            let column = file_pos.x + 1;

            self.output.push(CapturedOut::Locate(rowcol(self.console_size.y - 1, 0)));
            self.output.push(CapturedOut::Color(STATUS_COLOR.0, STATUS_COLOR.1));
            let mut status = String::from(" ESC Finish editing");
            if row < 10 && column < 10 {
                status += "       ";
            } else if row > 10 && column > 10 {
                status += "     ";
            } else {
                status += "      ";
            }
            status += &format!("| Ln {}, Col {} ", row, column);
            self.output.push(CapturedOut::Write(status.as_bytes().to_owned()));
            self
        }

        /// Records the console changes needed to incrementally update the editor, without going
        /// through a full refresh, assuming a `file_pos` position.
        fn quick_refresh(mut self, file_pos: CharsXY, cursor: CharsXY) -> Self {
            self.output.push(CapturedOut::HideCursor);
            self = self.refresh_status(file_pos);
            self.output.push(CapturedOut::Color(TEXT_COLOR.0, TEXT_COLOR.1));
            self.output.push(CapturedOut::Locate(cursor));
            self.output.push(CapturedOut::ShowCursor);
            self
        }

        /// Records the console changes needed to refresh the whole console view.  The status line
        /// is updated to reflect `file_pos`; the editor is pre-populated with the lines specified
        /// in `previous`; and the `cursor` is placed at the given location.
        fn refresh(mut self, file_pos: CharsXY, previous: &[&str], cursor: CharsXY) -> Self {
            self.output.push(CapturedOut::HideCursor);
            self.output.push(CapturedOut::Color(TEXT_COLOR.0, TEXT_COLOR.1));
            self.output.push(CapturedOut::Clear(ClearType::All));
            self = self.refresh_status(file_pos);
            self.output.push(CapturedOut::Color(TEXT_COLOR.0, TEXT_COLOR.1));
            self.output.push(CapturedOut::Locate(rowcol(0, 0)));
            for line in previous {
                self.output.push(CapturedOut::Print(line.to_string()));
            }
            self.output.push(CapturedOut::Locate(cursor));
            self.output.push(CapturedOut::ShowCursor);
            self
        }

        fn add(mut self, co: CapturedOut) -> Self {
            self.output.push(co);
            self
        }

        fn build(self) -> Vec<CapturedOut> {
            let mut output = self.output;
            output.push(CapturedOut::LeaveAlt);
            output
        }
    }

    /// Runs the editor and expects that the resulting text matches `exp_text` and that the
    /// side-effects on the console are those specified in `ob`.
    ///
    /// The editor can be pre-populated with some `previous` contents and the interactions with the
    /// editor are specified in `cb`. Note that the final Esc key press needed to exit the editor
    /// is automatically appended to `cb` here.
    fn run_editor(previous: &str, exp_text: &str, mut console: MockConsole, ob: OutputBuilder) {
        let mut editor = Editor::default();
        editor.load(previous);

        console.add_input_keys(&[Key::Escape]);
        block_on(editor.edit(&mut console)).unwrap();
        assert_eq!(exp_text, editor.text());
        assert_eq!(ob.build(), console.captured_out());
    }

    #[test]
    fn test_program_behavior() {
        let mut editor = Editor::default();
        assert!(editor.text().is_empty());

        editor.load("some text\n    and more\n");
        assert_eq!("some text\n    and more\n", editor.text());

        editor.load("different\n");
        assert_eq!("different\n", editor.text());
    }

    #[test]
    fn test_force_trailing_newline() {
        let mut editor = Editor::default();
        assert!(editor.text().is_empty());

        editor.load("missing\nnewline at eof");
        assert_eq!("missing\nnewline at eof\n", editor.text());
    }

    #[test]
    fn test_editing_with_previous_content_starts_on_top_left() {
        let mut cb = MockConsole::default();
        cb.set_size(rowcol(10, 40));
        let mut ob = OutputBuilder::new(rowcol(10, 40));
        ob = ob.refresh(rowcol(0, 0), &["previous content"], rowcol(0, 0));

        run_editor("previous content", "previous content\n", cb, ob);
    }

    #[test]
    fn test_insert_in_empty_file() {
        let mut cb = MockConsole::default();
        cb.set_size(rowcol(10, 40));
        let mut ob = OutputBuilder::new(rowcol(10, 40));
        ob = ob.refresh(rowcol(0, 0), &[""], rowcol(0, 0));

        cb.add_input_chars("abc");
        ob = ob.add(CapturedOut::Write(b"a".to_vec()));
        ob = ob.quick_refresh(rowcol(0, 1), rowcol(0, 1));
        ob = ob.add(CapturedOut::Write(b"b".to_vec()));
        ob = ob.quick_refresh(rowcol(0, 2), rowcol(0, 2));
        ob = ob.add(CapturedOut::Write(b"c".to_vec()));
        ob = ob.quick_refresh(rowcol(0, 3), rowcol(0, 3));

        cb.add_input_keys(&[Key::NewLine]);
        ob = ob.quick_refresh(rowcol(1, 0), rowcol(1, 0));

        cb.add_input_keys(&[Key::CarriageReturn]);
        ob = ob.quick_refresh(rowcol(2, 0), rowcol(2, 0));

        cb.add_input_chars("2");
        ob = ob.add(CapturedOut::Write(b"2".to_vec()));
        ob = ob.quick_refresh(rowcol(2, 1), rowcol(2, 1));

        run_editor("", "abc\n\n2\n", cb, ob);
    }

    #[test]
    fn test_insert_before_previous_content() {
        let mut cb = MockConsole::default();
        cb.set_size(rowcol(10, 40));
        let mut ob = OutputBuilder::new(rowcol(10, 40));
        ob = ob.refresh(rowcol(0, 0), &["previous content"], rowcol(0, 0));

        cb.add_input_chars("a");
        ob = ob.refresh(rowcol(0, 1), &["aprevious content"], rowcol(0, 1));

        cb.add_input_chars("b");
        ob = ob.refresh(rowcol(0, 2), &["abprevious content"], rowcol(0, 2));

        cb.add_input_chars("c");
        ob = ob.refresh(rowcol(0, 3), &["abcprevious content"], rowcol(0, 3));

        cb.add_input_chars(" ");
        ob = ob.refresh(rowcol(0, 4), &["abc previous content"], rowcol(0, 4));

        run_editor("previous content", "abc previous content\n", cb, ob);
    }

    #[test]
    fn test_move_in_empty_file() {
        let mut cb = MockConsole::default();
        cb.set_size(rowcol(10, 40));
        let mut ob = OutputBuilder::new(rowcol(10, 40));
        ob = ob.refresh(rowcol(0, 0), &[""], rowcol(0, 0));

        for k in &[Key::ArrowUp, Key::ArrowDown, Key::ArrowLeft, Key::ArrowRight] {
            cb.add_input_keys(&[k.clone()]);
            ob = ob.quick_refresh(rowcol(0, 0), rowcol(0, 0));
        }

        run_editor("", "\n", cb, ob);
    }

    #[test]
    fn test_move_preserves_insertion_column() {
        let mut cb = MockConsole::default();
        cb.set_size(rowcol(10, 40));
        let mut ob = OutputBuilder::new(rowcol(10, 40));
        ob = ob.refresh(rowcol(0, 0), &["longer", "a", "longer", "b"], rowcol(0, 0));

        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.quick_refresh(rowcol(0, 1), rowcol(0, 1));

        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.quick_refresh(rowcol(0, 2), rowcol(0, 2));

        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.quick_refresh(rowcol(0, 3), rowcol(0, 3));

        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.quick_refresh(rowcol(0, 4), rowcol(0, 4));

        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(rowcol(1, 1), rowcol(1, 1));

        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(rowcol(2, 4), rowcol(2, 4));

        cb.add_input_keys(&[Key::Char('X')]);
        ob = ob.refresh(rowcol(2, 5), &["longer", "a", "longXer", "b"], rowcol(2, 5));

        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(rowcol(3, 1), rowcol(3, 1));

        cb.add_input_keys(&[Key::Char('Z')]);
        ob = ob.add(CapturedOut::Write(b"Z".to_vec()));
        ob = ob.quick_refresh(rowcol(3, 2), rowcol(3, 2));

        run_editor("longer\na\nlonger\nb\n", "longer\na\nlongXer\nbZ\n", cb, ob);
    }

    #[test]
    fn test_move_down_preserves_insertion_column_with_horizontal_scrolling() {
        let mut cb = MockConsole::default();
        cb.set_size(rowcol(10, 40));
        let mut ob = OutputBuilder::new(rowcol(10, 40));
        ob = ob.refresh(
            rowcol(0, 0),
            &[
                "this is a line of text with more than 40",
                "short",
                "a",
                "",
                "another line of text with more than 40 c",
            ],
            rowcol(0, 0),
        );

        // Move the cursor to the right boundary.
        for col in 0..39 {
            cb.add_input_keys(&[Key::ArrowRight]);
            ob = ob.quick_refresh(rowcol(0, col + 1), rowcol(0, col + 1));
        }

        // Push the insertion point over the right boundary to cause scrolling.
        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.refresh(
            rowcol(0, 40),
            &[
                "his is a line of text with more than 40 ",
                "hort",
                "",
                "",
                "nother line of text with more than 40 ch",
            ],
            rowcol(0, 39),
        );
        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.refresh(
            rowcol(0, 41),
            &[
                "is is a line of text with more than 40 c",
                "ort",
                "",
                "",
                "other line of text with more than 40 cha",
            ],
            rowcol(0, 39),
        );

        // Move down to a shorter line whose end character is still visible. No scrolling.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(rowcol(1, 5), rowcol(1, 3));

        // Move down to a shorter line that's not visible but for which insertion can still happen
        // without scrolling.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(
            rowcol(2, 1),
            &[
                "his is a line of text with more than 40 ",
                "hort",
                "",
                "",
                "nother line of text with more than 40 ch",
            ],
            rowcol(2, 0),
        );

        // Move down to an empty line that requires horizontal scrolling for proper insertion.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(
            rowcol(3, 0),
            &[
                "this is a line of text with more than 40",
                "short",
                "a",
                "",
                "another line of text with more than 40 c",
            ],
            rowcol(3, 0),
        );

        // Move down to the last line, which is long again and thus needs scrolling to the right to
        // make the insertion point visible.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(
            rowcol(4, 41),
            &[
                "is is a line of text with more than 40 c",
                "ort",
                "",
                "",
                "other line of text with more than 40 cha",
            ],
            rowcol(4, 39),
        );

        run_editor(
            "this is a line of text with more than 40 characters\nshort\na\n\nanother line of text with more than 40 characters\n",
            "this is a line of text with more than 40 characters\nshort\na\n\nanother line of text with more than 40 characters\n",
            cb,
            ob);
    }

    #[test]
    fn test_move_up_preserves_insertion_column_with_horizontal_scrolling() {
        let mut cb = MockConsole::default();
        cb.set_size(rowcol(10, 40));
        let mut ob = OutputBuilder::new(rowcol(10, 40));
        ob = ob.refresh(
            rowcol(0, 0),
            &[
                "this is a line of text with more than 40",
                "",
                "a",
                "short",
                "another line of text with more than 40 c",
            ],
            rowcol(0, 0),
        );

        // Move to the last line.
        for i in 0..4 {
            cb.add_input_keys(&[Key::ArrowDown]);
            ob = ob.quick_refresh(rowcol(i + 1, 0), rowcol(i + 1, 0));
        }

        // Move the cursor to the right boundary.
        for col in 0..39 {
            cb.add_input_keys(&[Key::ArrowRight]);
            ob = ob.quick_refresh(rowcol(4, col + 1), rowcol(4, col + 1));
        }

        // Push the insertion point over the right boundary to cause scrolling.
        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.refresh(
            rowcol(4, 40),
            &[
                "his is a line of text with more than 40 ",
                "",
                "",
                "hort",
                "nother line of text with more than 40 ch",
            ],
            rowcol(4, 39),
        );
        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.refresh(
            rowcol(4, 41),
            &[
                "is is a line of text with more than 40 c",
                "",
                "",
                "ort",
                "other line of text with more than 40 cha",
            ],
            rowcol(4, 39),
        );

        // Move up to a shorter line whose end character is still visible. No scrolling.
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(rowcol(3, 5), rowcol(3, 3));

        // Move up to a shorter line that's not visible but for which insertion can still happen
        // without scrolling.
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.refresh(
            rowcol(2, 1),
            &[
                "his is a line of text with more than 40 ",
                "",
                "",
                "hort",
                "nother line of text with more than 40 ch",
            ],
            rowcol(2, 0),
        );

        // Move up to an empty line that requires horizontal scrolling for proper insertion.
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.refresh(
            rowcol(1, 0),
            &[
                "this is a line of text with more than 40",
                "",
                "a",
                "short",
                "another line of text with more than 40 c",
            ],
            rowcol(1, 0),
        );

        // Move up to the first line, which is long again and thus needs scrolling to the right to
        // make the insertion point visible.
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.refresh(
            rowcol(0, 41),
            &[
                "is is a line of text with more than 40 c",
                "",
                "",
                "ort",
                "other line of text with more than 40 cha",
            ],
            rowcol(0, 39),
        );

        run_editor(
            "this is a line of text with more than 40 characters\n\na\nshort\nanother line of text with more than 40 characters\n",
            "this is a line of text with more than 40 characters\n\na\nshort\nanother line of text with more than 40 characters\n",
            cb,
            ob);
    }

    #[test]
    fn test_horizontal_scrolling() {
        let mut cb = MockConsole::default();
        cb.set_size(rowcol(10, 40));
        let mut ob = OutputBuilder::new(rowcol(10, 40));
        ob = ob.refresh(rowcol(0, 0), &["ab", "", "xyz"], rowcol(0, 0));

        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(rowcol(1, 0), rowcol(1, 0));

        // Insert characters until the screen's right boundary.
        for (col, ch) in b"123456789012345678901234567890123456789".iter().enumerate() {
            cb.add_input_keys(&[Key::Char(*ch as char)]);
            ob = ob.add(CapturedOut::Write([*ch].to_vec()));
            ob = ob.quick_refresh(rowcol(1, col + 1), rowcol(1, col + 1));
        }

        // Push the insertion line over the right boundary and test that surrounding lines scroll as
        // well.
        cb.add_input_keys(&[Key::Char('A')]);
        ob = ob.refresh(
            rowcol(1, 40),
            &["b", "23456789012345678901234567890123456789A", "yz"],
            rowcol(1, 39),
        );
        cb.add_input_keys(&[Key::Char('B')]);
        ob = ob.refresh(
            rowcol(1, 41),
            &["", "3456789012345678901234567890123456789AB", "z"],
            rowcol(1, 39),
        );
        cb.add_input_keys(&[Key::Char('C')]);
        ob = ob.refresh(
            rowcol(1, 42),
            &["", "456789012345678901234567890123456789ABC", ""],
            rowcol(1, 39),
        );

        // Move back a few characters, without pushing over the left boundary, and then insert two
        // characters: one will cause the insertion line to fill up the empty space left by the
        // cursor and the other will cause the view of the insertion line to be truncated on the
        // right side.
        for (file_col, cursor_col) in &[(41, 38), (40, 37), (39, 36)] {
            cb.add_input_keys(&[Key::ArrowLeft]);
            ob = ob.quick_refresh(rowcol(1, *file_col), rowcol(1, *cursor_col));
        }
        cb.add_input_keys(&[Key::Char('D')]);
        ob = ob.refresh(
            rowcol(1, 40),
            &["", "456789012345678901234567890123456789DABC", ""],
            rowcol(1, 37),
        );
        cb.add_input_keys(&[Key::Char('E')]);
        ob = ob.refresh(
            rowcol(1, 41),
            &["", "456789012345678901234567890123456789DEAB", ""],
            rowcol(1, 38),
        );

        // Delete a few characters to restore the overflow part of the insertion line.
        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.refresh(
            rowcol(1, 40),
            &["", "456789012345678901234567890123456789DABC", ""],
            rowcol(1, 37),
        );
        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.refresh(
            rowcol(1, 39),
            &["", "456789012345678901234567890123456789ABC", ""],
            rowcol(1, 36),
        );
        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.refresh(
            rowcol(1, 38),
            &["", "45678901234567890123456789012345678ABC", ""],
            rowcol(1, 35),
        );

        // Move back to the beginning of the line to see surrounding lines reappear.
        for col in 0..35 {
            cb.add_input_keys(&[Key::ArrowLeft]);
            ob = ob.quick_refresh(rowcol(1, 37 - col), rowcol(1, 34 - col));
        }
        cb.add_input_keys(&[Key::ArrowLeft]);
        ob = ob.refresh(
            rowcol(1, 2),
            &["", "345678901234567890123456789012345678ABC", "z"],
            rowcol(1, 0),
        );
        cb.add_input_keys(&[Key::ArrowLeft]);
        ob = ob.refresh(
            rowcol(1, 1),
            &["b", "2345678901234567890123456789012345678ABC", "yz"],
            rowcol(1, 0),
        );
        cb.add_input_keys(&[Key::ArrowLeft]);
        ob = ob.refresh(
            rowcol(1, 0),
            &["ab", "12345678901234567890123456789012345678AB", "xyz"],
            rowcol(1, 0),
        );

        run_editor("ab\n\nxyz\n", "ab\n12345678901234567890123456789012345678ABC\nxyz\n", cb, ob);
    }

    #[test]
    fn test_vertical_scrolling() {
        let mut cb = MockConsole::default();
        cb.set_size(rowcol(5, 40));
        let mut ob = OutputBuilder::new(rowcol(5, 40));
        ob = ob.refresh(rowcol(0, 0), &["abc", "", "d", "e"], rowcol(0, 0));

        // Move to the last line.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(rowcol(1, 0), rowcol(1, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(rowcol(2, 0), rowcol(2, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(rowcol(3, 0), rowcol(3, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(rowcol(4, 0), &["", "d", "e", ""], rowcol(3, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(rowcol(5, 0), &["d", "e", "", "fg"], rowcol(3, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(rowcol(6, 0), &["e", "", "fg", "hij"], rowcol(3, 0));

        // Attempting to push through the end of the file does nothing.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(rowcol(6, 0), rowcol(3, 0));

        // Go back up to the first line.
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(rowcol(5, 0), rowcol(2, 0));
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(rowcol(4, 0), rowcol(1, 0));
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(rowcol(3, 0), rowcol(0, 0));
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.refresh(rowcol(2, 0), &["d", "e", "", "fg"], rowcol(0, 0));
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.refresh(rowcol(1, 0), &["", "d", "e", ""], rowcol(0, 0));
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.refresh(rowcol(0, 0), &["abc", "", "d", "e"], rowcol(0, 0));

        // Attempting to push through the beginning of the file does nothing.
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(rowcol(0, 0), rowcol(0, 0));

        run_editor("abc\n\nd\ne\n\nfg\nhij\n", "abc\n\nd\ne\n\nfg\nhij\n", cb, ob);
    }

    #[test]
    fn test_vertical_scrolling_when_splitting_last_visible_line() {
        let mut cb = MockConsole::default();
        cb.set_size(rowcol(4, 40));
        let mut ob = OutputBuilder::new(rowcol(4, 40));
        ob = ob.refresh(rowcol(0, 0), &["first", "second", "thirdfourth"], rowcol(0, 0));

        // Move to the desired split point.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(rowcol(1, 0), rowcol(1, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(rowcol(2, 0), rowcol(2, 0));
        for i in 0.."third".len() {
            cb.add_input_keys(&[Key::ArrowRight]);
            ob = ob.quick_refresh(rowcol(2, i + 1), rowcol(2, i + 1));
        }

        // Split the last visible line.
        cb.add_input_keys(&[Key::NewLine]);
        ob = ob.refresh(rowcol(3, 0), &["second", "third", "fourth"], rowcol(2, 0));

        run_editor(
            "first\nsecond\nthirdfourth\nfifth\n",
            "first\nsecond\nthird\nfourth\nfifth\n",
            cb,
            ob,
        );
    }

    #[test]
    fn test_horizontal_and_vertical_scrolling_when_splitting_last_visible_line() {
        let mut cb = MockConsole::default();
        cb.set_size(rowcol(4, 40));
        let mut ob = OutputBuilder::new(rowcol(4, 40));
        ob = ob.refresh(
            rowcol(0, 0),
            &["first", "second", "this is a line of text with more than 40"],
            rowcol(0, 0),
        );

        // Move to the desired split point.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(rowcol(1, 0), rowcol(1, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(rowcol(2, 0), rowcol(2, 0));
        for i in 0..39 {
            cb.add_input_keys(&[Key::ArrowRight]);
            ob = ob.quick_refresh(rowcol(2, i + 1), rowcol(2, i + 1));
        }
        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.refresh(
            rowcol(2, 40),
            &["irst", "econd", "his is a line of text with more than 40 "],
            rowcol(2, 39),
        );

        // Split the last visible line.
        cb.add_input_keys(&[Key::NewLine]);
        ob = ob.refresh(
            rowcol(3, 0),
            &["second", "this is a line of text with more than 40", " characters"],
            rowcol(2, 0),
        );

        run_editor(
            "first\nsecond\nthis is a line of text with more than 40 characters\nfifth\n",
            "first\nsecond\nthis is a line of text with more than 40\n characters\nfifth\n",
            cb,
            ob,
        );
    }

    #[test]
    fn test_vertical_scrolling_when_joining_first_visible_line() {
        let mut cb = MockConsole::default();
        cb.set_size(rowcol(4, 40));
        let mut ob = OutputBuilder::new(rowcol(4, 40));
        ob = ob.refresh(rowcol(0, 0), &["first", "second", "third"], rowcol(0, 0));

        // Move down until a couple of lines scroll up.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(rowcol(1, 0), rowcol(1, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(rowcol(2, 0), rowcol(2, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(rowcol(3, 0), &["second", "third", "fourth"], rowcol(2, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(rowcol(4, 0), &["third", "fourth", "fifth"], rowcol(2, 0));

        // Move back up to the first visible line, without scrolling.
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(rowcol(3, 0), rowcol(1, 0));
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(rowcol(2, 0), rowcol(0, 0));

        // Join first visible line with previous, which should scroll contents up.
        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.refresh(rowcol(1, 6), &["secondthird", "fourth", "fifth"], rowcol(0, 6));

        run_editor(
            "first\nsecond\nthird\nfourth\nfifth\n",
            "first\nsecondthird\nfourth\nfifth\n",
            cb,
            ob,
        );
    }

    #[test]
    fn test_horizontal_and_vertical_scrolling_when_joining_first_visible_line() {
        let mut cb = MockConsole::default();
        cb.set_size(rowcol(4, 40));
        let mut ob = OutputBuilder::new(rowcol(4, 40));
        ob = ob.refresh(
            rowcol(0, 0),
            &["first", "this is a line of text with more than 40", "third"],
            rowcol(0, 0),
        );

        // Move down until a couple of lines scroll up.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(rowcol(1, 0), rowcol(1, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(rowcol(2, 0), rowcol(2, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(
            rowcol(3, 0),
            &["this is a line of text with more than 40", "third", "fourth"],
            rowcol(2, 0),
        );
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(rowcol(4, 0), &["third", "fourth", "quite a long line"], rowcol(2, 0));

        // Move back up to the first visible line, without scrolling.
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(rowcol(3, 0), rowcol(1, 0));
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(rowcol(2, 0), rowcol(0, 0));

        // Join first visible line with previous, which should scroll contents up and right.
        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.refresh(
            rowcol(1, 51),
            &["ne of text with more than 40 characterst", "", " line"],
            rowcol(0, 39),
        );

        run_editor(
            "first\nthis is a line of text with more than 40 characters\nthird\nfourth\nquite a long line\n",
            "first\nthis is a line of text with more than 40 charactersthird\nfourth\nquite a long line\n",
            cb,
            ob,
        );
    }
}
