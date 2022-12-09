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
use async_trait::async_trait;
use endbasic_std::console::{AnsiColor, LineBuffer};
use endbasic_std::program::Program;
use std::cmp;
use std::convert::TryFrom;
use std::io;

/// The color of the main editor window.
const TEXT_COLOR: (Option<u8>, Option<u8>) = (Some(AnsiColor::BrightWhite as u8), None);

/// The color of the editor status bar.
const STATUS_COLOR: (Option<u8>, Option<u8>) =
    (Some(AnsiColor::BrightWhite as u8), Some(AnsiColor::Blue as u8));

/// Default indentation with.
const INDENT_WIDTH: usize = 4;

/// Keybindings cheat sheet.
const KEYS_SUMMARY: &str = " ESC Exit ";

/// Returns the indentation of a given string as a new string.
fn copy_indent(line: &LineBuffer) -> String {
    let mut indent = String::new();
    for ch in line.chars() {
        if !ch.is_whitespace() {
            break;
        }
        indent.push(ch);
    }
    indent
}

/// Finds the first position within the line that is not an indentation character, or returns
/// the line length if no such character is found.
fn find_indent_end(line: &LineBuffer) -> usize {
    let mut pos = 0;
    for ch in line.chars() {
        if ch != ' ' {
            break;
        }
        pos += 1;
    }
    debug_assert!(pos <= line.len());
    pos
}

/// Represents a position within a file.
#[derive(Clone, Copy, Default)]
struct FilePos {
    /// The column number, starting from zero.
    line: usize,

    /// The row number, starting from zero.
    col: usize,
}

/// An interactive console-based text editor.
///
/// The text editor owns the textual contents it is editing.
pub struct Editor {
    /// Path of the loaded program.  `None` if the program has never been saved yet.
    name: Option<String>,

    /// Owned contents of the file being edited.
    content: Vec<LineBuffer>,

    /// Whether the `content` was modified since it was last retrieved.
    dirty: bool,

    /// Position of the top-left character of the file visible in the console.
    viewport_pos: FilePos,

    /// Insertion position within the file.
    file_pos: FilePos,

    /// Last edited column, used when moving vertically to preserve the insertion point even when
    /// traversing shorter lines.
    insert_col: usize,
}

impl Default for Editor {
    /// Creates a new editor without any stored contents.
    fn default() -> Self {
        Self {
            name: None,
            content: vec![],
            dirty: false,
            viewport_pos: FilePos::default(),
            file_pos: FilePos::default(),
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
        // Even though we track file positions as 0-indexed, display them as 1-indexed for a better
        // user experience given that this is what all other editor seem to do.
        let dirty_marker = if self.dirty { "*" } else { "" };
        let details = format!(
            " | {}{} | Ln {}, Col {} ",
            self.name.as_deref().unwrap_or("<NO NAME>"),
            dirty_marker,
            self.file_pos.line + 1,
            self.file_pos.col + 1
        );

        let width = usize::from(console_size.x);
        let mut status = String::with_capacity(width);
        status.push_str(KEYS_SUMMARY);
        while status.len() < width - details.len() {
            status.push(' ');
        }
        status.push_str(&details);
        status.truncate(width);

        console.locate(CharsXY::new(0, console_size.y - 1))?;
        console.set_color(STATUS_COLOR.0, STATUS_COLOR.1)?;
        console.write(&status)?;
        Ok(())
    }

    /// Refreshes the contents of the whole `console`, using the previously queried `console_size`.
    ///
    /// It is the responsibility of the caller to move the cursor back to the appropriate location
    /// after calling this function, and the caller should also hide the cursor before calling this
    /// function.
    fn refresh(&self, console: &mut dyn Console, console_size: CharsXY) -> io::Result<()> {
        console.set_color(TEXT_COLOR.0, TEXT_COLOR.1)?;
        console.clear(ClearType::All)?;
        self.refresh_status(console, console_size)?;
        console.set_color(TEXT_COLOR.0, TEXT_COLOR.1)?;
        console.locate(CharsXY::default())?;

        let mut row = self.viewport_pos.line;
        let mut printed_rows = 0;
        while row < self.content.len() && printed_rows < console_size.y - 1 {
            let line = &self.content[row];
            let line_len = line.len();
            if line_len > self.viewport_pos.col {
                console.print(&line.range(
                    self.viewport_pos.col,
                    self.viewport_pos.col + usize::from(console_size.x),
                ))?;
            } else {
                console.print("")?;
            }
            row += 1;
            printed_rows += 1;
        }
        Ok(())
    }

    /// Moves the cursor down by the given number of lines in `nlines` or to the last line if there
    /// are insufficient lines to perform the move.
    fn move_down(&mut self, nlines: usize) {
        if self.file_pos.line + nlines < self.content.len() {
            self.file_pos.line += nlines;
        } else {
            self.file_pos.line = self.content.len() - 1;
        }

        let line = &self.content[self.file_pos.line];
        self.file_pos.col = cmp::min(self.insert_col, line.len());
    }

    /// Moves the cursor up by the given number of lines in `nlines` or to the first line if there
    /// are insufficient lines to perform the move.
    fn move_up(&mut self, nlines: usize) {
        if self.file_pos.line > nlines {
            self.file_pos.line -= nlines;
        } else {
            self.file_pos.line = 0;
        }

        let line = &self.content[self.file_pos.line];
        self.file_pos.col = cmp::min(self.insert_col, line.len());
    }

    /// Internal implementation of the interactive editor, which interacts with the `console`.
    async fn edit_interactively(&mut self, console: &mut dyn Console) -> io::Result<()> {
        let console_size = console.size_chars()?;

        if self.content.is_empty() {
            self.content.push(LineBuffer::default());
        }

        let mut need_refresh = true;
        loop {
            // The key handling below only deals with moving the insertion position within the file
            // but does not bother to update the viewport. Adjust it now, if necessary.
            let width = usize::from(console_size.x);
            let height = usize::from(console_size.y);
            if self.file_pos.line < self.viewport_pos.line {
                self.viewport_pos.line = self.file_pos.line;
                need_refresh = true;
            } else if self.file_pos.line > self.viewport_pos.line + height - 2 {
                if self.file_pos.line > height - 2 {
                    self.viewport_pos.line = self.file_pos.line - (height - 2);
                } else {
                    self.viewport_pos.line = 0;
                }
                need_refresh = true;
            }

            if self.file_pos.col < self.viewport_pos.col {
                self.viewport_pos.col = self.file_pos.col;
                need_refresh = true;
            } else if self.file_pos.col >= self.viewport_pos.col + width {
                self.viewport_pos.col = self.file_pos.col - width + 1;
                need_refresh = true;
            }

            console.hide_cursor()?;
            if need_refresh {
                self.refresh(console, console_size)?;
                need_refresh = false;
            } else {
                self.refresh_status(console, console_size)?;
                console.set_color(TEXT_COLOR.0, TEXT_COLOR.1)?;
            }
            let cursor_pos = {
                let x = u16::try_from(self.file_pos.col - self.viewport_pos.col)
                    .expect("Computed x must have fit on screen");
                let y = u16::try_from(self.file_pos.line - self.viewport_pos.line)
                    .expect("Computed y must have fit on screen");
                CharsXY::new(x, y)
            };
            console.locate(cursor_pos)?;
            console.show_cursor()?;

            match console.read_key().await? {
                Key::Escape | Key::Eof | Key::Interrupt => break,

                Key::ArrowUp => self.move_up(1),

                Key::ArrowDown => self.move_down(1),

                Key::ArrowLeft => {
                    if self.file_pos.col > 0 {
                        self.file_pos.col -= 1;
                        self.insert_col = self.file_pos.col;
                    }
                }

                Key::ArrowRight => {
                    if self.file_pos.col < self.content[self.file_pos.line].len() {
                        self.file_pos.col += 1;
                        self.insert_col = self.file_pos.col;
                    }
                }

                Key::Backspace => {
                    if self.file_pos.col > 0 {
                        let line = &mut self.content[self.file_pos.line];

                        let indent_pos = find_indent_end(line);
                        let is_indent = indent_pos >= self.file_pos.col;
                        let nremove = if is_indent {
                            let new_pos = if self.file_pos.col >= INDENT_WIDTH {
                                (self.file_pos.col - 1) / INDENT_WIDTH * INDENT_WIDTH
                            } else {
                                0
                            };
                            self.file_pos.col - new_pos
                        } else {
                            1
                        };

                        if self.file_pos.col == line.len() {
                            if nremove > 0 {
                                console.hide_cursor()?;
                            }
                            for _ in 0..nremove {
                                console.clear(ClearType::PreviousChar)?;
                            }
                            if nremove > 0 {
                                console.show_cursor()?;
                            }
                        } else {
                            // TODO(jmmv): Refresh only the affected line.
                            need_refresh = true;
                        }
                        for _ in 0..nremove {
                            line.remove(self.file_pos.col - 1);
                            self.file_pos.col -= 1;
                        }
                        if nremove > 0 {
                            self.dirty = true;
                        }
                    } else if self.file_pos.line > 0 {
                        let line = self.content.remove(self.file_pos.line);
                        let prev = &mut self.content[self.file_pos.line - 1];
                        self.file_pos.col = prev.len();
                        prev.push_str(&line);
                        self.file_pos.line -= 1;
                        need_refresh = true;
                        self.dirty = true;
                    }
                    self.insert_col = self.file_pos.col;
                }

                Key::Char(ch) => {
                    let mut buf = [0; 4];

                    let line = &mut self.content[self.file_pos.line];
                    if self.file_pos.col < line.len() {
                        // TODO(jmmv): Refresh only the affected line.
                        need_refresh = true;
                    }

                    line.insert(self.file_pos.col, ch);
                    self.file_pos.col += 1;
                    self.insert_col = self.file_pos.col;

                    if cursor_pos.x < console_size.x - 1 && !need_refresh {
                        console.write(ch.encode_utf8(&mut buf))?;
                    }

                    self.dirty = true;
                }

                Key::End => {
                    self.file_pos.col = self.content[self.file_pos.line].len();
                    self.insert_col = self.file_pos.col;
                }

                Key::Home => {
                    let indent_pos = find_indent_end(&self.content[self.file_pos.line]);
                    if self.file_pos.col == indent_pos {
                        self.file_pos.col = 0;
                    } else {
                        self.file_pos.col = indent_pos;
                    }
                    self.insert_col = self.file_pos.col;
                }

                Key::NewLine | Key::CarriageReturn => {
                    let indent = copy_indent(&self.content[self.file_pos.line]);
                    let indent_len = indent.len();

                    let appending = (self.file_pos.line + 1 == self.content.len())
                        && (self.file_pos.col == self.content[self.file_pos.line].len());

                    let new = self.content[self.file_pos.line].split_off(self.file_pos.col);
                    self.content.insert(
                        self.file_pos.line + 1,
                        LineBuffer::from(indent + &new.into_inner()),
                    );
                    need_refresh = !appending;

                    self.file_pos.col = indent_len;
                    self.file_pos.line += 1;
                    self.insert_col = self.file_pos.col;
                    self.dirty = true;
                }

                Key::PageDown => self.move_down(usize::from(console_size.y - 2)),

                Key::PageUp => self.move_up(usize::from(console_size.y - 2)),

                Key::Tab => {
                    let line = &mut self.content[self.file_pos.line];
                    if self.file_pos.col < line.len() {
                        // TODO(jmmv): Refresh only the affected line.
                        need_refresh = true;
                    }

                    let new_pos = (self.file_pos.col + INDENT_WIDTH) / INDENT_WIDTH * INDENT_WIDTH;
                    let mut new_text = String::with_capacity(new_pos - self.file_pos.col);
                    for _ in 0..new_text.capacity() {
                        new_text.push(' ');
                    }
                    line.insert_str(self.file_pos.col, &new_text);
                    self.file_pos.col = new_pos;
                    self.insert_col = self.file_pos.col;
                    if !need_refresh {
                        console.write(&new_text)?;
                    }
                    self.dirty = true;
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
    fn is_dirty(&self) -> bool {
        self.dirty
    }

    async fn edit(&mut self, console: &mut dyn Console) -> io::Result<()> {
        console.enter_alt()?;
        let result = self.edit_interactively(console).await;
        console.leave_alt()?;
        result
    }

    fn load(&mut self, name: Option<&str>, text: &str) {
        self.name = name.map(str::to_owned);
        self.content = text.lines().map(LineBuffer::from).collect();
        self.dirty = false;
        self.viewport_pos = FilePos::default();
        self.file_pos = FilePos::default();
        self.insert_col = 0;
    }

    fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    fn set_name(&mut self, name: &str) {
        self.name = Some(name.to_owned());
        self.dirty = false;
    }

    fn text(&self) -> String {
        self.content
            .iter()
            .fold(String::new(), |contents, line| contents + &line.to_string() + "\n")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use endbasic_std::testutils::*;
    use futures_lite::future::block_on;

    /// Name of the program to inject into the editor for testing.  The name is very short because
    /// all tests operate on a pretty narrow window and the status bar would be mangled otherwise.
    const TEST_FILENAME: &str = "X";

    /// Syntactic sugar to easily instantiate a `CharsXY` at `(x,y)`.
    ///
    /// Note that the input arguments here are swapped.  This is partly because of historical
    /// reasons, but also because virtually all editors (including this one) display file positions
    /// with the line first followed by the column.  It's easier to reason about the tests below
    /// when the order of the arguments to `linecol` matches `yx`.
    fn yx(y: u16, x: u16) -> CharsXY {
        CharsXY::new(x, y)
    }

    /// Syntactic sugar to easily instantiate a `FilePos` at `(line, col)`.
    fn linecol(line: usize, col: usize) -> FilePos {
        FilePos { line, col }
    }

    /// Builder pattern to construct the expected sequence of side-effects on the console.
    #[must_use]
    struct OutputBuilder {
        console_size: CharsXY,
        output: Vec<CapturedOut>,
        dirty: bool,
    }

    impl OutputBuilder {
        /// Constructs a new output builder with just the command to enter the alternate screen.
        /// `console_size` holds the size of the mock console, which is used to determine where to
        /// print the status bar.
        fn new(console_size: CharsXY) -> Self {
            Self { console_size, output: vec![CapturedOut::EnterAlt], dirty: false }
        }

        /// Records the console changes needed to update the status line to reflect a new `file_pos`
        /// position.  Should not be used directly by tests.
        ///
        /// Note that, although `file_pos` is 0-indexed (to make it easier to reason about where
        /// file changes actually happen in the internal buffers), we display the position as
        /// 1-indexed here as the code under test does.
        fn refresh_status(mut self, file_pos: FilePos) -> Self {
            let row = file_pos.line + 1;
            let column = file_pos.col + 1;

            self.output.push(CapturedOut::Locate(yx(self.console_size.y - 1, 0)));
            self.output.push(CapturedOut::SetColor(STATUS_COLOR.0, STATUS_COLOR.1));
            let dirty_marker = if self.dirty { "*" } else { "" };
            let details =
                &format!("| {}{} | Ln {}, Col {} ", TEST_FILENAME, dirty_marker, row, column);
            let mut status = String::from(KEYS_SUMMARY);
            while status.len() + details.len() < usize::from(self.console_size.x) {
                status.push(' ');
            }
            status += details;
            self.output.push(CapturedOut::Write(status));
            self
        }

        /// Records the console changes needed to incrementally update the editor, without going
        /// through a full refresh, assuming a `file_pos` position.
        fn quick_refresh(mut self, file_pos: FilePos, cursor: CharsXY) -> Self {
            self.output.push(CapturedOut::HideCursor);
            self = self.refresh_status(file_pos);
            self.output.push(CapturedOut::SetColor(TEXT_COLOR.0, TEXT_COLOR.1));
            self.output.push(CapturedOut::Locate(cursor));
            self.output.push(CapturedOut::ShowCursor);
            self
        }

        /// Records the console changes needed to refresh the whole console view.  The status line
        /// is updated to reflect `file_pos`; the editor is pre-populated with the lines specified
        /// in `previous`; and the `cursor` is placed at the given location.
        fn refresh(mut self, file_pos: FilePos, previous: &[&str], cursor: CharsXY) -> Self {
            self.output.push(CapturedOut::HideCursor);
            self.output.push(CapturedOut::SetColor(TEXT_COLOR.0, TEXT_COLOR.1));
            self.output.push(CapturedOut::Clear(ClearType::All));
            self = self.refresh_status(file_pos);
            self.output.push(CapturedOut::SetColor(TEXT_COLOR.0, TEXT_COLOR.1));
            self.output.push(CapturedOut::Locate(yx(0, 0)));
            for line in previous {
                self.output.push(CapturedOut::Print(line.to_string()));
            }
            self.output.push(CapturedOut::Locate(cursor));
            self.output.push(CapturedOut::ShowCursor);
            self
        }

        /// Registers a new expected side-effect `co` on the console.
        fn add(mut self, co: CapturedOut) -> Self {
            self.output.push(co);
            self
        }

        /// Registers that the file has been modified.
        fn set_dirty(mut self) -> Self {
            self.dirty = true;
            self
        }

        /// Finalizes the list of expected side-effects on the console.
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
        editor.load(Some(TEST_FILENAME), previous);

        console.add_input_keys(&[Key::Escape]);
        block_on(editor.edit(&mut console)).unwrap();
        assert_eq!(exp_text, editor.text());
        assert_eq!(ob.dirty, editor.is_dirty());
        assert_eq!(ob.build(), console.captured_out());
    }

    #[test]
    fn test_program_behavior() {
        let mut editor = Editor::default();
        assert!(editor.text().is_empty());
        assert!(!editor.is_dirty());

        let mut console = MockConsole::default();
        console.set_size_chars(yx(10, 40));
        block_on(editor.edit(&mut console)).unwrap();
        assert!(!editor.is_dirty());

        console.add_input_keys(&[Key::Char('x')]);
        block_on(editor.edit(&mut console)).unwrap();
        assert!(editor.is_dirty());

        editor.load(Some(TEST_FILENAME), "some text\n    and more\n");
        assert_eq!("some text\n    and more\n", editor.text());
        assert!(!editor.is_dirty());

        editor.load(Some(TEST_FILENAME), "different\n");
        assert_eq!("different\n", editor.text());
        assert!(!editor.is_dirty());

        console.add_input_keys(&[Key::Char('x')]);
        block_on(editor.edit(&mut console)).unwrap();
        assert!(editor.is_dirty());

        editor.set_name("SAVED");
        assert!(!editor.is_dirty());
    }

    #[test]
    fn test_force_trailing_newline() {
        let mut editor = Editor::default();
        assert!(editor.text().is_empty());

        editor.load(Some(TEST_FILENAME), "missing\nnewline at eof");
        assert_eq!("missing\nnewline at eof\n", editor.text());
    }

    #[test]
    fn test_editing_with_previous_content_starts_on_top_left() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(linecol(0, 0), &["previous content"], yx(0, 0));

        run_editor("previous content", "previous content\n", cb, ob);
    }

    #[test]
    fn test_insert_in_empty_file() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(linecol(0, 0), &[""], yx(0, 0));

        cb.add_input_chars("abcéà");
        ob = ob.set_dirty();
        ob = ob.add(CapturedOut::Write("a".to_string()));
        ob = ob.quick_refresh(linecol(0, 1), yx(0, 1));
        ob = ob.add(CapturedOut::Write("b".to_string()));
        ob = ob.quick_refresh(linecol(0, 2), yx(0, 2));
        ob = ob.add(CapturedOut::Write("c".to_string()));
        ob = ob.quick_refresh(linecol(0, 3), yx(0, 3));
        ob = ob.add(CapturedOut::Write("é".to_string()));
        ob = ob.quick_refresh(linecol(0, 4), yx(0, 4));
        ob = ob.add(CapturedOut::Write("à".to_string()));
        ob = ob.quick_refresh(linecol(0, 5), yx(0, 5));

        cb.add_input_keys(&[Key::NewLine]);
        ob = ob.quick_refresh(linecol(1, 0), yx(1, 0));

        cb.add_input_keys(&[Key::CarriageReturn]);
        ob = ob.quick_refresh(linecol(2, 0), yx(2, 0));

        cb.add_input_chars("2");
        ob = ob.add(CapturedOut::Write("2".to_string()));
        ob = ob.quick_refresh(linecol(2, 1), yx(2, 1));

        run_editor("", "abcéà\n\n2\n", cb, ob);
    }

    #[test]
    fn test_insert_before_previous_content() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(linecol(0, 0), &["previous content"], yx(0, 0));

        cb.add_input_chars("a");
        ob = ob.set_dirty();
        ob = ob.refresh(linecol(0, 1), &["aprevious content"], yx(0, 1));

        cb.add_input_chars("b");
        ob = ob.refresh(linecol(0, 2), &["abprevious content"], yx(0, 2));

        cb.add_input_chars("c");
        ob = ob.refresh(linecol(0, 3), &["abcprevious content"], yx(0, 3));

        cb.add_input_chars(" ");
        ob = ob.refresh(linecol(0, 4), &["abc previous content"], yx(0, 4));

        run_editor("previous content", "abc previous content\n", cb, ob);
    }

    #[test]
    fn test_insert_before_last_character() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(linecol(0, 0), &[""], yx(0, 0));

        cb.add_input_chars("abc");
        ob = ob.set_dirty();
        ob = ob.add(CapturedOut::Write("a".to_string()));
        ob = ob.quick_refresh(linecol(0, 1), yx(0, 1));
        ob = ob.add(CapturedOut::Write("b".to_string()));
        ob = ob.quick_refresh(linecol(0, 2), yx(0, 2));
        ob = ob.add(CapturedOut::Write("c".to_string()));
        ob = ob.quick_refresh(linecol(0, 3), yx(0, 3));

        cb.add_input_keys(&[Key::ArrowLeft]);
        ob = ob.quick_refresh(linecol(0, 2), yx(0, 2));

        cb.add_input_chars("d");
        ob = ob.refresh(linecol(0, 3), &["abdc"], yx(0, 3));

        run_editor("", "abdc\n", cb, ob);
    }

    #[test]
    fn test_insert_newline_in_middle() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(linecol(0, 0), &[""], yx(0, 0));

        cb.add_input_chars("abc");
        ob = ob.set_dirty();
        ob = ob.add(CapturedOut::Write("a".to_string()));
        ob = ob.quick_refresh(linecol(0, 1), yx(0, 1));
        ob = ob.add(CapturedOut::Write("b".to_string()));
        ob = ob.quick_refresh(linecol(0, 2), yx(0, 2));
        ob = ob.add(CapturedOut::Write("c".to_string()));
        ob = ob.quick_refresh(linecol(0, 3), yx(0, 3));

        cb.add_input_keys(&[Key::ArrowLeft]);
        ob = ob.quick_refresh(linecol(0, 2), yx(0, 2));

        cb.add_input_keys(&[Key::NewLine]);
        ob = ob.refresh(linecol(1, 0), &["ab", "c"], yx(1, 0));

        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(linecol(0, 0), yx(0, 0));
        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.quick_refresh(linecol(0, 1), yx(0, 1));
        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.quick_refresh(linecol(0, 2), yx(0, 2));

        cb.add_input_keys(&[Key::NewLine]);
        ob = ob.refresh(linecol(1, 0), &["ab", "", "c"], yx(1, 0));

        run_editor("", "ab\n\nc\n", cb, ob);
    }

    #[test]
    fn test_split_last_line() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(linecol(0, 0), &[""], yx(0, 0));

        cb.add_input_chars("  abcd");
        ob = ob.set_dirty();
        ob = ob.add(CapturedOut::Write(" ".to_string()));
        ob = ob.quick_refresh(linecol(0, 1), yx(0, 1));
        ob = ob.add(CapturedOut::Write(" ".to_string()));
        ob = ob.quick_refresh(linecol(0, 2), yx(0, 2));
        ob = ob.add(CapturedOut::Write("a".to_string()));
        ob = ob.quick_refresh(linecol(0, 3), yx(0, 3));
        ob = ob.add(CapturedOut::Write("b".to_string()));
        ob = ob.quick_refresh(linecol(0, 4), yx(0, 4));
        ob = ob.add(CapturedOut::Write("c".to_string()));
        ob = ob.quick_refresh(linecol(0, 5), yx(0, 5));
        ob = ob.add(CapturedOut::Write("d".to_string()));
        ob = ob.quick_refresh(linecol(0, 6), yx(0, 6));

        cb.add_input_keys(&[Key::ArrowLeft]);
        ob = ob.quick_refresh(linecol(0, 5), yx(0, 5));
        cb.add_input_keys(&[Key::ArrowLeft]);
        ob = ob.quick_refresh(linecol(0, 4), yx(0, 4));

        cb.add_input_keys(&[Key::NewLine]);
        ob = ob.refresh(linecol(1, 2), &["  ab", "  cd"], yx(1, 2));

        run_editor("", "  ab\n  cd\n", cb, ob);
    }

    #[test]
    fn test_move_in_empty_file() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(linecol(0, 0), &[""], yx(0, 0));

        for k in &[
            Key::ArrowUp,
            Key::ArrowDown,
            Key::ArrowLeft,
            Key::ArrowRight,
            Key::PageUp,
            Key::PageDown,
        ] {
            cb.add_input_keys(&[k.clone()]);
            ob = ob.quick_refresh(linecol(0, 0), yx(0, 0));
        }

        run_editor("", "\n", cb, ob);
    }

    #[test]
    fn test_move_end() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(linecol(0, 0), &["text"], yx(0, 0));

        cb.add_input_keys(&[Key::End]);
        ob = ob.quick_refresh(linecol(0, 4), yx(0, 4));

        cb.add_input_chars(".");
        ob = ob.set_dirty();
        ob = ob.add(CapturedOut::Write(".".to_string()));
        ob = ob.quick_refresh(linecol(0, 5), yx(0, 5));

        run_editor("text", "text.\n", cb, ob);
    }

    #[test]
    fn test_move_home_no_indent() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(linecol(0, 0), &["text"], yx(0, 0));

        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.quick_refresh(linecol(0, 1), yx(0, 1));

        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.quick_refresh(linecol(0, 2), yx(0, 2));

        cb.add_input_keys(&[Key::Home]);
        ob = ob.quick_refresh(linecol(0, 0), yx(0, 0));

        cb.add_input_chars(".");
        ob = ob.set_dirty();
        ob = ob.refresh(linecol(0, 1), &[".text"], yx(0, 1));

        cb.add_input_keys(&[Key::Home]);
        ob = ob.quick_refresh(linecol(0, 0), yx(0, 0));

        cb.add_input_chars(",");
        ob = ob.refresh(linecol(0, 1), &[",.text"], yx(0, 1));

        run_editor("text", ",.text\n", cb, ob);
    }

    #[test]
    fn test_move_home_with_indent() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(linecol(0, 0), &["  text"], yx(0, 0));

        cb.add_input_keys(&[Key::Home]);
        ob = ob.quick_refresh(linecol(0, 2), yx(0, 2));

        cb.add_input_keys(&[Key::Home]);
        ob = ob.quick_refresh(linecol(0, 0), yx(0, 0));

        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.quick_refresh(linecol(0, 1), yx(0, 1));

        cb.add_input_keys(&[Key::Home]);
        ob = ob.quick_refresh(linecol(0, 2), yx(0, 2));

        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.quick_refresh(linecol(0, 3), yx(0, 3));

        cb.add_input_keys(&[Key::Home]);
        ob = ob.quick_refresh(linecol(0, 2), yx(0, 2));

        cb.add_input_chars(".");
        ob = ob.set_dirty();
        ob = ob.refresh(linecol(0, 3), &["  .text"], yx(0, 3));

        run_editor("  text", "  .text\n", cb, ob);
    }

    #[test]
    fn test_move_page_down_up() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(linecol(0, 0), &["1", "2", "3", "4", "5", "6", "7", "8", "9"], yx(0, 0));

        cb.add_input_keys(&[Key::PageDown]);
        ob = ob.quick_refresh(linecol(8, 0), yx(8, 0));

        cb.add_input_keys(&[Key::PageDown]);
        ob = ob.refresh(
            linecol(16, 0),
            &["9", "10", "11", "12", "13", "14", "15", "16", "17"],
            yx(8, 0),
        );

        cb.add_input_keys(&[Key::PageDown]);
        ob = ob.refresh(
            linecol(19, 0),
            &["12", "13", "14", "15", "16", "17", "18", "19", "20"],
            yx(8, 0),
        );

        cb.add_input_keys(&[Key::PageDown]);
        ob = ob.quick_refresh(linecol(19, 0), yx(8, 0));

        cb.add_input_keys(&[Key::PageUp]);
        ob = ob.quick_refresh(linecol(11, 0), yx(0, 0));

        cb.add_input_keys(&[Key::PageUp]);
        ob = ob.refresh(linecol(3, 0), &["4", "5", "6", "7", "8", "9", "10", "11", "12"], yx(0, 0));

        cb.add_input_keys(&[Key::PageUp]);
        ob = ob.refresh(linecol(0, 0), &["1", "2", "3", "4", "5", "6", "7", "8", "9"], yx(0, 0));

        cb.add_input_keys(&[Key::PageUp]);
        ob = ob.quick_refresh(linecol(0, 0), yx(0, 0));

        run_editor(
            "1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n11\n12\n13\n14\n15\n16\n17\n18\n19\n20\n",
            "1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n11\n12\n13\n14\n15\n16\n17\n18\n19\n20\n",
            cb,
            ob,
        );
    }

    #[test]
    fn test_tab_append() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(linecol(0, 0), &[""], yx(0, 0));

        cb.add_input_keys(&[Key::Tab]);
        ob = ob.set_dirty();
        ob = ob.add(CapturedOut::Write("    ".to_string()));
        ob = ob.quick_refresh(linecol(0, 4), yx(0, 4));

        cb.add_input_chars("x");
        ob = ob.add(CapturedOut::Write("x".to_string()));
        ob = ob.quick_refresh(linecol(0, 5), yx(0, 5));

        cb.add_input_keys(&[Key::Tab]);
        ob = ob.add(CapturedOut::Write("   ".to_string()));
        ob = ob.quick_refresh(linecol(0, 8), yx(0, 8));

        run_editor("", "    x   \n", cb, ob);
    }

    #[test]
    fn test_tab_existing_content() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(linecol(0, 0), &["."], yx(0, 0));

        cb.add_input_keys(&[Key::Tab]);
        ob = ob.set_dirty();
        ob = ob.refresh(linecol(0, 4), &["    ."], yx(0, 4));

        cb.add_input_keys(&[Key::Tab]);
        ob = ob.refresh(linecol(0, 8), &["        ."], yx(0, 8));

        run_editor(".", "        .\n", cb, ob);
    }

    #[test]
    fn test_tab_remove_empty_line() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(linecol(0, 0), &["          "], yx(0, 0));

        cb.add_input_keys(&[Key::End]);
        ob = ob.quick_refresh(linecol(0, 10), yx(0, 10));

        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.set_dirty();
        ob = ob.add(CapturedOut::HideCursor);
        ob = ob.add(CapturedOut::Clear(ClearType::PreviousChar));
        ob = ob.add(CapturedOut::Clear(ClearType::PreviousChar));
        ob = ob.add(CapturedOut::ShowCursor);
        ob = ob.quick_refresh(linecol(0, 8), yx(0, 8));

        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.add(CapturedOut::HideCursor);
        ob = ob.add(CapturedOut::Clear(ClearType::PreviousChar));
        ob = ob.add(CapturedOut::Clear(ClearType::PreviousChar));
        ob = ob.add(CapturedOut::Clear(ClearType::PreviousChar));
        ob = ob.add(CapturedOut::Clear(ClearType::PreviousChar));
        ob = ob.add(CapturedOut::ShowCursor);
        ob = ob.quick_refresh(linecol(0, 4), yx(0, 4));

        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.add(CapturedOut::HideCursor);
        ob = ob.add(CapturedOut::Clear(ClearType::PreviousChar));
        ob = ob.add(CapturedOut::Clear(ClearType::PreviousChar));
        ob = ob.add(CapturedOut::Clear(ClearType::PreviousChar));
        ob = ob.add(CapturedOut::Clear(ClearType::PreviousChar));
        ob = ob.add(CapturedOut::ShowCursor);
        ob = ob.quick_refresh(linecol(0, 0), yx(0, 0));

        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.quick_refresh(linecol(0, 0), yx(0, 0));

        run_editor("          ", "\n", cb, ob);
    }

    #[test]
    fn test_tab_remove_before_some_text() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(linecol(0, 0), &["          aligned"], yx(0, 0));

        for i in 0..10 {
            cb.add_input_keys(&[Key::ArrowRight]);
            ob = ob.quick_refresh(linecol(0, i + 1), yx(0, u16::try_from(i + 1).unwrap()));
        }

        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.set_dirty();
        ob = ob.refresh(linecol(0, 8), &["        aligned"], yx(0, 8));

        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.refresh(linecol(0, 4), &["    aligned"], yx(0, 4));

        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.refresh(linecol(0, 0), &["aligned"], yx(0, 0));

        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.quick_refresh(linecol(0, 0), yx(0, 0));

        run_editor("          aligned", "aligned\n", cb, ob);
    }

    #[test]
    fn test_move_preserves_insertion_column() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(linecol(0, 0), &["longer", "a", "longer", "b"], yx(0, 0));

        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.quick_refresh(linecol(0, 1), yx(0, 1));

        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.quick_refresh(linecol(0, 2), yx(0, 2));

        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.quick_refresh(linecol(0, 3), yx(0, 3));

        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.quick_refresh(linecol(0, 4), yx(0, 4));

        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(linecol(1, 1), yx(1, 1));

        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(linecol(2, 4), yx(2, 4));

        cb.add_input_keys(&[Key::Char('X')]);
        ob = ob.set_dirty();
        ob = ob.refresh(linecol(2, 5), &["longer", "a", "longXer", "b"], yx(2, 5));

        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(linecol(3, 1), yx(3, 1));

        cb.add_input_keys(&[Key::Char('Z')]);
        ob = ob.add(CapturedOut::Write("Z".to_string()));
        ob = ob.quick_refresh(linecol(3, 2), yx(3, 2));

        run_editor("longer\na\nlonger\nb\n", "longer\na\nlongXer\nbZ\n", cb, ob);
    }

    #[test]
    fn test_move_down_preserves_insertion_column_with_horizontal_scrolling() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(
            linecol(0, 0),
            &[
                "this is a line of text with more than 40",
                "short",
                "a",
                "",
                "another line of text with more than 40 c",
            ],
            yx(0, 0),
        );

        // Move the cursor to the right boundary.
        for col in 0u16..39u16 {
            cb.add_input_keys(&[Key::ArrowRight]);
            ob = ob.quick_refresh(linecol(0, usize::from(col) + 1), yx(0, col + 1));
        }

        // Push the insertion point over the right boundary to cause scrolling.
        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.refresh(
            linecol(0, 40),
            &[
                "his is a line of text with more than 40 ",
                "hort",
                "",
                "",
                "nother line of text with more than 40 ch",
            ],
            yx(0, 39),
        );
        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.refresh(
            linecol(0, 41),
            &[
                "is is a line of text with more than 40 c",
                "ort",
                "",
                "",
                "other line of text with more than 40 cha",
            ],
            yx(0, 39),
        );

        // Move down to a shorter line whose end character is still visible. No scrolling.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(linecol(1, 5), yx(1, 3));

        // Move down to a shorter line that's not visible but for which insertion can still happen
        // without scrolling.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(
            linecol(2, 1),
            &[
                "his is a line of text with more than 40 ",
                "hort",
                "",
                "",
                "nother line of text with more than 40 ch",
            ],
            yx(2, 0),
        );

        // Move down to an empty line that requires horizontal scrolling for proper insertion.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(
            linecol(3, 0),
            &[
                "this is a line of text with more than 40",
                "short",
                "a",
                "",
                "another line of text with more than 40 c",
            ],
            yx(3, 0),
        );

        // Move down to the last line, which is long again and thus needs scrolling to the right to
        // make the insertion point visible.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(
            linecol(4, 41),
            &[
                "is is a line of text with more than 40 c",
                "ort",
                "",
                "",
                "other line of text with more than 40 cha",
            ],
            yx(4, 39),
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
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(
            linecol(0, 0),
            &[
                "this is a line of text with more than 40",
                "",
                "a",
                "short",
                "another line of text with more than 40 c",
            ],
            yx(0, 0),
        );

        // Move to the last line.
        for i in 0u16..4u16 {
            cb.add_input_keys(&[Key::ArrowDown]);
            ob = ob.quick_refresh(linecol(usize::from(i + 1), 0), yx(i + 1, 0));
        }

        // Move the cursor to the right boundary.
        for col in 0u16..39u16 {
            cb.add_input_keys(&[Key::ArrowRight]);
            ob = ob.quick_refresh(linecol(4, usize::from(col + 1)), yx(4, col + 1));
        }

        // Push the insertion point over the right boundary to cause scrolling.
        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.refresh(
            linecol(4, 40),
            &[
                "his is a line of text with more than 40 ",
                "",
                "",
                "hort",
                "nother line of text with more than 40 ch",
            ],
            yx(4, 39),
        );
        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.refresh(
            linecol(4, 41),
            &[
                "is is a line of text with more than 40 c",
                "",
                "",
                "ort",
                "other line of text with more than 40 cha",
            ],
            yx(4, 39),
        );

        // Move up to a shorter line whose end character is still visible. No scrolling.
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(linecol(3, 5), yx(3, 3));

        // Move up to a shorter line that's not visible but for which insertion can still happen
        // without scrolling.
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.refresh(
            linecol(2, 1),
            &[
                "his is a line of text with more than 40 ",
                "",
                "",
                "hort",
                "nother line of text with more than 40 ch",
            ],
            yx(2, 0),
        );

        // Move up to an empty line that requires horizontal scrolling for proper insertion.
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.refresh(
            linecol(1, 0),
            &[
                "this is a line of text with more than 40",
                "",
                "a",
                "short",
                "another line of text with more than 40 c",
            ],
            yx(1, 0),
        );

        // Move up to the first line, which is long again and thus needs scrolling to the right to
        // make the insertion point visible.
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.refresh(
            linecol(0, 41),
            &[
                "is is a line of text with more than 40 c",
                "",
                "",
                "ort",
                "other line of text with more than 40 cha",
            ],
            yx(0, 39),
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
        cb.set_size_chars(yx(10, 40));
        let mut ob = OutputBuilder::new(yx(10, 40));
        ob = ob.refresh(linecol(0, 0), &["ab", "", "xyz"], yx(0, 0));

        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(linecol(1, 0), yx(1, 0));

        // Insert characters until the screen's right boundary.
        for (col, ch) in "123456789012345678901234567890123456789".chars().enumerate() {
            cb.add_input_keys(&[Key::Char(ch)]);
            ob = ob.set_dirty();
            let mut buf = [0u8; 4];
            ob = ob.add(CapturedOut::Write(ch.encode_utf8(&mut buf).to_string()));
            ob = ob.quick_refresh(linecol(1, col + 1), yx(1, u16::try_from(col + 1).unwrap()));
        }

        // Push the insertion line over the right boundary and test that surrounding lines scroll as
        // well.
        cb.add_input_keys(&[Key::Char('A')]);
        ob = ob.refresh(
            linecol(1, 40),
            &["b", "23456789012345678901234567890123456789A", "yz"],
            yx(1, 39),
        );
        cb.add_input_keys(&[Key::Char('B')]);
        ob = ob.refresh(
            linecol(1, 41),
            &["", "3456789012345678901234567890123456789AB", "z"],
            yx(1, 39),
        );
        cb.add_input_keys(&[Key::Char('C')]);
        ob = ob.refresh(
            linecol(1, 42),
            &["", "456789012345678901234567890123456789ABC", ""],
            yx(1, 39),
        );

        // Move back a few characters, without pushing over the left boundary, and then insert two
        // characters: one will cause the insertion line to fill up the empty space left by the
        // cursor and the other will cause the view of the insertion line to be truncated on the
        // right side.
        for (file_col, cursor_col) in &[(41, 38), (40, 37), (39, 36)] {
            cb.add_input_keys(&[Key::ArrowLeft]);
            ob = ob.quick_refresh(linecol(1, *file_col), yx(1, *cursor_col));
        }
        cb.add_input_keys(&[Key::Char('D')]);
        ob = ob.refresh(
            linecol(1, 40),
            &["", "456789012345678901234567890123456789DABC", ""],
            yx(1, 37),
        );
        cb.add_input_keys(&[Key::Char('E')]);
        ob = ob.refresh(
            linecol(1, 41),
            &["", "456789012345678901234567890123456789DEAB", ""],
            yx(1, 38),
        );

        // Delete a few characters to restore the overflow part of the insertion line.
        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.refresh(
            linecol(1, 40),
            &["", "456789012345678901234567890123456789DABC", ""],
            yx(1, 37),
        );
        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.refresh(
            linecol(1, 39),
            &["", "456789012345678901234567890123456789ABC", ""],
            yx(1, 36),
        );
        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.refresh(
            linecol(1, 38),
            &["", "45678901234567890123456789012345678ABC", ""],
            yx(1, 35),
        );

        // Move back to the beginning of the line to see surrounding lines reappear.
        for col in 0u16..35u16 {
            cb.add_input_keys(&[Key::ArrowLeft]);
            ob = ob.quick_refresh(linecol(1, usize::from(37 - col)), yx(1, 34 - col));
        }
        cb.add_input_keys(&[Key::ArrowLeft]);
        ob = ob.refresh(
            linecol(1, 2),
            &["", "345678901234567890123456789012345678ABC", "z"],
            yx(1, 0),
        );
        cb.add_input_keys(&[Key::ArrowLeft]);
        ob = ob.refresh(
            linecol(1, 1),
            &["b", "2345678901234567890123456789012345678ABC", "yz"],
            yx(1, 0),
        );
        cb.add_input_keys(&[Key::ArrowLeft]);
        ob = ob.refresh(
            linecol(1, 0),
            &["ab", "12345678901234567890123456789012345678AB", "xyz"],
            yx(1, 0),
        );

        run_editor("ab\n\nxyz\n", "ab\n12345678901234567890123456789012345678ABC\nxyz\n", cb, ob);
    }

    #[test]
    fn test_vertical_scrolling() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(5, 40));
        let mut ob = OutputBuilder::new(yx(5, 40));
        ob = ob.refresh(linecol(0, 0), &["abc", "", "d", "e"], yx(0, 0));

        // Move to the last line.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(linecol(1, 0), yx(1, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(linecol(2, 0), yx(2, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(linecol(3, 0), yx(3, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(linecol(4, 0), &["", "d", "e", ""], yx(3, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(linecol(5, 0), &["d", "e", "", "fg"], yx(3, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(linecol(6, 0), &["e", "", "fg", "hij"], yx(3, 0));

        // Attempting to push through the end of the file does nothing.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(linecol(6, 0), yx(3, 0));

        // Go back up to the first line.
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(linecol(5, 0), yx(2, 0));
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(linecol(4, 0), yx(1, 0));
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(linecol(3, 0), yx(0, 0));
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.refresh(linecol(2, 0), &["d", "e", "", "fg"], yx(0, 0));
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.refresh(linecol(1, 0), &["", "d", "e", ""], yx(0, 0));
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.refresh(linecol(0, 0), &["abc", "", "d", "e"], yx(0, 0));

        // Attempting to push through the beginning of the file does nothing.
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(linecol(0, 0), yx(0, 0));

        run_editor("abc\n\nd\ne\n\nfg\nhij\n", "abc\n\nd\ne\n\nfg\nhij\n", cb, ob);
    }

    #[test]
    fn test_vertical_scrolling_when_splitting_last_visible_line() {
        let mut cb = MockConsole::default();
        cb.set_size_chars(yx(4, 40));
        let mut ob = OutputBuilder::new(yx(4, 40));
        ob = ob.refresh(linecol(0, 0), &["first", "second", "thirdfourth"], yx(0, 0));

        // Move to the desired split point.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(linecol(1, 0), yx(1, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(linecol(2, 0), yx(2, 0));
        for i in 0.."third".len() {
            cb.add_input_keys(&[Key::ArrowRight]);
            ob = ob.quick_refresh(linecol(2, i + 1), yx(2, u16::try_from(i + 1).unwrap()));
        }

        // Split the last visible line.
        cb.add_input_keys(&[Key::NewLine]);
        ob = ob.set_dirty();
        ob = ob.refresh(linecol(3, 0), &["second", "third", "fourth"], yx(2, 0));

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
        cb.set_size_chars(yx(4, 40));
        let mut ob = OutputBuilder::new(yx(4, 40));
        ob = ob.refresh(
            linecol(0, 0),
            &["first", "second", "this is a line of text with more than 40"],
            yx(0, 0),
        );

        // Move to the desired split point.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(linecol(1, 0), yx(1, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(linecol(2, 0), yx(2, 0));
        for i in 0u16..39u16 {
            cb.add_input_keys(&[Key::ArrowRight]);
            ob = ob.quick_refresh(linecol(2, usize::from(i + 1)), yx(2, i + 1));
        }
        cb.add_input_keys(&[Key::ArrowRight]);
        ob = ob.refresh(
            linecol(2, 40),
            &["irst", "econd", "his is a line of text with more than 40 "],
            yx(2, 39),
        );

        // Split the last visible line.
        cb.add_input_keys(&[Key::NewLine]);
        ob = ob.set_dirty();
        ob = ob.refresh(
            linecol(3, 0),
            &["second", "this is a line of text with more than 40", " characters"],
            yx(2, 0),
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
        cb.set_size_chars(yx(4, 40));
        let mut ob = OutputBuilder::new(yx(4, 40));
        ob = ob.refresh(linecol(0, 0), &["first", "second", "third"], yx(0, 0));

        // Move down until a couple of lines scroll up.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(linecol(1, 0), yx(1, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(linecol(2, 0), yx(2, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(linecol(3, 0), &["second", "third", "fourth"], yx(2, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(linecol(4, 0), &["third", "fourth", "fifth"], yx(2, 0));

        // Move back up to the first visible line, without scrolling.
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(linecol(3, 0), yx(1, 0));
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(linecol(2, 0), yx(0, 0));

        // Join first visible line with previous, which should scroll contents up.
        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.set_dirty();
        ob = ob.refresh(linecol(1, 6), &["secondthird", "fourth", "fifth"], yx(0, 6));

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
        cb.set_size_chars(yx(4, 40));
        let mut ob = OutputBuilder::new(yx(4, 40));
        ob = ob.refresh(
            linecol(0, 0),
            &["first", "this is a line of text with more than 40", "third"],
            yx(0, 0),
        );

        // Move down until a couple of lines scroll up.
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(linecol(1, 0), yx(1, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.quick_refresh(linecol(2, 0), yx(2, 0));
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(
            linecol(3, 0),
            &["this is a line of text with more than 40", "third", "fourth"],
            yx(2, 0),
        );
        cb.add_input_keys(&[Key::ArrowDown]);
        ob = ob.refresh(linecol(4, 0), &["third", "fourth", "quite a long line"], yx(2, 0));

        // Move back up to the first visible line, without scrolling.
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(linecol(3, 0), yx(1, 0));
        cb.add_input_keys(&[Key::ArrowUp]);
        ob = ob.quick_refresh(linecol(2, 0), yx(0, 0));

        // Join first visible line with previous, which should scroll contents up and right.
        cb.add_input_keys(&[Key::Backspace]);
        ob = ob.set_dirty();
        ob = ob.refresh(
            linecol(1, 51),
            &["ne of text with more than 40 characterst", "", " line"],
            yx(0, 39),
        );

        run_editor(
            "first\nthis is a line of text with more than 40 characters\nthird\nfourth\nquite a long line\n",
            "first\nthis is a line of text with more than 40 charactersthird\nfourth\nquite a long line\n",
            cb,
            ob,
        );
    }
}
