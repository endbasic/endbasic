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

//! Console representation and manipulation.

use async_trait::async_trait;
use std::io;

mod cmds;
pub(crate) use cmds::add_all;
mod format;
pub(crate) use format::refill_and_print;
mod readline;
pub use readline::read_line;
pub(crate) use readline::read_line_secure;

/// Decoded key presses as returned by the console.
#[derive(Clone, Debug)]
pub enum Key {
    /// The cursor down key.
    ArrowDown,

    /// The cursor left key.
    ArrowLeft,

    /// The cursor right key.
    ArrowRight,

    /// The cursor up key.
    ArrowUp,

    /// Deletes the previous character.
    Backspace,

    /// Accepts the current line.
    CarriageReturn,

    /// A printable character.
    Char(char),

    /// Indicates a request for termination (e.g. `Ctrl-D`).
    Eof,

    /// The escape key.
    Escape,

    /// Indicates a request for interrupt (e.g. `Ctrl-C`).
    // TODO(jmmv): This (and maybe Eof too) should probably be represented as a more generic
    // Control(char) value so that we can represent other control sequences and allow the logic in
    // here to determine what to do with each.
    Interrupt,

    /// Accepts the current line.
    NewLine,

    /// An unknown character or sequence. The text describes what went wrong.
    Unknown(String),
}

/// Indicates what part of the console to clear on a `Console::clear()` call.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ClearType {
    /// Clears the whole console and moves the cursor to the top left corner.
    All,

    /// Clears only the current line without moving the cursor.
    CurrentLine,

    /// Clears from the cursor position to the end of the line without moving the cursor.
    UntilNewLine,
}

/// Represents a position in the console, using character-based coordinates.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CharsXY {
    /// The column number, starting from zero.
    pub x: usize,

    /// The row number, starting from zero.
    pub y: usize,
}

impl std::ops::Sub for CharsXY {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        CharsXY { x: self.x - other.x, y: self.y - other.y }
    }
}

/// Hooks to implement the commands that manipulate the console.
#[async_trait(?Send)]
pub trait Console {
    /// Clears the part of the console given by `how`.
    fn clear(&mut self, how: ClearType) -> io::Result<()>;

    /// Sets the console's foreground and background colors to `fg` and `bg`.
    ///
    /// If any of the colors is `None`, the color is left unchanged.
    fn color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()>;

    /// Enters the alternate console.
    // TODO(jmmv): This API leads to misuse as callers can forget to leave the alternate console.
    fn enter_alt(&mut self) -> io::Result<()>;

    /// Hides the cursor.
    // TODO(jmmv): This API leads to misuse as callers can forget to show the cursor again.
    fn hide_cursor(&mut self) -> io::Result<()>;

    /// Returns true if the console is attached to an interactive terminal.  This controls whether
    /// reading a line echoes back user input, for example.
    fn is_interactive(&self) -> bool;

    /// Leaves the alternate console.
    fn leave_alt(&mut self) -> io::Result<()>;

    /// Moves the cursor to the given position, which must be within the screen.
    fn locate(&mut self, pos: CharsXY) -> io::Result<()>;

    /// Moves the cursor within the line.  Positive values move right, negative values move left.
    fn move_within_line(&mut self, off: i16) -> io::Result<()>;

    /// Writes `text` to the console, followed by a newline or CRLF pair depending on the needs of
    /// the console to advance a line.
    // TODO(jmmv): Remove this in favor of write?
    fn print(&mut self, text: &str) -> io::Result<()>;

    /// Waits for and returns the next key press.
    async fn read_key(&mut self) -> io::Result<Key>;

    /// Shows the cursor.
    fn show_cursor(&mut self) -> io::Result<()>;

    /// Queries the size of the console.
    ///
    /// The returned position represents the first row and column that lay *outside* of the console.
    fn size(&self) -> io::Result<CharsXY>;

    /// Writes the raw `bytes` into the console.
    fn write(&mut self, bytes: &[u8]) -> io::Result<()>;
}
