// EndBASIC
// Copyright 2020 Julio Merino
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

//! Console representation and manipulation.

use crate::Clearable;
use async_trait::async_trait;
use std::cell::RefCell;
use std::collections::VecDeque;
use std::env;
use std::io;
use std::rc::Rc;
use std::str;

mod cmds;
pub(crate) use cmds::add_all;
mod colors;
pub use colors::{AnsiColor, RGB, ansi_color_to_rgb, rgb_to_ansi_color};
pub mod drawing;
mod format;
pub(crate) use format::refill_and_page;
pub use format::refill_and_print;
pub mod graphics;
pub use graphics::GraphicsConsole;
mod linebuffer;
pub use linebuffer::LineBuffer;
mod pager;
pub(crate) use pager::Pager;
mod readline;
pub use readline::{read_line, read_line_secure};
mod spec;
pub use spec::{ConsoleSpec, ParseError, Resolution};
mod trivial;
pub use trivial::TrivialConsole;

/// Decoded key presses as returned by the console.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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

    /// The end key or `Ctrl-E`.
    End,

    /// Indicates a request for termination (e.g. `Ctrl-D`).
    Eof,

    /// The escape key.
    Escape,

    /// Indicates a request for interrupt (e.g. `Ctrl-C`).
    // TODO(jmmv): This (and maybe Eof too) should probably be represented as a more generic
    // Control(char) value so that we can represent other control sequences and allow the logic in
    // here to determine what to do with each.
    Interrupt,

    /// The home key or `Ctrl-A`.
    Home,

    /// Accepts the current line.
    NewLine,

    /// The Page Down key.
    PageDown,

    /// The Page Up key.
    PageUp,

    /// The Tab key.
    Tab,

    /// An unknown character or sequence.
    Unknown,
}

/// Indicates what part of the console to clear on a `Console::clear()` call.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ClearType {
    /// Clears the whole console and moves the cursor to the top left corner.
    All,

    /// Clears only the current line without moving the cursor.
    CurrentLine,

    /// Clears the previous character.
    PreviousChar,

    /// Clears from the cursor position to the end of the line without moving the cursor.
    UntilNewLine,
}

/// Represents a coordinate for character-based console operations.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CharsXY {
    /// The column number, starting from zero.
    pub x: u16,

    /// The row number, starting from zero.
    pub y: u16,
}

impl CharsXY {
    /// Constructs a new coordinate at the given `(x, y)` position.
    pub fn new(x: u16, y: u16) -> Self {
        Self { x, y }
    }
}

/// Represents a coordinate for pixel-based console operations.
///
/// Coordinates can be off-screen, which means they can be negative and/or can exceed the
/// bottom-right margin.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PixelsXY {
    /// The column number.
    pub x: i16,

    /// The row number.
    pub y: i16,
}

impl PixelsXY {
    /// Constructs a new coordinate at the given `(x, y)` position.
    pub fn new(x: i16, y: i16) -> Self {
        Self { x, y }
    }
}

#[cfg(test)]
impl PixelsXY {
    pub(crate) const TOP_LEFT: Self = Self { x: i16::MIN, y: i16::MIN };
    pub(crate) const TOP_RIGHT: Self = Self { x: i16::MAX, y: i16::MIN };
    pub(crate) const BOTTOM_LEFT: Self = Self { x: i16::MIN, y: i16::MAX };
    pub(crate) const BOTTOM_RIGHT: Self = Self { x: i16::MAX, y: i16::MAX };
}

/// Represents a rectangular size in pixels.
#[derive(Clone, Copy, Debug, PartialEq)]
#[non_exhaustive]
pub struct SizeInPixels {
    /// The width in pixels.
    pub width: u16,

    /// The height in pixels.
    pub height: u16,
}

impl SizeInPixels {
    /// Construts a new size in pixels, validating that the quantities are non-zero.
    pub fn new(width: u16, height: u16) -> Self {
        debug_assert!(width > 0, "Zero widths don't make sense");
        debug_assert!(height > 0, "Zero heights don't make sense");
        Self { width, height }
    }
}

#[cfg(test)]
impl SizeInPixels {
    pub(crate) const MAX: Self = Self { width: u16::MAX, height: u16::MAX };
}

/// Hooks to implement the commands that manipulate the console.
#[async_trait(?Send)]
pub trait Console {
    /// Clears the part of the console given by `how`.
    fn clear(&mut self, how: ClearType) -> io::Result<()>;

    /// Gets the console's current foreground and background colors.
    fn color(&self) -> (Option<u8>, Option<u8>);

    /// Sets the console's foreground and background colors to `fg` and `bg`.
    ///
    /// If any of the colors is `None`, the color is left unchanged.
    fn set_color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()>;

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
    ///
    /// The input `text` is not supposed to contain any control characters, such as CR or LF.
    // TODO(jmmv): Remove this in favor of write?
    fn print(&mut self, text: &str) -> io::Result<()>;

    /// Returns the next key press if any is available.
    async fn poll_key(&mut self) -> io::Result<Option<Key>>;

    /// Waits for and returns the next key press.
    async fn read_key(&mut self) -> io::Result<Key>;

    /// Shows the cursor.
    fn show_cursor(&mut self) -> io::Result<()>;

    /// Queries the size of the text console.
    ///
    /// The returned position represents the first row and column that lay *outside* of the console.
    fn size_chars(&self) -> io::Result<CharsXY>;

    /// Queries the size of the graphical console.
    fn size_pixels(&self) -> io::Result<SizeInPixels> {
        Err(io::Error::other("No graphics support in this console"))
    }

    /// Writes the text into the console at the position of the cursor.
    ///
    fn write(&mut self, text: &str) -> io::Result<()>;

    /// Draws the outline of a circle at `_center` with `_radius` using the current drawing color.
    fn draw_circle(&mut self, _center: PixelsXY, _radius: u16) -> io::Result<()> {
        Err(io::Error::other("No graphics support in this console"))
    }

    /// Draws a filled circle at `_center` with `_radius` using the current drawing color.
    fn draw_circle_filled(&mut self, _center: PixelsXY, _radius: u16) -> io::Result<()> {
        Err(io::Error::other("No graphics support in this console"))
    }

    /// Draws a line from `_x1y1` to `_x2y2` using the current drawing color.
    fn draw_line(&mut self, _x1y1: PixelsXY, _x2y2: PixelsXY) -> io::Result<()> {
        Err(io::Error::other("No graphics support in this console"))
    }

    /// Draws a single pixel at `_xy` using the current drawing color.
    fn draw_pixel(&mut self, _xy: PixelsXY) -> io::Result<()> {
        Err(io::Error::other("No graphics support in this console"))
    }

    /// Draws the outline of a polygon using the current drawing color.
    fn draw_poly(&mut self, _points: &[PixelsXY]) -> io::Result<()> {
        Err(io::Error::other("No graphics support in this console"))
    }

    /// Draws a filled polygon using the current drawing color.
    fn draw_poly_filled(&mut self, _points: &[PixelsXY]) -> io::Result<()> {
        Err(io::Error::other("No graphics support in this console"))
    }

    /// Draws the outline of a rectangle from `_x1y1` to `_x2y2` using the current drawing color.
    fn draw_rect(&mut self, _x1y1: PixelsXY, _x2y2: PixelsXY) -> io::Result<()> {
        Err(io::Error::other("No graphics support in this console"))
    }

    /// Draws a filled rectangle from `_x1y1` to `_x2y2` using the current drawing color.
    fn draw_rect_filled(&mut self, _x1y1: PixelsXY, _x2y2: PixelsXY) -> io::Result<()> {
        Err(io::Error::other("No graphics support in this console"))
    }

    /// Draws the outline of a triangle using the current drawing color.
    fn draw_tri(&mut self, _x1y1: PixelsXY, _x2y2: PixelsXY, _x3y3: PixelsXY) -> io::Result<()> {
        Err(io::Error::other("No graphics support in this console"))
    }

    /// Draws a filled triangle using the current drawing color.
    fn draw_tri_filled(
        &mut self,
        _x1y1: PixelsXY,
        _x2y2: PixelsXY,
        _x3y3: PixelsXY,
    ) -> io::Result<()> {
        Err(io::Error::other("No graphics support in this console"))
    }

    /// Returns the color number of the pixel at `_xy` if it is in bounds and exactly mappable.
    fn peek_pixel(&self, _xy: PixelsXY) -> io::Result<Option<u8>> {
        Err(io::Error::other("No graphics support in this console"))
    }

    /// Causes any buffered output to be synced.
    ///
    /// This is a no-op when video syncing is enabled because output is never buffered in that case.
    fn sync_now(&mut self) -> io::Result<()>;

    /// Enables or disables video syncing.
    ///
    /// When enabled, all graphical operations immediately updated the rendering target, which is
    /// useful for interactive behavior because we want to see an immediate response.  When
    /// disabled, all operations are buffered, which is useful for scripts (as otherwise rendering
    /// is too slow).
    ///
    /// Flushes any pending updates when enabled.
    ///
    /// Returns the previous status of the video syncing flag.
    fn set_sync(&mut self, _enabled: bool) -> io::Result<bool>;
}

/// Trait to run the console's host on the main UI thread (if needed).
pub trait ConsoleHost {
    /// Executes the console's host event loop.
    fn run(self: Box<Self>) -> io::Result<()>;
}

/// A console host that does nothing for all consoles which can run on a secondary thread.
pub struct NoopConsoleHost;

impl ConsoleHost for NoopConsoleHost {
    fn run(self: Box<Self>) -> io::Result<()> {
        Ok(())
    }
}

/// Trait for an object that is able to instantiate a console.
///
/// Console objects are not `Send` so we must instantiate them within the thread that runs
/// the REPL.  But in some cases, we need to create the console in a thread that's different than
/// the one that will run it.  The factory allows us to prepare the console elsewhere, passing the
/// Send-safe factory into the REPL thread.
pub trait ConsoleFactory: Send {
    /// Creates a new console and wires it up to inject signals into `signals_tx`.
    fn build(self: Box<Self>) -> io::Result<Rc<RefCell<dyn Console>>>;
}

/// Resets the state of a console in a best-effort manner.
pub(crate) struct ConsoleClearable {
    console: Rc<RefCell<dyn Console>>,
}

impl ConsoleClearable {
    /// Creates a new clearable for `console`.
    pub(crate) fn new(console: Rc<RefCell<dyn Console>>) -> Box<Self> {
        Box::from(Self { console })
    }
}

impl Clearable for ConsoleClearable {
    fn reset_state(&self) {
        let mut console = self.console.borrow_mut();
        let _ = console.leave_alt();
        let _ = console.set_color(None, None);
        let _ = console.show_cursor();
        let _ = console.set_sync(true);
    }
}

/// Checks if a given string has control characters.
pub fn has_control_chars(s: &str) -> bool {
    for ch in s.chars() {
        if ch.is_control() {
            return true;
        }
    }
    false
}

/// Removes control characters from a string to make it suitable for printing.
pub fn remove_control_chars<S: Into<String>>(s: S) -> String {
    let s = s.into();

    // Handle the expected common case first.  We use this function to strip control characters
    // before printing them to the console, and thus we expect such input strings to rarely include
    // control characters.
    if !has_control_chars(&s) {
        return s;
    }

    let mut o = String::with_capacity(s.len());
    for ch in s.chars() {
        if ch.is_control() {
            o.push(' ');
        } else {
            o.push(ch);
        }
    }
    o
}

/// Gets the value of the environment variable `name` and interprets it as a `u16`.  Returns
/// `None` if the variable is not set or if its contents are invalid.
pub fn get_env_var_as_u16(name: &str) -> Option<u16> {
    match env::var_os(name) {
        Some(value) => value.as_os_str().to_string_lossy().parse::<u16>().map(Some).unwrap_or(None),
        None => None,
    }
}

/// Converts a line of text into a collection of keys.
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
            keys.push_back(Key::Unknown);
        }
    }
    keys
}

/// Reads a single key from stdin when not attached to a TTY.  Because characters are not
/// visible to us until a newline is received, this reads complete lines and buffers them in
/// memory inside the given `buffer`.
pub fn read_key_from_stdin(buffer: &mut VecDeque<Key>) -> io::Result<Key> {
    if buffer.is_empty() {
        let mut line = String::new();
        if io::stdin().read_line(&mut line)? == 0 {
            return Ok(Key::Eof);
        }
        *buffer = line_to_keys(line);
    }
    match buffer.pop_front() {
        Some(key) => Ok(key),
        None => Ok(Key::Eof),
    }
}

/// Returns true if the console is too narrow for the standard interface.
///
/// A narrow console is defined as one that cannot fit the welcome message.
pub fn is_narrow(console: &dyn Console) -> bool {
    match console.size_chars() {
        Ok(size) => size.x < 50,
        Err(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_has_control_chars() {
        assert!(!has_control_chars(""));
        assert!(!has_control_chars("foo bar^baz"));

        assert!(has_control_chars("foo\nbar"));
        assert!(has_control_chars("foo\rbar"));
        assert!(has_control_chars("foo\x08bar"));
    }

    #[test]
    fn test_remove_control_chars() {
        assert_eq!("", remove_control_chars(""));
        assert_eq!("foo bar", remove_control_chars("foo bar"));
        assert_eq!("foo  bar baz ", remove_control_chars("foo\r\nbar\rbaz\n"));
    }
}
