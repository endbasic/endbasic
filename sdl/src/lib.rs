// EndBASIC
// Copyright 2021 Julio Merino
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

//! SDL2-based graphics terminal emulator.

use async_channel::Sender;
use endbasic_std::Signal;
use endbasic_std::console::{Console, ConsoleFactory, ConsoleSpec, Resolution};
use endbasic_std::gfx::lcd::fonts::{FONT_VGA8X16, Font, Fonts};
use std::cell::RefCell;
use std::io;
use std::num::NonZeroU32;
use std::rc::Rc;

mod console;
mod host;

/// Default resolution to use when none is provided.
const DEFAULT_RESOLUTION_PIXELS: (u32, u32) = (800, 600);

/// Converts a flat string error message to an `io::Error`.
fn string_error_to_io_error(e: String) -> io::Error {
    io::Error::other(e)
}

/// Console factory for an SDL-backed graphical console.
pub struct SdlConsoleFactory {
    resolution: Resolution,
    default_fg_color: Option<u8>,
    default_bg_color: Option<u8>,
    font: &'static Font,
}

impl SdlConsoleFactory {
    /// Creates an SDL console factory based on the given `spec`.
    pub fn new(spec: &mut ConsoleSpec<'_>, fonts: &Fonts) -> io::Result<Self> {
        let resolution: Resolution = spec.take_keyed_flag("resolution")?.unwrap_or_else(|| {
            let width = NonZeroU32::new(DEFAULT_RESOLUTION_PIXELS.0).unwrap();
            let height = NonZeroU32::new(DEFAULT_RESOLUTION_PIXELS.1).unwrap();
            Resolution::Windowed((width, height))
        });

        let default_fg_color = spec.take_keyed_flag::<u8>("fg_color")?;
        let default_bg_color = spec.take_keyed_flag::<u8>("bg_color")?;

        let font_name = spec.take_keyed_flag_str("font").unwrap_or(FONT_VGA8X16.name);
        let font = fonts.get(font_name)?;

        Ok(SdlConsoleFactory { resolution, default_fg_color, default_bg_color, font })
    }
}

impl ConsoleFactory for SdlConsoleFactory {
    fn build(self: Box<Self>, signals_tx: Sender<Signal>) -> io::Result<Rc<RefCell<dyn Console>>> {
        let console = console::SdlConsole::new(
            self.resolution,
            self.default_fg_color,
            self.default_bg_color,
            self.font,
            signals_tx,
        )?;
        Ok(Rc::from(RefCell::from(console)))
    }
}
