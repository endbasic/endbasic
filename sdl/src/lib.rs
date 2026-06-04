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
use endbasic_std::console::{Console, ConsoleFactory, ConsoleHost, ConsoleSpec, Resolution};
use endbasic_std::gfx::lcd::fonts::{FONT_VGA8X16, Font, Fonts};
use std::cell::RefCell;
use std::io;
use std::num::NonZeroU32;
use std::rc::Rc;
use std::sync::mpsc::{self, Receiver, SyncSender};

mod console;
use console::SdlConsole;

mod host;
use host::SdlConsoleHost;

/// Default resolution to use when none is provided.
const DEFAULT_RESOLUTION_PIXELS: (u32, u32) = (800, 600);

/// Converts a flat string error message to an `io::Error`.
fn string_error_to_io_error(e: String) -> io::Error {
    io::Error::other(e)
}

/// Console factory for an SDL-backed graphical console.
struct SdlConsoleFactory {
    request_tx: SyncSender<host::Request>,
    response_rx: Receiver<host::Response>,
    on_key_rx: Receiver<endbasic_std::console::Key>,
}

impl SdlConsoleFactory {
    /// Creates a new SDL console factory from prewired channels.
    fn new(
        request_tx: SyncSender<host::Request>,
        response_rx: Receiver<host::Response>,
        on_key_rx: Receiver<endbasic_std::console::Key>,
    ) -> Self {
        Self { request_tx, response_rx, on_key_rx }
    }

    /// Constructs the SDL console.
    fn build_console(self) -> io::Result<SdlConsole> {
        SdlConsole::new(self.request_tx, self.response_rx, self.on_key_rx)
    }
}

impl ConsoleFactory for SdlConsoleFactory {
    fn build(self: Box<Self>) -> io::Result<Rc<RefCell<dyn Console>>> {
        let console = self.build_console()?;
        Ok(Rc::from(RefCell::from(console)))
    }
}

/// Creates a new SDL console host and a factory for the client.
pub(crate) fn new_console_pair(
    resolution: Resolution,
    default_fg_color: Option<u8>,
    default_bg_color: Option<u8>,
    font: &'static Font,
    signals_tx: Sender<Signal>,
) -> (SdlConsoleHost, SdlConsoleFactory) {
    let (request_tx, request_rx) = mpsc::sync_channel(1);
    let (response_tx, response_rx) = mpsc::sync_channel(1);
    let (on_key_tx, on_key_rx) = mpsc::channel();
    let host = SdlConsoleHost {
        resolution,
        default_fg_color,
        default_bg_color,
        font,
        request_rx,
        response_tx,
        on_key_tx,
        signals_tx,
    };
    let factory = SdlConsoleFactory::new(request_tx, response_rx, on_key_rx);
    (host, factory)
}

/// Creates an SDL console host and factory based on the given `spec`.
pub fn setup(
    spec: &mut ConsoleSpec<'_>,
    signals_tx: Sender<Signal>,
    fonts: &Fonts,
) -> io::Result<(Box<dyn ConsoleHost>, Box<dyn ConsoleFactory>)> {
    let resolution: Resolution = spec.take_keyed_flag("resolution")?.unwrap_or_else(|| {
        let width = NonZeroU32::new(DEFAULT_RESOLUTION_PIXELS.0).unwrap();
        let height = NonZeroU32::new(DEFAULT_RESOLUTION_PIXELS.1).unwrap();
        Resolution::Windowed((width, height))
    });

    let default_fg_color = spec.take_keyed_flag::<u8>("fg_color")?;
    let default_bg_color = spec.take_keyed_flag::<u8>("bg_color")?;

    let font_name = spec.take_keyed_flag_str("font").unwrap_or(FONT_VGA8X16.name);
    let font = fonts.get(font_name)?;

    let (host, factory) =
        new_console_pair(resolution, default_fg_color, default_bg_color, font, signals_tx);
    Ok((Box::from(host), Box::from(factory)))
}
