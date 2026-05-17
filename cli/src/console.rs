// EndBASIC
// Copyright 2026 Julio Merino
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

//! Logic to instantiate a console for the CLI.

use async_channel::Sender;
use endbasic_std::Signal;
use endbasic_std::console::{Console, ConsoleFactory, ConsoleSpec};
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

/// Console factory for a terminal-backed console.
struct TextConsoleFactory {}

impl ConsoleFactory for TextConsoleFactory {
    #[cfg(feature = "crossterm")]
    fn build(self: Box<Self>, signals_tx: Sender<Signal>) -> io::Result<Rc<RefCell<dyn Console>>> {
        Ok(Rc::from(RefCell::from(endbasic_terminal::TerminalConsole::from_stdio(signals_tx)?)))
    }

    #[cfg(not(feature = "crossterm"))]
    fn build(self: Box<Self>, signals_tx: Sender<Signal>) -> io::Result<Rc<RefCell<dyn Console>>> {
        Ok(Rc::from(RefCell::from(endbasic_std::console::TrivialConsole::default())))
    }
}

/// Instantiates a console factory for a terminal-backed console.
fn setup_text_console() -> Box<dyn ConsoleFactory> {
    Box::from(TextConsoleFactory {})
}

/// Instantiates a console factory for an SDL-backed console with the given `spec`.
#[cfg(feature = "sdl")]
pub fn setup_sdl_console(spec: &mut ConsoleSpec) -> io::Result<Box<dyn ConsoleFactory>> {
    let factory =
        endbasic_sdl::SdlConsoleFactory::new(spec, &endbasic_std::gfx::lcd::fonts::Fonts::all())?;
    Ok(Box::from(factory))
}

/// Instantiates a console factory for an SDL-backed console with the given `spec`.
#[cfg(not(feature = "sdl"))]
pub fn setup_sdl_console(_spec: &mut ConsoleSpec) -> io::Result<Box<dyn ConsoleFactory>> {
    // TODO(jmmv): Make this io::ErrorKind::Unsupported when our MSRV allows it.
    Err(io::Error::new(io::ErrorKind::InvalidInput, "SDL support not compiled in"))
}

/// Instantiates a console factory for an ST7735s-backed console with the given `spec`.
#[cfg(feature = "rpi")]
fn setup_st7735s_console(spec: &mut ConsoleSpec) -> io::Result<Box<dyn ConsoleFactory>> {
    let factory = endbasic_st7735s::St7735sConsoleFactory::new(
        endbasic_rpi::RppalPins::default(),
        endbasic_rpi::spi_bus_open,
        endbasic_terminal::TerminalConsole::from_stdio,
        spec,
        &endbasic_std::gfx::lcd::fonts::Fonts::all(),
    )?;
    Ok(Box::from(factory))
}

/// Instantiates a console factory for an ST7735s-backed console with the given `spec`.
#[cfg(not(feature = "rpi"))]
fn setup_st7735s_console(_spec: &mut ConsoleSpec) -> io::Result<Box<dyn ConsoleFactory>> {
    Err(io::Error::new(io::ErrorKind::InvalidInput, "ST7735S support not compiled in"))
}

/// Sets up the console.
pub fn setup_console(console_spec: Option<&str>) -> io::Result<Box<dyn ConsoleFactory>> {
    let mut console_spec = ConsoleSpec::init(console_spec.unwrap_or("text"));
    let console: Box<dyn ConsoleFactory> = match console_spec.driver {
        "sdl" => setup_sdl_console(&mut console_spec)?,
        "st7735s" => setup_st7735s_console(&mut console_spec)?,
        "text" => setup_text_console(),
        driver => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("Unknown console driver {}", driver),
            ));
        }
    };
    console_spec.finish().map_err(|e| {
        io::Error::new(io::ErrorKind::InvalidInput, format!("Invalid --console flag: {}", e))
    })?;
    Ok(console)
}
