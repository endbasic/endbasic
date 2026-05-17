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
use endbasic_std::console::{Console, ConsoleSpec};
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

/// Sets up the console.
pub(crate) fn setup_console(
    console_spec: Option<&str>,
    signals_tx: Sender<Signal>,
) -> io::Result<Rc<RefCell<dyn Console>>> {
    /// Creates the textual console when crossterm support is built in.
    #[cfg(feature = "crossterm")]
    fn setup_text_console(signals_tx: Sender<Signal>) -> io::Result<Rc<RefCell<dyn Console>>> {
        Ok(Rc::from(RefCell::from(endbasic_terminal::TerminalConsole::from_stdio(signals_tx)?)))
    }

    /// Creates the textual console with very basic features when crossterm support is not built in.
    #[cfg(not(feature = "crossterm"))]
    fn setup_text_console(_signals_tx: Sender<Signal>) -> io::Result<Rc<RefCell<dyn Console>>> {
        Ok(Rc::from(RefCell::from(endbasic_std::console::TrivialConsole::default())))
    }

    /// Creates the graphical console when SDL support is built in.
    #[cfg(feature = "sdl")]
    fn setup_sdl_console(
        signals_tx: Sender<Signal>,
        spec: &mut ConsoleSpec,
    ) -> io::Result<Rc<RefCell<dyn Console>>> {
        endbasic_sdl::setup(spec, &endbasic_std::gfx::lcd::fonts::Fonts::all(), signals_tx)
    }

    /// Errors out during the creation of the graphical console when SDL support is not compiled in.
    #[cfg(not(feature = "sdl"))]
    fn setup_sdl_console(
        _signals_tx: Sender<Signal>,
        _spec: &mut ConsoleSpec,
    ) -> io::Result<Rc<RefCell<dyn Console>>> {
        // TODO(jmmv): Make this io::ErrorKind::Unsupported when our MSRV allows it.
        Err(io::Error::new(io::ErrorKind::InvalidInput, "SDL support not compiled in"))
    }

    #[cfg(feature = "rpi")]
    fn setup_st7735s_console(
        signals_tx: Sender<Signal>,
        spec: &mut ConsoleSpec,
    ) -> io::Result<Rc<RefCell<dyn Console>>> {
        let console = endbasic_st7735s::new_console(
            endbasic_rpi::RppalPins::default(),
            endbasic_rpi::spi_bus_open,
            endbasic_terminal::TerminalConsole::from_stdio(signals_tx)?,
            spec,
            &endbasic_std::gfx::lcd::fonts::Fonts::all(),
        )?;
        Ok(Rc::from(RefCell::from(console)))
    }

    #[cfg(not(feature = "rpi"))]
    fn setup_st7735s_console(
        _signals_tx: Sender<Signal>,
        _spec: &mut ConsoleSpec,
    ) -> io::Result<Rc<RefCell<dyn Console>>> {
        Err(io::Error::new(io::ErrorKind::InvalidInput, "ST7735S support not compiled in"))
    }

    let mut console_spec = ConsoleSpec::init(console_spec.unwrap_or("text"));
    let console: Rc<RefCell<dyn Console>> = match console_spec.driver {
        "sdl" => setup_sdl_console(signals_tx, &mut console_spec)?,
        "st7735s" => setup_st7735s_console(signals_tx, &mut console_spec)?,
        "text" => setup_text_console(signals_tx)?,
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
