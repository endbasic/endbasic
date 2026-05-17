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

//! Logic to instantiate the GPIO pins for the CLI.

use anyhow::Result;
use endbasic_std::gpio;
use getoptsargs::prelude::bad_usage;
use std::cell::RefCell;
use std::rc::Rc;

/// Creates the rppal GPIO backend when the rpi feature is compiled in.
#[cfg(feature = "rpi")]
fn setup_gpio_pins_rppal() -> Result<Rc<RefCell<dyn gpio::Pins>>> {
    Ok(Rc::new(RefCell::new(endbasic_rpi::RppalPins::default())))
}

/// Errors out for rppal when the rpi feature is not compiled in.
#[cfg(not(feature = "rpi"))]
fn setup_gpio_pins_rppal() -> Result<Rc<RefCell<dyn gpio::Pins>>> {
    Err(bad_usage!("--gpio-pins=rppal requires the rpi feature to be compiled in").into())
}

/// Parses the `--gpio-pins` flag value and constructs the pins backend.
pub(crate) fn setup_gpio_pins(spec: Option<&str>) -> Result<Rc<RefCell<dyn gpio::Pins>>> {
    let spec = if cfg!(feature = "rpi") { spec.unwrap_or("rppal") } else { spec.unwrap_or("noop") };
    match spec {
        "mock" => Ok(Rc::new(RefCell::new(gpio::MockPins::default()))),
        "noop" => Ok(Rc::new(RefCell::new(gpio::NoopPins::default()))),
        "rppal" => setup_gpio_pins_rppal(),
        other => Err(bad_usage!(format!("Unknown --gpio-pins backend: {}", other)).into()),
    }
}
