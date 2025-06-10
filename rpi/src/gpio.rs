// EndBASIC
// Copyright 2021 Julio Merino
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

//! GPIO implementation for the Raspberry Pi.

use endbasic_std::gpio::{Pin, PinMode, Pins};
use rppal::gpio;
use std::collections::HashMap;
use std::io;

/// Implementation of the EndBASIC GPIO operations for a Raspberry Pi using the rppal library.
#[derive(Default)]
pub struct RppalPins {
    chip: Option<gpio::Gpio>,
    inputs: HashMap<Pin, gpio::InputPin>,
    outputs: HashMap<Pin, gpio::OutputPin>,
}

/// Converts a `gpio::Error` to an `io::Error`.
pub(crate) fn gpio_error_to_io_error(e: gpio::Error) -> io::Error {
    match e {
        gpio::Error::Io(e) => e,
        gpio::Error::PermissionDenied(path) => io::Error::new(
            io::ErrorKind::PermissionDenied,
            format!("Cannot open {}: permission denied", path),
        ),
        gpio::Error::PinNotAvailable(pin) => {
            io::Error::new(io::ErrorKind::InvalidInput, format!("Unknown pin number {}", pin))
        }
        e => io::Error::other(e.to_string()),
    }
}

impl RppalPins {
    /// Gets access to the default GPIO chip and lazily opens it if not yet open.
    fn get_chip(&mut self) -> io::Result<&mut gpio::Gpio> {
        if self.chip.is_none() {
            self.chip = Some(gpio::Gpio::new().map_err(gpio_error_to_io_error)?);
        }
        Ok(self.chip.as_mut().unwrap())
    }
}

impl Pins for RppalPins {
    fn setup(&mut self, pin: Pin, mode: PinMode) -> io::Result<()> {
        self.clear(pin)?;
        let chip = self.get_chip()?;
        let gpio_pin = chip.get(pin.0).map_err(gpio_error_to_io_error)?;
        match mode {
            PinMode::In => {
                self.inputs.insert(pin, gpio_pin.into_input());
            }
            PinMode::InPullDown => {
                self.inputs.insert(pin, gpio_pin.into_input_pulldown());
            }
            PinMode::InPullUp => {
                self.inputs.insert(pin, gpio_pin.into_input_pullup());
            }
            PinMode::Out => {
                self.outputs.insert(pin, gpio_pin.into_output());
            }
        };
        Ok(())
    }

    fn clear(&mut self, pin: Pin) -> io::Result<()> {
        self.inputs.remove(&pin);
        self.outputs.remove(&pin);
        Ok(())
    }

    fn clear_all(&mut self) -> io::Result<()> {
        self.inputs.clear();
        self.outputs.clear();
        Ok(())
    }

    fn read(&mut self, pin: Pin) -> io::Result<bool> {
        if !self.inputs.contains_key(&pin) || self.outputs.contains_key(&pin) {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "Pin not configured for read; use GPIO_SETUP first",
            ));
        }
        let pin = self.inputs.get(&pin).unwrap();
        match pin.read() {
            gpio::Level::High => Ok(true),
            gpio::Level::Low => Ok(false),
        }
    }

    fn write(&mut self, pin: Pin, v: bool) -> io::Result<()> {
        if self.inputs.contains_key(&pin) || !self.outputs.contains_key(&pin) {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "Pin not configured for write; use GPIO_SETUP first",
            ));
        }
        let pin = self.outputs.get_mut(&pin).unwrap();
        if v {
            pin.write(gpio::Level::High);
        } else {
            pin.write(gpio::Level::Low);
        }
        Ok(())
    }
}
