// EndBASIC
// Copyright 2025 Julio Merino
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

//! SPI bus implementation using rppal.

use endbasic_std::spi::{SpiBus, SpiMode};
use rppal::spi::{self, Bus, SlaveSelect, Spi};
use std::io::Write;
use std::path::Path;
use std::{fs, io};

/// Path to the configuration file containing the maximum SPI transfer size.
const SPIDEV_BUFSIZ_PATH: &str = "/sys/module/spidev/parameters/bufsiz";

/// Converts an SPI error to an IO error.
fn spi_error_to_io_error(e: spi::Error) -> io::Error {
    match e {
        spi::Error::Io(e) => e,
        e => io::Error::new(io::ErrorKind::InvalidInput, e.to_string()),
    }
}

/// Queries the maximum SPI transfer size from `path`.  If `path` is not provided, defaults to
/// `SPIDEV_BUFSIZ_PATH`.
fn query_spi_bufsiz(path: Option<&Path>) -> io::Result<usize> {
    let path = path.unwrap_or(Path::new(SPIDEV_BUFSIZ_PATH));

    let content = match fs::read_to_string(path) {
        Ok(content) => content,
        Err(e) => {
            return Err(io::Error::new(
                e.kind(),
                format!("Failed to read {}: {}", path.display(), e),
            ));
        }
    };

    let content = content.trim_end();

    match content.parse::<usize>() {
        Ok(i) => Ok(i),
        Err(e) => Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("Failed to read {}: invalid content: {}", path.display(), e),
        )),
    }
}

/// An implementation of an `SpiBus` using rppal.
pub struct RppalSpiBus {
    spi: Spi,
    bufsiz: usize,
}

/// Factory function to open an `RppalSpiBus`.
pub fn spi_bus_open(bus: u8, slave: u8, clock_hz: u32, mode: SpiMode) -> io::Result<RppalSpiBus> {
    let bus = match bus {
        0 => Bus::Spi0,
        _ => return Err(io::Error::new(io::ErrorKind::InvalidInput, "Only bus 0 is supported")),
    };

    let slave = match slave {
        0 => SlaveSelect::Ss0,
        _ => return Err(io::Error::new(io::ErrorKind::InvalidInput, "Only slave 0 is supported")),
    };

    let mode = match mode {
        SpiMode::Mode0 => spi::Mode::Mode0,
        SpiMode::Mode1 => spi::Mode::Mode1,
        SpiMode::Mode2 => spi::Mode::Mode2,
        SpiMode::Mode3 => spi::Mode::Mode3,
    };

    let spi = Spi::new(bus, slave, clock_hz, mode).map_err(spi_error_to_io_error)?;

    let bufsiz = query_spi_bufsiz(None)?;

    Ok(RppalSpiBus { spi, bufsiz })
}

impl Write for RppalSpiBus {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.spi.write(buf).map_err(spi_error_to_io_error)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl SpiBus for RppalSpiBus {
    fn max_size(&self) -> usize {
        self.bufsiz
    }
}
