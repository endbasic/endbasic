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

//! SPI bus abstractions for EndBASIC.

use std::io::{self, Write};

/// Defines the SPI clock polarity and phase.
#[derive(Debug, PartialEq)]
pub enum SpiMode {
    /// CPOL 0, CPHA 0
    Mode0 = 0,
    /// CPOL 0, CPHA 1
    Mode1 = 1,
    /// CPOL 1, CPHA 0
    Mode2 = 2,
    /// CPOL 1, CPHA 1
    Mode3 = 3,
}

/// Factory function to open an SPI bus.
pub type SpiFactory<B> = fn(bus: u8, slave: u8, clock_hz: u32, mode: SpiMode) -> io::Result<B>;

/// A trait abstracting access to an SPI bus.
pub trait SpiBus: Write {
    /// Returns the maximum transfer size for the bus.
    fn max_size(&self) -> usize;
}
