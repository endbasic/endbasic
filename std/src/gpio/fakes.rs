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

//! Fake implementations of GPIO pins that work on all platforms.

use crate::gpio::{Pin, PinMode, Pins};
use std::any::Any;
use std::collections::VecDeque;
use std::io;

/// Stand-in implementation of the EndBASIC GPIO operations that always returns an error.
#[derive(Default)]
pub struct NoopPins {}

impl Pins for NoopPins {
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn setup(&mut self, _pin: Pin, _mode: PinMode) -> io::Result<()> {
        Err(io::Error::other("GPIO backend not compiled in"))
    }

    fn clear(&mut self, _pin: Pin) -> io::Result<()> {
        Err(io::Error::other("GPIO backend not compiled in"))
    }

    fn clear_all(&mut self) -> io::Result<()> {
        Err(io::Error::other("GPIO backend not compiled in"))
    }

    fn read(&mut self, _pin: Pin) -> io::Result<bool> {
        Err(io::Error::other("GPIO backend not compiled in"))
    }

    fn write(&mut self, _pin: Pin, _v: bool) -> io::Result<()> {
        Err(io::Error::other("GPIO backend not compiled in"))
    }
}

/// Per-pin operation identifier in the mock data.
#[derive(PartialEq)]
enum MockOp {
    SetupIn = 1,
    SetupInPullDown = 2,
    SetupInPullUp = 3,
    SetupOut = 4,

    Clear = 5,
    ClearAll = -1,

    ReadLow = 10,
    ReadHigh = 11,

    WriteLow = 20,
    WriteHigh = 21,
}

impl MockOp {
    /// Encodes a `pin` and `op` pair as a trace datum.
    fn encode(pin: Pin, op: Self) -> i32 {
        assert!(op != Self::ClearAll);
        (pin.0 as i32) * 100 + (op as i32)
    }
}

/// Self-contained mock GPIO implementation that records operations and supplies pre-seeded reads.
///
/// Call `inject_read` to pre-seed reads before running code that calls `GPIO_READ`, and call
/// `trace` afterwards to inspect the ordered record of all GPIO operations.
#[derive(Default)]
pub struct MockPins {
    /// FIFO queue of pre-seeded reads: the next `read` call pops from the front.
    reads: VecDeque<(Pin, bool)>,

    /// Ordered record of all GPIO operations performed.
    ///
    /// Operations are encoded as `pin * 100 + MockOp` with `ClearAll` being encoded as `-1`.
    trace: Vec<i32>,
}

impl MockPins {
    /// Pre-seeds a future `read(pin)` call to return `high`.
    pub fn inject_read(&mut self, pin: Pin, high: bool) {
        self.reads.push_back((pin, high));
    }

    /// Returns the ordered trace of all GPIO operations performed so far.
    pub fn trace(&self) -> &[i32] {
        &self.trace
    }
}

impl Pins for MockPins {
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn setup(&mut self, pin: Pin, mode: PinMode) -> io::Result<()> {
        let datum = match mode {
            PinMode::In => MockOp::encode(pin, MockOp::SetupIn),
            PinMode::InPullDown => MockOp::encode(pin, MockOp::SetupInPullDown),
            PinMode::InPullUp => MockOp::encode(pin, MockOp::SetupInPullUp),
            PinMode::Out => MockOp::encode(pin, MockOp::SetupOut),
        };
        self.trace.push(datum);
        Ok(())
    }

    fn clear(&mut self, pin: Pin) -> io::Result<()> {
        self.trace.push(MockOp::encode(pin, MockOp::Clear));
        Ok(())
    }

    fn clear_all(&mut self) -> io::Result<()> {
        self.trace.push(MockOp::ClearAll as i32);
        Ok(())
    }

    fn read(&mut self, pin: Pin) -> io::Result<bool> {
        match self.reads.pop_front() {
            Some((read_pin, high)) if read_pin == pin => {
                let op = if high { MockOp::ReadHigh } else { MockOp::ReadLow };
                self.trace.push(MockOp::encode(pin, op));
                Ok(high)
            }
            Some((read_pin, _)) => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Want to read pin {} but next mock read is for pin {}", pin.0, read_pin.0),
            )),
            None => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("No mock read available for pin {}", pin.0),
            )),
        }
    }

    fn write(&mut self, pin: Pin, v: bool) -> io::Result<()> {
        let op = if v { MockOp::WriteHigh } else { MockOp::WriteLow };
        self.trace.push(MockOp::encode(pin, op));
        Ok(())
    }
}
