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
use endbasic_core::ast::{ExprType, Value, VarRef};
use endbasic_core::syms::{Array, Symbol, Symbols};
use std::io;

/// Stand-in implementation of the EndBASIC GPIO operations that always returns an error.
#[derive(Default)]
pub(crate) struct NoopPins {}

impl Pins for NoopPins {
    fn setup(&mut self, _pin: Pin, _mode: PinMode) -> io::Result<()> {
        Err(io::Error::new(io::ErrorKind::Other, "GPIO backend not compiled in"))
    }

    fn clear(&mut self, _pin: Pin) -> io::Result<()> {
        Err(io::Error::new(io::ErrorKind::Other, "GPIO backend not compiled in"))
    }

    fn clear_all(&mut self) -> io::Result<()> {
        Err(io::Error::new(io::ErrorKind::Other, "GPIO backend not compiled in"))
    }

    fn read(&mut self, _pin: Pin) -> io::Result<bool> {
        Err(io::Error::new(io::ErrorKind::Other, "GPIO backend not compiled in"))
    }

    fn write(&mut self, _pin: Pin, _v: bool) -> io::Result<()> {
        Err(io::Error::new(io::ErrorKind::Other, "GPIO backend not compiled in"))
    }
}

/// Mock GPIO implementation that tracks operations and supplies fake reads.
///
/// This is an undocumented feature to support unit-testing of our own demo code and is quite
/// convoluted due to the fact that we don't have a lot of freedom in what we can do in the context
/// of the `Pins` implementation: we get no context passed in (intentionally), so the only context
/// we can grab with some contortions is a reference to the machine's symbols.  This reference is
/// only valid for the duration of a GPIO call and thus this structure must be recreated on each
/// GPIO call and cannot maintain state of its own (other than via symbols).
///
/// To enable mocking, the user must define the `__GPIO_MOCK_DATA` unidimensional array of integer
/// type (aka `data`) and the `__GPIO_MOCK_LAST` integer variable (aka `last`).  If these types are
/// not met, mocking is silently not enabled.
///
/// The `data` array represents an ordered trace of GPIO calls and `last` indicates the index
/// within the array that should be inspected on the next GPIO call.  Each `data[last]` value is
/// encoded as a pin number (times 100) plus a `MockOp` integer that identifies the operation that
/// happened.
///
/// For mutating GPIO calls, `data[last]` has to be zero on entry (or else the operation will fail)
/// and will be updated with the affected pin number and the operation.  The meta operation to clear
/// all pins has a special number.
///
/// For read GPIO calls, `data[last]` has to contain the pin number that matches the read operation
/// and the desired outcome of the operation.
///
/// When a test is complete, the test should inspect the values in `data` up to the `last` position
/// and ensure they match expectations.
pub(crate) struct MockPins<'a> {
    symbols: &'a mut Symbols,
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
    /// Encodes a `pin` and `op` pair as a datum for the mock data.
    fn encode(pin: Pin, op: Self) -> i32 {
        assert!(op != Self::ClearAll);
        (pin.0 as i32) * 100 + (op as i32)
    }

    /// Decodes a datum from the mock data that is to be used for a read operation.
    fn decode_read(pos: i32, datum: i32) -> io::Result<(Pin, bool)> {
        if datum < 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Negative read value at __GPIO_MOCK_DATA({})", pos),
            ));
        }
        let pin = datum / 100;
        if pin > u8::MAX as i32 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Pin number too large at __GPIO_MOCK_DATA({})", pos),
            ));
        }
        let pin = Pin(pin as u8);
        match datum % 100 {
            i if i == (MockOp::ReadLow as i32) => Ok((pin, false)),
            i if i == (MockOp::ReadHigh as i32) => Ok((pin, true)),
            i => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Unknown read operation {} at __GPIO_MOCK_DATA({})", i, pos),
            )),
        }
    }
}

impl<'a> MockPins<'a> {
    /// Creates a mock pins instance if `__GPIO_MOCK_DATA` *and* `__GPIO_MOCK_LAST` are set and of
    /// the correct types.
    ///
    /// Note that, while this object is alive (which is in the context of an individual GPIO call),
    /// we know that these symbols are valid so other methods can assume that they are.
    pub(crate) fn try_new(symbols: &'a mut Symbols) -> Option<MockPins<'a>> {
        if MockPins::get_last(symbols).is_none() || MockPins::get_mut_data(symbols).is_none() {
            None
        } else {
            Some(Self { symbols })
        }
    }

    /// Obtains the value of `__GPIO_MOCK_LAST` if present.
    fn get_last(symbols: &Symbols) -> Option<i32> {
        match symbols.get(&VarRef::new("__GPIO_MOCK_LAST", Some(ExprType::Integer))) {
            Ok(Some(Symbol::Variable(Value::Integer(i)))) => Some(*i),
            _ => None,
        }
    }

    /// Obtains a mutable reference to `__GPIO_MOCK_DATA` if present.
    fn get_mut_data(symbols: &mut Symbols) -> Option<&mut Array> {
        match symbols.get_mut(&VarRef::new("__GPIO_MOCK_DATA", Some(ExprType::Integer))) {
            Ok(Some(Symbol::Array(data))) if data.dimensions().len() == 1 => Some(data),
            _ => None,
        }
    }

    /// Reads the current value at `data[last]` with proper validation.
    fn raw_get(last: i32, data: &Array) -> io::Result<i32> {
        match data.index(&[last]) {
            Ok(Value::Integer(v)) => Ok(*v),
            Ok(_) => panic!("We know it's an integer"),
            Err(e) => Err(io::Error::new(io::ErrorKind::InvalidData, e.to_string())),
        }
    }

    /// Increments `__GPIO_MOCK_LAST`.
    fn increment_last(&mut self) -> io::Result<()> {
        let last = MockPins::get_last(self.symbols).expect("Validated at construction time");
        let new_last = Value::Integer(last + 1);
        match self
            .symbols
            .set_var(&VarRef::new("__GPIO_MOCK_LAST", Some(ExprType::Integer)), new_last)
        {
            Ok(()) => Ok(()),
            Err(e) => Err(io::Error::new(io::ErrorKind::InvalidData, e.to_string())),
        }
    }

    /// Reads `__GPIO_MOCK_DATA[__GPIO_MOCK_LAST]` and advances `__GPIO_MOCK_LAST`.  Returns the
    /// position of the array that was read and the value at that position.
    fn read_and_advance(&mut self) -> io::Result<(i32, i32)> {
        let last = MockPins::get_last(self.symbols).expect("Validated at construction time");
        let data = MockPins::get_mut_data(self.symbols).expect("Validated at construction time");

        let v = MockPins::raw_get(last, data)?;
        self.increment_last()?;
        Ok((last, v))
    }

    /// Writes `datum` to `__GPIO_MOCK_DATA[__GPIO_MOCK_LAST]`, which must be zero upfront.
    fn append(&mut self, datum: i32) -> io::Result<()> {
        let last = MockPins::get_last(self.symbols).expect("Validated at construction time");
        let data = MockPins::get_mut_data(self.symbols).expect("Validated at construction time");

        let old_datum = MockPins::raw_get(last, data)?;
        if old_datum != 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Position already occupied at __GPIO_MOCK_READ({})", last),
            ));
        }

        let data = MockPins::get_mut_data(self.symbols).expect("Validated at construction time");
        match data.assign(&[last], Value::Integer(datum)) {
            Ok(()) => (),
            Err(e) => return Err(io::Error::new(io::ErrorKind::InvalidData, e.to_string())),
        };
        self.increment_last()
    }
}

impl<'a> Pins for MockPins<'a> {
    fn setup(&mut self, pin: Pin, mode: PinMode) -> io::Result<()> {
        let datum = match mode {
            PinMode::In => MockOp::encode(pin, MockOp::SetupIn),
            PinMode::InPullDown => MockOp::encode(pin, MockOp::SetupInPullDown),
            PinMode::InPullUp => MockOp::encode(pin, MockOp::SetupInPullUp),
            PinMode::Out => MockOp::encode(pin, MockOp::SetupOut),
        };
        self.append(datum)
    }

    fn clear(&mut self, pin: Pin) -> io::Result<()> {
        let datum = MockOp::encode(pin, MockOp::Clear);
        self.append(datum)
    }

    fn clear_all(&mut self) -> io::Result<()> {
        let datum = MockOp::ClearAll as i32;
        self.append(datum)
    }

    fn read(&mut self, pin: Pin) -> io::Result<bool> {
        let (pos, datum) = self.read_and_advance()?;
        let (datum_pin, value) = MockOp::decode_read(pos, datum)?;
        if datum_pin != pin {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "Want to read pin {} but __GPIO_MOCK_DATA({}) is for pin {}",
                    pin.0, pos, datum_pin.0
                ),
            ));
        }
        Ok(value)
    }

    fn write(&mut self, pin: Pin, v: bool) -> io::Result<()> {
        if v {
            self.append(MockOp::encode(pin, MockOp::WriteHigh))
        } else {
            self.append(MockOp::encode(pin, MockOp::WriteLow))
        }
    }
}
