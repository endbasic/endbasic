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

//! GPIO access functions and commands for EndBASIC.

use async_trait::async_trait;
use endbasic_core::ast::{ArgSep, Expr, Value, VarType};
use endbasic_core::exec::Machine;
use endbasic_core::syms::{
    CallError, CallableMetadata, CallableMetadataBuilder, Command, CommandResult, Function,
    FunctionResult, Symbols,
};
use std::cell::RefCell;
use std::io;
use std::rc::Rc;
use std::result::Result;

mod fakes;
pub(crate) use fakes::{MockPins, NoopPins};

#[cfg(feature = "rpi")]
mod rpi;
#[cfg(feature = "rpi")]
pub(crate) use rpi::RppalPins;

/// Category string for all functions provided by this module.
const CATEGORY: &str = "Hardware manipulation";

/// Pin identifier.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Pin(u8);

impl Pin {
    /// Creates a new pin number from an EndBASIC integer value.
    fn from_i32(i: i32) -> Result<Self, CallError> {
        if i < 0 {
            return Err(CallError::ArgumentError(format!("Pin number {} must be positive", i)));
        }
        if i > std::u8::MAX as i32 {
            return Err(CallError::ArgumentError(format!("Pin number {} is too large", i)));
        }
        Ok(Self(i as u8))
    }

    /// Obtains a pin number from an expression.
    fn parse(expr: &Expr, machine: &mut Machine) -> Result<Pin, CallError> {
        Pin::parse_value(&expr.eval(machine.get_mut_symbols())?)
    }

    /// Obtains a pin number from a value.
    fn parse_value(value: &Value) -> Result<Pin, CallError> {
        match value {
            Value::Integer(n) => Ok(Pin::from_i32(*n)?),
            v => Err(CallError::ArgumentError(format!("Pin number {:?} must be an integer", v))),
        }
    }
}

/// Pin configuration, which includes mode and bias.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum PinMode {
    /// Pin that can be read from with no bias.
    In,

    /// Pin that can be read from with its built-in pull-down resistor (if present) enabled.
    InPullDown,

    /// Pin that can be read from with its built-in pull-up resistor (if present) enabled.
    InPullUp,

    /// Pin that can be written to.
    Out,
}

impl PinMode {
    /// Obtains a `PinMode` from an expression.
    fn parse(expr: &Expr, machine: &mut Machine) -> Result<PinMode, CallError> {
        match expr.eval(machine.get_mut_symbols())? {
            Value::Text(s) => match s.to_ascii_uppercase().as_ref() {
                "IN" => Ok(PinMode::In),
                "IN-PULL-UP" => Ok(PinMode::InPullUp),
                "IN-PULL-DOWN" => Ok(PinMode::InPullDown),
                "OUT" => Ok(PinMode::Out),
                s => Err(CallError::ArgumentError(format!("Unknown pin mode {}", s))),
            },
            v => Err(CallError::ArgumentError(format!("Pin mode {:?} must be a string", v))),
        }
    }
}

/// Obtains a pin value from an expression.
fn parse_value(expr: &Expr, machine: &mut Machine) -> Result<bool, CallError> {
    match expr.eval(machine.get_mut_symbols())? {
        Value::Boolean(b) => Ok(b),
        v => Err(CallError::ArgumentError(format!("Pin value {:?} must be boolean", v))),
    }
}

/// Generic abstraction over a GPIO chip to back all EndBASIC commands.
pub trait Pins {
    /// Configures the `pin` as either input or output (per `mode`).
    ///
    /// This lazily initialies the GPIO chip as well on the first pin setup.
    ///
    /// It is OK to set up a pin multiple times without calling `clear()` in-between.
    fn setup(&mut self, pin: Pin, mode: PinMode) -> io::Result<()>;

    /// Resets a given `pin` to its default state.
    fn clear(&mut self, pin: Pin) -> io::Result<()>;

    /// Resets all pins to their default state.
    fn clear_all(&mut self) -> io::Result<()>;

    /// Reads the value of the given `pin`, which must have been previously setup as an input pin.
    fn read(&mut self, pin: Pin) -> io::Result<bool>;

    /// Writes `v` to the given `pin`, which must have been previously setup as an output pin.
    fn write(&mut self, pin: Pin, v: bool) -> io::Result<()>;
}

/// The `GPIO_SETUP` command.
pub struct GpioSetupCommand {
    metadata: CallableMetadata,
    pins: Rc<RefCell<dyn Pins>>,
}

impl GpioSetupCommand {
    /// Creates a new instance of the command.
    pub fn new(pins: Rc<RefCell<dyn Pins>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GPIO_SETUP", VarType::Void)
                .with_syntax("pin% mode$")
                .with_category(CATEGORY)
                .with_description(
                    "Configures a GPIO pin for input or output.
Before a GPIO pin can be used for reads or writes, it must be configured to be an input or \
output pin.  Additionally, if pull up or pull down resistors are available and desired, these \
must be configured upfront too.
The mode$ has to be one of \"IN\", \"IN-PULL-DOWN\", \"IN-PULL-UP\", or \"OUT\".  These values \
are case-insensitive.  The possibility of using the pull-down and pull-up resistors depends on \
whether they are available in the hardware, and selecting these modes will fail if they are not.
It is OK to reconfigure an already configured pin without clearing its state first.",
                )
                .build(),
            pins,
        })
    }
}

#[async_trait(?Send)]
impl Command for GpioSetupCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        match args {
            [(Some(pin), ArgSep::Long), (Some(mode), ArgSep::End)] => {
                let pin = Pin::parse(pin, machine)?;
                let mode = PinMode::parse(mode, machine)?;

                match MockPins::try_new(machine.get_mut_symbols()) {
                    Some(mut pins) => pins.setup(pin, mode)?,
                    None => self.pins.borrow_mut().setup(pin, mode)?,
                };
                Ok(())
            }
            _ => Err(CallError::ArgumentError("GPIO_SETUP takes two arguments".to_owned())),
        }
    }
}

/// The `GPIO_CLEAR` command.
pub struct GpioClearCommand {
    metadata: CallableMetadata,
    pins: Rc<RefCell<dyn Pins>>,
}

impl GpioClearCommand {
    /// Creates a new instance of the command.
    pub fn new(pins: Rc<RefCell<dyn Pins>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GPIO_CLEAR", VarType::Void)
                .with_syntax("[pin%]")
                .with_category(CATEGORY)
                .with_description(
                    "Resets the GPIO chip or a specific pin.
If no pin% is specified, resets the state of all GPIO pins. \
If a pin% is given, only that pin is reset.  It is OK if the given pin has never been configured \
before.",
                )
                .build(),
            pins,
        })
    }
}

#[async_trait(?Send)]
impl Command for GpioClearCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        match args {
            [] => {
                match MockPins::try_new(machine.get_mut_symbols()) {
                    Some(mut pins) => pins.clear_all()?,
                    None => self.pins.borrow_mut().clear_all()?,
                };
                Ok(())
            }
            [(Some(pin), ArgSep::End)] => {
                let pin = Pin::parse(pin, machine)?;
                match MockPins::try_new(machine.get_mut_symbols()) {
                    Some(mut pins) => pins.clear(pin)?,
                    None => self.pins.borrow_mut().clear(pin)?,
                };
                Ok(())
            }
            _ => Err(CallError::ArgumentError("GPIO_CLEAR takes zero or one argument".to_owned())),
        }
    }
}

/// The `GPIO_READ` function.
pub struct GpioReadFunction {
    metadata: CallableMetadata,
    pins: Rc<RefCell<dyn Pins>>,
}

impl GpioReadFunction {
    /// Creates a new instance of the function.
    pub fn new(pins: Rc<RefCell<dyn Pins>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GPIO_READ", VarType::Boolean)
                .with_syntax("pin%")
                .with_category(CATEGORY)
                .with_description(
                    "Reads the state of a GPIO pin.
Returns FALSE to represent a low value, and TRUE to represent a high value.",
                )
                .build(),
            pins,
        })
    }
}

impl Function for GpioReadFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    fn exec(&self, args: Vec<Value>, symbols: &mut Symbols) -> FunctionResult {
        match args.as_slice() {
            [pin] => {
                let pin = Pin::parse_value(pin)?;
                let value = match MockPins::try_new(symbols) {
                    Some(mut pins) => pins.read(pin)?,
                    None => self.pins.borrow_mut().read(pin)?,
                };
                Ok(value.into())
            }
            _ => Err(CallError::SyntaxError),
        }
    }
}

/// The `GPIO_WRITE` command.
pub struct GpioWriteCommand {
    metadata: CallableMetadata,
    pins: Rc<RefCell<dyn Pins>>,
}

impl GpioWriteCommand {
    /// Creates a new instance of the command.
    pub fn new(pins: Rc<RefCell<dyn Pins>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GPIO_WRITE", VarType::Void)
                .with_syntax("pin% value?")
                .with_category(CATEGORY)
                .with_description(
                    "Sets the state of a GPIO pin.
A FALSE value? sets the pin to low, and a TRUE value? sets the pin to high.",
                )
                .build(),
            pins,
        })
    }
}

#[async_trait(?Send)]
impl Command for GpioWriteCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        match args {
            [(Some(pin), ArgSep::Long), (Some(value), ArgSep::End)] => {
                let pin = Pin::parse(pin, machine)?;
                let value = parse_value(value, machine)?;
                match MockPins::try_new(machine.get_mut_symbols()) {
                    Some(mut pins) => pins.write(pin, value)?,
                    None => self.pins.borrow_mut().write(pin, value)?,
                };
                Ok(())
            }
            _ => Err(CallError::ArgumentError("GPIO_WRITE takes two arguments".to_owned())),
        }
    }
}

/// Adds all symbols provided by this module to the given `machine`.
pub fn add_all(machine: &mut Machine, pins: Rc<RefCell<dyn Pins>>) {
    machine.add_command(GpioClearCommand::new(pins.clone()));
    machine.add_command(GpioSetupCommand::new(pins.clone()));
    machine.add_command(GpioWriteCommand::new(pins.clone()));
    machine.add_function(GpioReadFunction::new(pins));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;

    /// Common checks for pin number validation.
    ///
    /// The given input `fmt` string contains the command to test with a placeholder `_PIN` for
    /// where the pin number goes.  The `prefix` contains a possible prefix for the error messages.
    fn check_pin_validation(prefix: &str, fmt: &str) {
        check_stmt_err(
            format!(r#"{}Pin number Boolean(true) must be an integer"#, prefix),
            &fmt.replace("_PIN_", "TRUE"),
        );
        check_stmt_err(
            format!(r#"{}Pin number 123456789 is too large"#, prefix),
            &fmt.replace("_PIN_", "123456789"),
        );
        check_stmt_err(
            format!(r#"{}Pin number -1 must be positive"#, prefix),
            &fmt.replace("_PIN_", "-1"),
        );
    }

    /// Does a GPIO test using the mocking feature, running the commands in `code` and expecting
    /// that the `__GPIO_MOCK_DATA` array contains `trace` after completion.
    fn do_mock_test<S: Into<String>>(code: S, trace: &[i32]) {
        let code = code.into();

        let mut exp_data = vec![Value::Integer(0); 50];
        for (i, d) in trace.iter().enumerate() {
            exp_data[i] = Value::Integer(*d);
        }

        Tester::default()
            .run(format!(r#"DIM __GPIO_MOCK_DATA(50) AS INTEGER: __GPIO_MOCK_LAST = 0: {}"#, code))
            .expect_var("__GPIO_MOCK_LAST", Value::Integer(trace.len() as i32))
            .expect_array_simple("__GPIO_MOCK_DATA", VarType::Integer, exp_data)
            .check();
    }

    /// Tests that all GPIO operations delegate to the real pins implementation, which defaults to
    /// the no-op backend when using the tester.  All other tests in this file use the mocking
    /// features to validate operation.
    #[test]
    fn test_real_backend() {
        check_stmt_err("GPIO backend not compiled in", "GPIO_SETUP 0, \"IN\"");
        check_stmt_err("GPIO backend not compiled in", "GPIO_CLEAR");
        check_stmt_err("GPIO backend not compiled in", "GPIO_CLEAR 0");
        check_expr_error(
            "Error in call to GPIO_READ: GPIO backend not compiled in",
            "GPIO_READ(0)",
        );
        check_stmt_err("GPIO backend not compiled in", "GPIO_WRITE 0, TRUE");
    }

    #[test]
    fn test_gpio_setup_ok() {
        for mode in &["in", "IN"] {
            do_mock_test(format!(r#"GPIO_SETUP 5, "{}""#, mode), &[501]);
        }
        for mode in &["in-pull-down", "IN-PULL-DOWN"] {
            do_mock_test(format!(r#"GPIO_SETUP 6, "{}""#, mode), &[602]);
        }
        for mode in &["in-pull-up", "IN-PULL-UP"] {
            do_mock_test(format!(r#"GPIO_SETUP 7, "{}""#, mode), &[703]);
        }
        for mode in &["out", "OUT"] {
            do_mock_test(format!(r#"GPIO_SETUP 8, "{}""#, mode), &[804]);
        }
    }

    #[test]
    fn test_gpio_setup_multiple() {
        do_mock_test(r#"GPIO_SETUP 18, "IN-PULL-UP": GPIO_SETUP 10, "OUT""#, &[1803, 1004]);
    }

    #[test]
    fn test_gpio_setup_errors() {
        check_stmt_err("GPIO_SETUP takes two arguments", r#"GPIO_SETUP"#);
        check_stmt_err("GPIO_SETUP takes two arguments", r#"GPIO_SETUP 1"#);
        check_stmt_err("GPIO_SETUP takes two arguments", r#"GPIO_SETUP 1; 2"#);
        check_stmt_err("GPIO_SETUP takes two arguments", r#"GPIO_SETUP 1, 2, 3"#);

        check_pin_validation("", r#"GPIO_SETUP _PIN_, "IN""#);

        check_stmt_err(r#"Unknown pin mode IN-OUT"#, r#"GPIO_SETUP 1, "IN-OUT""#);
    }

    #[test]
    fn test_gpio_clear_all() {
        do_mock_test("GPIO_CLEAR", &[-1]);
    }

    #[test]
    fn test_gpio_clear_one() {
        do_mock_test("GPIO_CLEAR 4", &[405]);
    }

    #[test]
    fn test_gpio_clear_errors() {
        check_stmt_err("GPIO_CLEAR takes zero or one argument", r#"GPIO_CLEAR 1, 2"#);

        check_pin_validation("", r#"GPIO_CLEAR _PIN_"#);
    }

    #[test]
    fn test_gpio_read_ok() {
        do_mock_test(
            "__GPIO_MOCK_DATA(0) = 310
            __GPIO_MOCK_DATA(2) = 311
            GPIO_WRITE 5, GPIO_READ(3)
            GPIO_WRITE 7, GPIO_READ(3)",
            &[310, 520, 311, 721],
        );
    }

    #[test]
    fn test_gpio_read_errors() {
        check_expr_error("Syntax error in call to GPIO_READ: expected pin%", r#"GPIO_READ()"#);
        check_expr_error("Syntax error in call to GPIO_READ: expected pin%", r#"GPIO_READ(1, 2)"#);

        check_pin_validation("Syntax error in call to GPIO_READ: ", r#"v = GPIO_READ(_PIN_)"#);
    }

    #[test]
    fn test_gpio_write_ok() {
        do_mock_test("GPIO_WRITE 3, TRUE: GPIO_WRITE 3, FALSE", &[321, 320]);
    }

    #[test]
    fn test_gpio_write_errors() {
        check_stmt_err("GPIO_WRITE takes two arguments", r#"GPIO_WRITE"#);
        check_stmt_err("GPIO_WRITE takes two arguments", r#"GPIO_WRITE 1, TRUE, 2"#);
        check_stmt_err("GPIO_WRITE takes two arguments", r#"GPIO_WRITE 1; TRUE"#);

        check_pin_validation("", r#"GPIO_WRITE _PIN_, TRUE"#);

        check_stmt_err("Pin value Integer(5) must be boolean", r#"GPIO_WRITE 1, 5"#);
    }
}
