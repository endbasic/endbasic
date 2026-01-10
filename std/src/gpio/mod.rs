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
use endbasic_core::LineCol;
use endbasic_core::ast::{ArgSep, ExprType};
use endbasic_core::compiler::{ArgSepSyntax, RequiredValueSyntax, SingularArgSyntax};
use endbasic_core::exec::{Clearable, Error, Machine, Result, Scope};
use endbasic_core::syms::{Callable, CallableMetadata, CallableMetadataBuilder, Symbols};
use std::borrow::Cow;
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

mod fakes;
pub(crate) use fakes::{MockPins, NoopPins};

/// Category description for all symbols provided by this module.
const CATEGORY: &str = "Hardware interface
EndBASIC provides features to manipulate external hardware.  These features are currently limited \
to GPIO interaction on a Raspberry Pi and are only available when EndBASIC has explicitly been \
built with the --features=rpi option.  Support for other busses and platforms may come later.";

/// Pin identifier.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Pin(pub u8);

impl Pin {
    /// Creates a new pin number from an EndBASIC integer value.
    fn from_i32(i: i32, pos: LineCol) -> Result<Self> {
        if i < 0 {
            return Err(Error::SyntaxError(pos, format!("Pin number {} must be positive", i)));
        }
        if i > u8::MAX as i32 {
            return Err(Error::SyntaxError(pos, format!("Pin number {} is too large", i)));
        }
        Ok(Self(i as u8))
    }
}

/// Pin configuration, which includes mode and bias.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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
    /// Obtains a `PinMode` from a value.
    fn parse(s: &str, pos: LineCol) -> Result<PinMode> {
        match s.to_ascii_uppercase().as_ref() {
            "IN" => Ok(PinMode::In),
            "IN-PULL-UP" => Ok(PinMode::InPullUp),
            "IN-PULL-DOWN" => Ok(PinMode::InPullDown),
            "OUT" => Ok(PinMode::Out),
            s => Err(Error::SyntaxError(pos, format!("Unknown pin mode {}", s))),
        }
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

/// Resets the state of the pins in a best-effort manner.
pub(crate) struct PinsClearable {
    pins: Rc<RefCell<dyn Pins>>,
}

impl PinsClearable {
    /// Creates a new clearable for `pins`.
    pub(crate) fn new(pins: Rc<RefCell<dyn Pins>>) -> Box<Self> {
        Box::from(Self { pins })
    }
}

impl Clearable for PinsClearable {
    fn reset_state(&self, syms: &mut Symbols) {
        let _ = match MockPins::try_new(syms) {
            Some(mut pins) => pins.clear_all(),
            None => self.pins.borrow_mut().clear_all(),
        };
    }
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
            metadata: CallableMetadataBuilder::new("GPIO_SETUP")
                .with_syntax(&[(
                    &[
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("pin"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("mode"),
                                vtype: ExprType::Text,
                            },
                            ArgSepSyntax::End,
                        ),
                    ],
                    None,
                )])
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
impl Callable for GpioSetupCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, machine: &mut Machine) -> Result<()> {
        debug_assert_eq!(2, scope.nargs());
        let pin = {
            let (i, pos) = scope.pop_integer_with_pos();
            Pin::from_i32(i, pos)?
        };
        let mode = {
            let (t, pos) = scope.pop_string_with_pos();
            PinMode::parse(&t, pos)?
        };

        match MockPins::try_new(machine.get_mut_symbols()) {
            Some(mut pins) => pins.setup(pin, mode).map_err(|e| scope.io_error(e))?,
            None => self.pins.borrow_mut().setup(pin, mode).map_err(|e| scope.io_error(e))?,
        };
        Ok(())
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
            metadata: CallableMetadataBuilder::new("GPIO_CLEAR")
                .with_syntax(&[
                    (&[], None),
                    (
                        &[SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("pin"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::End,
                        )],
                        None,
                    ),
                ])
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
impl Callable for GpioClearCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, machine: &mut Machine) -> Result<()> {
        if scope.nargs() == 0 {
            match MockPins::try_new(machine.get_mut_symbols()) {
                Some(mut pins) => pins.clear_all().map_err(|e| scope.io_error(e))?,
                None => self.pins.borrow_mut().clear_all().map_err(|e| scope.io_error(e))?,
            };
        } else {
            debug_assert_eq!(1, scope.nargs());
            let pin = {
                let (i, pos) = scope.pop_integer_with_pos();
                Pin::from_i32(i, pos)?
            };

            match MockPins::try_new(machine.get_mut_symbols()) {
                Some(mut pins) => pins.clear(pin).map_err(|e| scope.io_error(e))?,
                None => self.pins.borrow_mut().clear(pin).map_err(|e| scope.io_error(e))?,
            };
        }

        Ok(())
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
            metadata: CallableMetadataBuilder::new("GPIO_READ")
                .with_return_type(ExprType::Boolean)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax {
                            name: Cow::Borrowed("pin"),
                            vtype: ExprType::Integer,
                        },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
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

#[async_trait(?Send)]
impl Callable for GpioReadFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, machine: &mut Machine) -> Result<()> {
        debug_assert_eq!(1, scope.nargs());
        let pin = {
            let (i, pos) = scope.pop_integer_with_pos();
            Pin::from_i32(i, pos)?
        };

        let value = match MockPins::try_new(machine.get_mut_symbols()) {
            Some(mut pins) => pins.read(pin).map_err(|e| scope.io_error(e))?,
            None => self.pins.borrow_mut().read(pin).map_err(|e| scope.io_error(e))?,
        };
        scope.return_boolean(value)
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
            metadata: CallableMetadataBuilder::new("GPIO_WRITE")
                .with_syntax(&[(
                    &[
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("pin"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("value"),
                                vtype: ExprType::Boolean,
                            },
                            ArgSepSyntax::End,
                        ),
                    ],
                    None,
                )])
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
impl Callable for GpioWriteCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, machine: &mut Machine) -> Result<()> {
        debug_assert_eq!(2, scope.nargs());
        let pin = {
            let (i, pos) = scope.pop_integer_with_pos();
            Pin::from_i32(i, pos)?
        };
        let value = scope.pop_boolean();

        match MockPins::try_new(machine.get_mut_symbols()) {
            Some(mut pins) => pins.write(pin, value).map_err(|e| scope.io_error(e))?,
            None => self.pins.borrow_mut().write(pin, value).map_err(|e| scope.io_error(e))?,
        };
        Ok(())
    }
}

/// Adds all symbols provided by this module to the given `machine`.
pub fn add_all(machine: &mut Machine, pins: Rc<RefCell<dyn Pins>>) {
    machine.add_clearable(PinsClearable::new(pins.clone()));
    machine.add_callable(GpioClearCommand::new(pins.clone()));
    machine.add_callable(GpioReadFunction::new(pins.clone()));
    machine.add_callable(GpioSetupCommand::new(pins.clone()));
    machine.add_callable(GpioWriteCommand::new(pins));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;
    use endbasic_core::ast::Value;

    /// Common checks for pin number validation.
    ///
    /// The given input `fmt` string contains the command to test with a placeholder `_PIN` for
    /// where the pin number goes.  The `short_prefix` and `long_prefix` contain possible prefixes
    /// for the error messages.
    fn check_pin_validation(short_prefix: &str, long_prefix: &str, fmt: &str) {
        check_stmt_compilation_err(
            format!(r#"{}BOOLEAN is not a number"#, short_prefix),
            &fmt.replace("_PIN_", "TRUE"),
        );
        check_stmt_err(
            format!(r#"{}Pin number 123456789 is too large"#, long_prefix),
            &fmt.replace("_PIN_", "123456789"),
        );
        check_stmt_err(
            format!(r#"{}Pin number -1 must be positive"#, long_prefix),
            &fmt.replace("_PIN_", "-1"),
        );
    }

    /// Does a GPIO test using the mocking feature, running the commands in `code` and expecting
    /// that the `__GPIO_MOCK_DATA` array contains `trace` after completion.
    ///
    /// Sets all `vars` before evaluating the expression so that the expression can contain variable
    /// references.
    fn do_mock_test_with_vars<S: Into<String>, VS: Into<Vec<(&'static str, Value)>>>(
        code: S,
        trace: &[i32],
        vars: VS,
    ) {
        let code = code.into();
        let vars = vars.into();

        let mut exp_data = vec![Value::Integer(0); 50];
        for (i, d) in trace.iter().enumerate() {
            exp_data[i] = Value::Integer(*d);
        }

        let mut t = Tester::default();
        for var in vars.as_slice() {
            t = t.set_var(var.0, var.1.clone());
        }

        let mut c = t
            .run(format!(r#"DIM __GPIO_MOCK_DATA(50) AS INTEGER: __GPIO_MOCK_LAST = 0: {}"#, code));
        for var in vars.into_iter() {
            c = c.expect_var(var.0, var.1.clone());
        }
        c.expect_var("__GPIO_MOCK_LAST", Value::Integer(trace.len() as i32))
            .expect_array_simple("__GPIO_MOCK_DATA", ExprType::Integer, exp_data)
            .check();
    }

    /// Does a GPIO test using the mocking feature, running the commands in `code` and expecting
    /// that the `__GPIO_MOCK_DATA` array contains `trace` after completion.
    fn do_mock_test<S: Into<String>>(code: S, trace: &[i32]) {
        do_mock_test_with_vars(code, trace, [])
    }

    /// Tests that all GPIO operations delegate to the real pins implementation, which defaults to
    /// the no-op backend when using the tester.  All other tests in this file use the mocking
    /// features to validate operation.
    #[test]
    fn test_real_backend() {
        check_stmt_err("1:1: GPIO backend not compiled in", "GPIO_SETUP 0, \"IN\"");
        check_stmt_err("1:1: GPIO backend not compiled in", "GPIO_CLEAR");
        check_stmt_err("1:1: GPIO backend not compiled in", "GPIO_CLEAR 0");
        check_expr_error("1:10: GPIO backend not compiled in", "GPIO_READ(0)");
        check_stmt_err("1:1: GPIO backend not compiled in", "GPIO_WRITE 0, TRUE");
    }

    #[test]
    fn test_gpio_setup_ok() {
        for mode in &["in", "IN"] {
            do_mock_test(format!(r#"GPIO_SETUP 5, "{}""#, mode), &[501]);
            do_mock_test(format!(r#"GPIO_SETUP 5.2, "{}""#, mode), &[501]);
        }
        for mode in &["in-pull-down", "IN-PULL-DOWN"] {
            do_mock_test(format!(r#"GPIO_SETUP 6, "{}""#, mode), &[602]);
            do_mock_test(format!(r#"GPIO_SETUP 6.2, "{}""#, mode), &[602]);
        }
        for mode in &["in-pull-up", "IN-PULL-UP"] {
            do_mock_test(format!(r#"GPIO_SETUP 7, "{}""#, mode), &[703]);
            do_mock_test(format!(r#"GPIO_SETUP 7.2, "{}""#, mode), &[703]);
        }
        for mode in &["out", "OUT"] {
            do_mock_test(format!(r#"GPIO_SETUP 8, "{}""#, mode), &[804]);
            do_mock_test(format!(r#"GPIO_SETUP 8.2, "{}""#, mode), &[804]);
        }
    }

    #[test]
    fn test_gpio_setup_multiple() {
        do_mock_test(r#"GPIO_SETUP 18, "IN-PULL-UP": GPIO_SETUP 10, "OUT""#, &[1803, 1004]);
    }

    #[test]
    fn test_gpio_setup_errors() {
        check_stmt_compilation_err("1:1: GPIO_SETUP expected pin%, mode$", r#"GPIO_SETUP"#);
        check_stmt_compilation_err("1:1: GPIO_SETUP expected pin%, mode$", r#"GPIO_SETUP 1"#);
        check_stmt_compilation_err("1:15: expected STRING but found INTEGER", r#"GPIO_SETUP 1; 2"#);
        check_stmt_compilation_err("1:1: GPIO_SETUP expected pin%, mode$", r#"GPIO_SETUP 1, 2, 3"#);

        check_pin_validation("1:12: ", "1:12: ", r#"GPIO_SETUP _PIN_, "IN""#);

        check_stmt_err(r#"1:15: Unknown pin mode IN-OUT"#, r#"GPIO_SETUP 1, "IN-OUT""#);
    }

    #[test]
    fn test_gpio_clear_all() {
        do_mock_test("GPIO_CLEAR", &[-1]);
    }

    #[test]
    fn test_gpio_clear_one() {
        do_mock_test("GPIO_CLEAR 4", &[405]);
        do_mock_test("GPIO_CLEAR 4.1", &[405]);
    }

    #[test]
    fn test_gpio_clear_errors() {
        check_stmt_compilation_err("1:1: GPIO_CLEAR expected <> | <pin%>", r#"GPIO_CLEAR 1,"#);
        check_stmt_compilation_err("1:1: GPIO_CLEAR expected <> | <pin%>", r#"GPIO_CLEAR 1, 2"#);

        check_pin_validation("1:12: ", "1:12: ", r#"GPIO_CLEAR _PIN_"#);
    }

    #[test]
    fn test_gpio_read_ok() {
        do_mock_test_with_vars(
            "__GPIO_MOCK_DATA(0) = 310
            __GPIO_MOCK_DATA(2) = 311
            GPIO_WRITE 5, GPIO_READ(3.1)
            GPIO_WRITE 7, GPIO_READ(pin)",
            &[310, 520, 311, 721],
            [("pin", 3.into())],
        );
    }

    #[test]
    fn test_gpio_read_errors() {
        check_expr_compilation_error("1:10: GPIO_READ expected pin%", r#"GPIO_READ()"#);
        check_expr_compilation_error("1:10: GPIO_READ expected pin%", r#"GPIO_READ(1, 2)"#);

        check_pin_validation("1:15: ", "1:15: ", r#"v = GPIO_READ(_PIN_)"#);
    }

    #[test]
    fn test_gpio_write_ok() {
        do_mock_test("GPIO_WRITE 3, TRUE: GPIO_WRITE 3.1, FALSE", &[321, 320]);
    }

    #[test]
    fn test_gpio_write_errors() {
        check_stmt_compilation_err("1:1: GPIO_WRITE expected pin%, value?", r#"GPIO_WRITE"#);
        check_stmt_compilation_err("1:1: GPIO_WRITE expected pin%, value?", r#"GPIO_WRITE 2,"#);
        check_stmt_compilation_err(
            "1:1: GPIO_WRITE expected pin%, value?",
            r#"GPIO_WRITE 1, TRUE, 2"#,
        );
        check_stmt_compilation_err(
            "1:1: GPIO_WRITE expected pin%, value?",
            r#"GPIO_WRITE 1; TRUE"#,
        );

        check_pin_validation("1:12: ", "1:12: ", r#"GPIO_WRITE _PIN_, TRUE"#);

        check_stmt_compilation_err(
            "1:15: expected BOOLEAN but found INTEGER",
            r#"GPIO_WRITE 1, 5"#,
        );
    }
}
