// EndBASIC
// Copyright 2021 Julio Merino
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

//! GPIO access functions and commands for EndBASIC.

use async_trait::async_trait;
use endbasic_core2::{
    ArgSep, ArgSepSyntax, CallError, CallResult, Callable, CallableMetadata,
    CallableMetadataBuilder, ExprType, RequiredValueSyntax, Scope, SingularArgSyntax,
};
use std::any::Any;
use std::borrow::Cow;
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

mod fakes;
pub use fakes::{MockPins, NoopPins};

use crate::{Clearable, MachineBuilder};

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
    fn from_i32(i: i32) -> Result<Self, String> {
        if i < 0 {
            return Err(format!("Pin number {} must be positive", i));
        }
        if i > u8::MAX as i32 {
            return Err(format!("Pin number {} is too large", i));
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
    fn parse(s: &str) -> Result<PinMode, String> {
        match s.to_ascii_uppercase().as_ref() {
            "IN" => Ok(PinMode::In),
            "IN-PULL-UP" => Ok(PinMode::InPullUp),
            "IN-PULL-DOWN" => Ok(PinMode::InPullDown),
            "OUT" => Ok(PinMode::Out),
            s => Err(format!("Unknown pin mode {}", s)),
        }
    }
}

fn parse_pin(scope: &Scope<'_>, narg: u8) -> CallResult<Pin> {
    Pin::from_i32(scope.get_integer(narg)).map_err(|e| CallError::Syntax(scope.get_pos(narg), e))
}

fn parse_pin_mode(scope: &Scope<'_>, narg: u8) -> CallResult<PinMode> {
    PinMode::parse(scope.get_string(narg)).map_err(|e| CallError::Syntax(scope.get_pos(narg), e))
}

/// Generic abstraction over a GPIO chip to back all EndBASIC commands.
pub trait Pins {
    /// Returns `self` as `&dyn Any` to allow downcasting to a concrete type.
    fn as_any(&self) -> &dyn Any;

    /// Returns `self` as `&mut dyn Any` to allow downcasting to a concrete type.
    fn as_any_mut(&mut self) -> &mut dyn Any;

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
    fn reset_state(&self) {
        let _ = self.pins.borrow_mut().clear_all();
    }
}

/// The `GPIO_SETUP` command.
pub struct GpioSetupCommand {
    metadata: Rc<CallableMetadata>,
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
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(2, scope.nargs());
        let pin = parse_pin(&scope, 0)?;
        let mode = parse_pin_mode(&scope, 1)?;

        self.pins.borrow_mut().setup(pin, mode).map_err(CallError::from)?;
        Ok(())
    }
}

/// The `GPIO_CLEAR` command.
pub struct GpioClearCommand {
    metadata: Rc<CallableMetadata>,
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
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        if scope.nargs() == 0 {
            self.pins.borrow_mut().clear_all().map_err(CallError::from)?;
        } else {
            debug_assert_eq!(1, scope.nargs());
            let pin = parse_pin(&scope, 0)?;

            self.pins.borrow_mut().clear(pin).map_err(CallError::from)?;
        }

        Ok(())
    }
}

/// The `GPIO_READ` function.
pub struct GpioReadFunction {
    metadata: Rc<CallableMetadata>,
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
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(1, scope.nargs());
        let pin = parse_pin(&scope, 0)?;

        let value = self.pins.borrow_mut().read(pin).map_err(CallError::from)?;
        scope.return_boolean(value)
    }
}

/// The `GPIO_WRITE` command.
pub struct GpioWriteCommand {
    metadata: Rc<CallableMetadata>,
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
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(2, scope.nargs());
        let pin = parse_pin(&scope, 0)?;
        let value = scope.get_boolean(1);

        self.pins.borrow_mut().write(pin, value).map_err(CallError::from)?;
        Ok(())
    }
}

/// The `GPIO_MOCK_INJECT` command.
pub struct GpioMockInjectCommand {
    metadata: Rc<CallableMetadata>,
    pins: Rc<RefCell<dyn Pins>>,
}

impl GpioMockInjectCommand {
    /// Creates a new instance of the command.
    pub fn new(pins: Rc<RefCell<dyn Pins>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GPIO_MOCK_INJECT")
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
                                name: Cow::Borrowed("high"),
                                vtype: ExprType::Boolean,
                            },
                            ArgSepSyntax::End,
                        ),
                    ],
                    None,
                )])
                .with_category(CATEGORY)
                .with_description(
                    "Pre-seeds a GPIO_READ result for testing.
This command is only available when EndBASIC is started with --gpio-pins=mock.  It pre-seeds \
the next GPIO_READ call for the given pin% to return the given high? value.",
                )
                .build(),
            pins,
        })
    }
}

#[async_trait(?Send)]
impl Callable for GpioMockInjectCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(2, scope.nargs());
        let pin = parse_pin(&scope, 0)?;
        let high = scope.get_boolean(1);

        self.pins
            .borrow_mut()
            .as_any_mut()
            .downcast_mut::<MockPins>()
            .expect("Only registered for mock backend")
            .inject_read(pin, high);
        Ok(())
    }
}

/// The `GPIO_MOCK_TRACE` function.
pub struct GpioMockTraceFunction {
    metadata: Rc<CallableMetadata>,
    pins: Rc<RefCell<dyn Pins>>,
}

impl GpioMockTraceFunction {
    /// Creates a new instance of the function.
    pub fn new(pins: Rc<RefCell<dyn Pins>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GPIO_MOCK_TRACE")
                .with_return_type(ExprType::Text)
                .with_syntax(&[(&[], None)])
                .with_category(CATEGORY)
                .with_description(
                    "Returns the GPIO operation trace for testing.
This function is only available when EndBASIC is started with --gpio-pins=mock.  It returns a \
space-separated list of integers representing the ordered record of all GPIO operations \
performed since the last reset.",
                )
                .build(),
            pins,
        })
    }
}

#[async_trait(?Send)]
impl Callable for GpioMockTraceFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(0, scope.nargs());
        let pins = self.pins.borrow();
        let mock =
            pins.as_any().downcast_ref::<MockPins>().expect("Only registered for mock backend");
        let result = mock.trace().iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" ");
        scope.return_string(result)
    }
}

/// Adds all symbols provided by this module to the given `machine`.
pub fn add_all(machine: &mut MachineBuilder, pins: Rc<RefCell<dyn Pins>>) {
    if pins.borrow().as_any().downcast_ref::<MockPins>().is_some() {
        machine.add_callable(GpioMockInjectCommand::new(pins.clone()));
        machine.add_callable(GpioMockTraceFunction::new(pins.clone()));
    }

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
    use futures_lite::future::block_on;

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

    /// Creates a machine backed by `MockPins` pre-seeded with `reads` and returns both the machine
    /// and a handle to inspect the trace afterwards.
    fn make_mock_machine(reads: &[(u8, bool)]) -> (crate::Machine, Rc<RefCell<MockPins>>) {
        let mock_pins = Rc::new(RefCell::new(MockPins::default()));
        for &(pin, high) in reads {
            mock_pins.borrow_mut().inject_read(Pin(pin), high);
        }
        let pins: Rc<RefCell<dyn Pins>> = mock_pins.clone();
        let machine = MachineBuilder::default().with_gpio_pins(pins).build();
        (machine, mock_pins)
    }

    /// Runs `code` in a machine backed by MockPins pre-seeded with `reads` and asserts that the
    /// resulting trace equals `expected_trace`.
    fn do_mock_test(code: &str, reads: &[(u8, bool)], expected_trace: &[i32]) {
        let (mut machine, mock_pins) = make_mock_machine(reads);
        machine.compile(&mut code.as_bytes()).unwrap();
        let _ = block_on(machine.exec()).unwrap();
        assert_eq!(expected_trace, mock_pins.borrow().trace());
    }

    /// Tests that all GPIO operations delegate to the real pins implementation, which defaults to
    /// the no-op backend when using the tester.  All other tests in this file use MockPins via
    /// `make_mock_machine` to validate operation.
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
            do_mock_test(&format!(r#"GPIO_SETUP 5, "{}""#, mode), &[], &[501]);
            do_mock_test(&format!(r#"GPIO_SETUP 5.2, "{}""#, mode), &[], &[501]);
        }
        for mode in &["in-pull-down", "IN-PULL-DOWN"] {
            do_mock_test(&format!(r#"GPIO_SETUP 6, "{}""#, mode), &[], &[602]);
            do_mock_test(&format!(r#"GPIO_SETUP 6.2, "{}""#, mode), &[], &[602]);
        }
        for mode in &["in-pull-up", "IN-PULL-UP"] {
            do_mock_test(&format!(r#"GPIO_SETUP 7, "{}""#, mode), &[], &[703]);
            do_mock_test(&format!(r#"GPIO_SETUP 7.2, "{}""#, mode), &[], &[703]);
        }
        for mode in &["out", "OUT"] {
            do_mock_test(&format!(r#"GPIO_SETUP 8, "{}""#, mode), &[], &[804]);
            do_mock_test(&format!(r#"GPIO_SETUP 8.2, "{}""#, mode), &[], &[804]);
        }
    }

    #[test]
    fn test_gpio_setup_multiple() {
        do_mock_test(r#"GPIO_SETUP 18, "IN-PULL-UP": GPIO_SETUP 10, "OUT""#, &[], &[1803, 1004]);
    }

    #[test]
    fn test_gpio_setup_errors() {
        check_stmt_compilation_err("1:1: GPIO_SETUP expected pin%, mode$", r#"GPIO_SETUP"#);
        check_stmt_compilation_err("1:1: GPIO_SETUP expected pin%, mode$", r#"GPIO_SETUP 1"#);
        check_stmt_compilation_err("1:13: GPIO_SETUP expected pin%, mode$", r#"GPIO_SETUP 1; 2"#);
        check_stmt_compilation_err("1:1: GPIO_SETUP expected pin%, mode$", r#"GPIO_SETUP 1, 2, 3"#);

        check_pin_validation("1:12: ", "1:12: ", r#"GPIO_SETUP _PIN_, "IN""#);

        check_stmt_err(r#"1:15: Unknown pin mode IN-OUT"#, r#"GPIO_SETUP 1, "IN-OUT""#);
    }

    #[test]
    fn test_gpio_clear_all() {
        do_mock_test("GPIO_CLEAR", &[], &[-1]);
    }

    #[test]
    fn test_gpio_clear_one() {
        do_mock_test("GPIO_CLEAR 4", &[], &[405]);
        do_mock_test("GPIO_CLEAR 4.1", &[], &[405]);
    }

    #[test]
    fn test_gpio_clear_errors() {
        check_stmt_compilation_err("1:1: GPIO_CLEAR expected <> | <pin%>", r#"GPIO_CLEAR 1,"#);
        check_stmt_compilation_err("1:1: GPIO_CLEAR expected <> | <pin%>", r#"GPIO_CLEAR 1, 2"#);

        check_pin_validation("1:12: ", "1:12: ", r#"GPIO_CLEAR _PIN_"#);
    }

    #[test]
    fn test_gpio_read_ok() {
        // Read pin 3 (low → GPIO_WRITE 5 low), then read pin 3 (high → GPIO_WRITE 7 high).
        // GPIO_READ evaluates before GPIO_WRITE, so trace is: read3low, write5low, read3high, write7high.
        do_mock_test(
            "GPIO_WRITE 5, GPIO_READ(3.1): GPIO_WRITE 7, GPIO_READ(3)",
            &[(3, false), (3, true)],
            &[310, 520, 311, 721],
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
        do_mock_test("GPIO_WRITE 3, TRUE: GPIO_WRITE 3.1, FALSE", &[], &[321, 320]);
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
            "1:13: GPIO_WRITE expected pin%, value?",
            r#"GPIO_WRITE 1; TRUE"#,
        );

        check_pin_validation("1:12: ", "1:12: ", r#"GPIO_WRITE _PIN_, TRUE"#);

        check_stmt_compilation_err(
            "1:15: Expected BOOLEAN but found INTEGER",
            r#"GPIO_WRITE 1, 5"#,
        );
    }
}
