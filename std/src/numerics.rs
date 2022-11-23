// EndBASIC
// Copyright 2020 Julio Merino
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

//! Numerical functions for EndBASIC.

use async_trait::async_trait;
use endbasic_core::ast::{
    ArgSep, ArgSpan, BuiltinCallSpan, Expr, FunctionCallSpan, Value, VarType,
};
use endbasic_core::eval::eval_all;
use endbasic_core::exec::{Clearable, Machine};
use endbasic_core::syms::{
    CallError, CallableMetadata, CallableMetadataBuilder, Command, CommandResult, Function,
    FunctionResult, Symbols,
};
use rand::rngs::SmallRng;
use rand::{RngCore, SeedableRng};
use std::cell::RefCell;
use std::cmp::Ordering;
use std::rc::Rc;

/// Category description for all symbols provided by this module.
const CATEGORY: &str = "Numerical functions";

/// Indicates the calculation mode for trigonometric functions.
pub enum AngleMode {
    /// Specifies degrees mode of calculation.
    Degrees,

    /// Specifies radians mode of calculation.
    Radians,
}

struct ClearableAngleMode {
    angle_mode: Rc<RefCell<AngleMode>>,
}

impl Clearable for ClearableAngleMode {
    fn reset_state(&self, _syms: &mut Symbols) {
        *self.angle_mode.borrow_mut() = AngleMode::Radians;
    }
}

/// Gets the single argument to a trigonometric function, which is its angle.  Applies units
/// conversion based on `angle_mode`.
async fn get_angle(
    args: &[Expr],
    symbols: &mut Symbols,
    angle_mode: &AngleMode,
) -> Result<f64, CallError> {
    let values = eval_all(args, symbols).await?;
    let angle = match values.as_slice() {
        [v] => v
            .as_f64()
            .map_err(|e| CallError::ArgumentError(args[0].start_pos(), format!("{}", e)))?,
        _ => return Err(CallError::SyntaxError),
    };
    match angle_mode {
        AngleMode::Degrees => Ok(angle.to_radians()),
        AngleMode::Radians => Ok(angle),
    }
}

/// Tracks the state of the PRNG used by the random number manipulation functions and commands.
///
/// The PRNG implemented here is intentionally simplistic and has no cryptographical guarantees.
pub struct Prng {
    prng: SmallRng,
    last: u32,
}

impl Prng {
    /// Generates a new PRNG based on system entropy.
    pub fn new_from_entryopy() -> Self {
        let mut prng = SmallRng::from_entropy();
        let last = prng.next_u32();
        Self { prng, last }
    }

    /// Generates a new PRNG based on the given seed.
    pub fn new_from_seed(seed: i32) -> Self {
        let mut prng = SmallRng::seed_from_u64(seed as u64);
        let last = prng.next_u32();
        Self { prng, last }
    }

    /// Returns the previously returned random number.
    fn last(&self) -> f64 {
        (self.last as f64) / (std::u32::MAX as f64)
    }

    /// Computes the next random number and returns it.
    fn next(&mut self) -> f64 {
        self.last = self.prng.next_u32();
        self.last()
    }
}

/// The `ATN` function.
pub struct AtnFunction {
    metadata: CallableMetadata,
    angle_mode: Rc<RefCell<AngleMode>>,
}

impl AtnFunction {
    /// Creates a new instance of the function.
    pub fn new(angle_mode: Rc<RefCell<AngleMode>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("ATN", VarType::Double)
                .with_syntax("n<%|#>")
                .with_category(CATEGORY)
                .with_description(
                    "Computes the arc-tangent of a number.
The resulting angle is measured in degrees or radians depending on the angle mode as selected by \
the DEG and RAD commands.",
                )
                .build(),
            angle_mode,
        })
    }
}

#[async_trait(?Send)]
impl Function for AtnFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(&span.args, symbols).await?;
        let n = match args.as_slice() {
            [Value::Double(n)] => *n,
            [Value::Integer(n)] => *n as f64,
            _ => return Err(CallError::SyntaxError),
        };
        match *self.angle_mode.borrow() {
            AngleMode::Degrees => Ok(Value::Double(n.atan().to_degrees())),
            AngleMode::Radians => Ok(Value::Double(n.atan())),
        }
    }
}

/// The `CINT` function.
pub struct CintFunction {
    metadata: CallableMetadata,
}

impl CintFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("CINT", VarType::Integer)
                .with_syntax("expr<%|#>")
                .with_category(CATEGORY)
                .with_description(
                    "Casts the given numeric expression to an integer (with rounding).
When casting a double value to an integer, the double value is first rounded to the closest \
integer.  For example, 4.4 becomes 4, but both 4.5 and 4.6 become 5.",
                )
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for CintFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        if span.args.len() != 1 {
            return Err(CallError::SyntaxError);
        }
        let mut args = eval_all(&span.args, symbols).await?;
        let value =
            args.pop().unwrap().maybe_cast(VarType::Integer).map_err(|e| {
                CallError::ArgumentError(span.args[0].start_pos(), format!("{}", e))
            })?;
        debug_assert!(args.is_empty());
        match value {
            Value::Double(_) | Value::Integer(_) => Ok(value),
            _ => Err(CallError::SyntaxError),
        }
    }
}

/// The `COS` function.
pub struct CosFunction {
    metadata: CallableMetadata,
    angle_mode: Rc<RefCell<AngleMode>>,
}

impl CosFunction {
    /// Creates a new instance of the function.
    pub fn new(angle_mode: Rc<RefCell<AngleMode>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("COS", VarType::Double)
                .with_syntax("angle<%|#>")
                .with_category(CATEGORY)
                .with_description(
                    "Computes the cosine of an angle.
The input angle% or angle# is measured in degrees or radians depending on the angle mode as \
selected by the DEG and RAD commands.",
                )
                .build(),
            angle_mode,
        })
    }
}

#[async_trait(?Send)]
impl Function for CosFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        let angle = get_angle(&span.args, symbols, &self.angle_mode.borrow()).await?;
        Ok(Value::Double(angle.cos()))
    }
}

/// The `DEG` command.
pub struct DegCommand {
    metadata: CallableMetadata,
    angle_mode: Rc<RefCell<AngleMode>>,
}

impl DegCommand {
    /// Creates a new instance of the command.
    pub fn new(angle_mode: Rc<RefCell<AngleMode>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("DEG", VarType::Void)
                .with_syntax("")
                .with_category(CATEGORY)
                .with_description(
                    "Sets degrees mode of calculation.
The default condition for the trigonometric functions is to use radians.  DEG configures the \
environment to use degrees until instructed otherwise.",
                )
                .build(),
            angle_mode,
        })
    }
}

#[async_trait(?Send)]
impl Command for DegCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &BuiltinCallSpan, _machine: &mut Machine) -> CommandResult {
        if !span.args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        *self.angle_mode.borrow_mut() = AngleMode::Degrees;
        Ok(())
    }
}

/// The `INT` function.
pub struct IntFunction {
    metadata: CallableMetadata,
}

impl IntFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("INT", VarType::Integer)
                .with_syntax("expr<%|#>")
                .with_category(CATEGORY)
                .with_description(
                    "Casts the given numeric expression to an integer (with truncation).
When casting a double value to an integer, the double value is first truncated to the smallest
integer that is not larger than the double value.  For example, all of 4.4, 4.5 and 4.6 become 4.",
                )
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for IntFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        if span.args.len() != 1 {
            return Err(CallError::SyntaxError);
        }
        let mut args = eval_all(&span.args, symbols).await?;
        let value = match args.pop().unwrap() {
            Value::Double(d) => Value::Double(d.floor()),
            v => v,
        };
        debug_assert!(args.is_empty());
        let value = value
            .maybe_cast(VarType::Integer)
            .map_err(|e| CallError::ArgumentError(span.args[0].start_pos(), format!("{}", e)))?;
        match value {
            Value::Double(_) | Value::Integer(_) => Ok(value),
            _ => Err(CallError::SyntaxError),
        }
    }
}

/// The `MAX` function.
pub struct MaxFunction {
    metadata: CallableMetadata,
}

impl MaxFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("MAX", VarType::Double)
                .with_syntax("expr<%|#>[, .., expr<%|#>]")
                .with_category(CATEGORY)
                .with_description("Returns the maximum number out of a set of numbers.")
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for MaxFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        if span.args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        let args = eval_all(&span.args, symbols).await?;
        let mut max = f64::MIN;
        for (arg, value) in span.args.iter().zip(args) {
            let n = value
                .as_f64()
                .map_err(|e| CallError::ArgumentError(arg.start_pos(), format!("{}", e)))?;
            if n > max {
                max = n;
            }
        }
        Ok(Value::Double(max))
    }
}

/// The `MIN` function.
pub struct MinFunction {
    metadata: CallableMetadata,
}

impl MinFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("MIN", VarType::Double)
                .with_syntax("expr<%|#>[, .., expr<%|#>]")
                .with_category(CATEGORY)
                .with_description("Returns the minimum number out of a set of numbers.")
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for MinFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        if span.args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        let args = eval_all(&span.args, symbols).await?;
        let mut min = f64::MAX;
        for (arg, value) in span.args.iter().zip(args) {
            let n = value
                .as_f64()
                .map_err(|e| CallError::ArgumentError(arg.start_pos(), format!("{}", e)))?;
            if n < min {
                min = n;
            }
        }
        Ok(Value::Double(min))
    }
}

/// The `PI` function.
pub struct PiFunction {
    metadata: CallableMetadata,
}

impl PiFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("PI", VarType::Double)
                .with_syntax("")
                .with_category(CATEGORY)
                .with_description("Returns the Archimedes' constant.")
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for PiFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, _symbols: &mut Symbols) -> FunctionResult {
        if !span.args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        Ok(Value::Double(std::f64::consts::PI))
    }
}

/// The `RAD` command.
pub struct RadCommand {
    metadata: CallableMetadata,
    angle_mode: Rc<RefCell<AngleMode>>,
}

impl RadCommand {
    /// Creates a new instance of the command.
    pub fn new(angle_mode: Rc<RefCell<AngleMode>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("RAD", VarType::Void)
                .with_syntax("")
                .with_category(CATEGORY)
                .with_description(
                    "Sets radians mode of calculation.
The default condition for the trigonometric functions is to use radians but it can be set to \
degrees with the DEG command.  RAD restores the environment to use radians mode.",
                )
                .build(),
            angle_mode,
        })
    }
}

#[async_trait(?Send)]
impl Command for RadCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &BuiltinCallSpan, _machine: &mut Machine) -> CommandResult {
        if !span.args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        *self.angle_mode.borrow_mut() = AngleMode::Radians;
        Ok(())
    }
}

/// The `RANDOMIZE` command.
pub struct RandomizeCommand {
    metadata: CallableMetadata,
    prng: Rc<RefCell<Prng>>,
}

impl RandomizeCommand {
    /// Creates a new command that updates `code` with the exit code once called.
    pub fn new(prng: Rc<RefCell<Prng>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("RANDOMIZE", VarType::Void)
                .with_syntax("[seed%]")
                .with_category(CATEGORY)
                .with_description(
                    "Reinitializes the pseudo-random number generator.
If no seed is given, uses system entropy to create a new sequence of random numbers.
WARNING: These random numbers offer no cryptographic guarantees.",
                )
                .build(),
            prng,
        })
    }
}

#[async_trait(?Send)]
impl Command for RandomizeCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        match span.args.as_slice() {
            [] => {
                *self.prng.borrow_mut() = Prng::new_from_entryopy();
            }
            [ArgSpan { expr: Some(expr), sep: ArgSep::End, .. }] => {
                let n = expr.eval(machine.get_mut_symbols()).await?;
                let n = n
                    .as_i32()
                    .map_err(|e| CallError::ArgumentError(expr.start_pos(), format!("{}", e)))?;
                *self.prng.borrow_mut() = Prng::new_from_seed(n);
            }
            _ => return Err(CallError::SyntaxError),
        };
        Ok(())
    }
}

/// The `RND` function.
pub struct RndFunction {
    metadata: CallableMetadata,
    prng: Rc<RefCell<Prng>>,
}

impl RndFunction {
    /// Creates a new instance of the function.
    pub fn new(prng: Rc<RefCell<Prng>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("RND", VarType::Double)
                .with_syntax("n%")
                .with_category(CATEGORY)
                .with_description(
                    "Returns a random number in the [0..1] range.
If n% is zero, returns the previously generated random number.  If n% is positive, returns a new \
random number.
If you need to generate an integer random number within a specific range, say [0..100], compute it \
with an expression like CINT%(RND#(1) * 100.0).
WARNING: These random numbers offer no cryptographic guarantees.",
                )
                .build(),
            prng,
        })
    }
}

#[async_trait(?Send)]
impl Function for RndFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(&span.args, symbols).await?;
        match args.as_slice() {
            [] => Ok(Value::Double(self.prng.borrow_mut().next())),
            [n] => {
                let n = n.as_i32().map_err(|e| {
                    CallError::ArgumentError(span.args[0].start_pos(), format!("{}", e))
                })?;
                match n.cmp(&0) {
                    Ordering::Equal => Ok(Value::Double(self.prng.borrow_mut().last())),
                    Ordering::Greater => Ok(Value::Double(self.prng.borrow_mut().next())),
                    Ordering::Less => Err(CallError::ArgumentError(
                        span.args[0].start_pos(),
                        "n% cannot be negative".to_owned(),
                    )),
                }
            }
            _ => Err(CallError::SyntaxError),
        }
    }
}

/// The `SIN` function.
pub struct SinFunction {
    metadata: CallableMetadata,
    angle_mode: Rc<RefCell<AngleMode>>,
}

impl SinFunction {
    /// Creates a new instance of the function.
    pub fn new(angle_mode: Rc<RefCell<AngleMode>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("SIN", VarType::Double)
                .with_syntax("angle<%|#>")
                .with_category(CATEGORY)
                .with_description(
                    "Computes the sine of an angle.
The input angle% or angle# is measured in degrees or radians depending on the angle mode as \
selected by the DEG and RAD commands.",
                )
                .build(),
            angle_mode,
        })
    }
}

#[async_trait(?Send)]
impl Function for SinFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        let angle = get_angle(&span.args, symbols, &self.angle_mode.borrow()).await?;
        Ok(Value::Double(angle.sin()))
    }
}

/// The `SQR` function.
pub struct SqrFunction {
    metadata: CallableMetadata,
}

impl SqrFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("SQR", VarType::Double)
                .with_syntax("num<%|#>")
                .with_category(CATEGORY)
                .with_description("Computes the square root of the given number.")
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for SqrFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(&span.args, symbols).await?;
        let num = match args.as_slice() {
            [Value::Integer(i)] => *i as f64,
            [Value::Double(d)] => *d,
            _ => return Err(CallError::SyntaxError),
        };
        if num < 0.0 {
            return Err(CallError::ArgumentError(
                span.args[0].start_pos(),
                "Cannot take square root of a negative number".to_owned(),
            ));
        }
        Ok(Value::Double(num.sqrt()))
    }
}

/// The `TAN` function.
pub struct TanFunction {
    metadata: CallableMetadata,
    angle_mode: Rc<RefCell<AngleMode>>,
}

impl TanFunction {
    /// Creates a new instance of the function.
    pub fn new(angle_mode: Rc<RefCell<AngleMode>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("TAN", VarType::Double)
                .with_syntax("angle<%|#>")
                .with_category(CATEGORY)
                .with_description(
                    "Computes the tangent of an angle.
The input angle% or angle# is measured in degrees or radians depending on the angle mode as \
selected by the DEG and RAD commands.",
                )
                .build(),
            angle_mode,
        })
    }
}

#[async_trait(?Send)]
impl Function for TanFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        let angle = get_angle(&span.args, symbols, &self.angle_mode.borrow()).await?;
        Ok(Value::Double(angle.tan()))
    }
}

/// Adds all symbols provided by this module to the given `machine`.
pub fn add_all(machine: &mut Machine) {
    let angle_mode = Rc::from(RefCell::from(AngleMode::Radians));
    let prng = Rc::from(RefCell::from(Prng::new_from_entryopy()));
    machine.add_clearable(Box::from(ClearableAngleMode { angle_mode: angle_mode.clone() }));
    machine.add_command(RandomizeCommand::new(prng.clone()));
    machine.add_command(DegCommand::new(angle_mode.clone()));
    machine.add_function(AtnFunction::new(angle_mode.clone()));
    machine.add_function(CintFunction::new());
    machine.add_function(CosFunction::new(angle_mode.clone()));
    machine.add_function(IntFunction::new());
    machine.add_function(MaxFunction::new());
    machine.add_function(MinFunction::new());
    machine.add_function(PiFunction::new());
    machine.add_command(RadCommand::new(angle_mode.clone()));
    machine.add_function(RndFunction::new(prng));
    machine.add_function(SinFunction::new(angle_mode.clone()));
    machine.add_function(SqrFunction::new());
    machine.add_function(TanFunction::new(angle_mode));
}

#[cfg(test)]
mod tests {
    use crate::testutils::*;

    #[test]
    fn test_atn() {
        check_expr_ok(123f64.atan(), "ATN(123)");
        check_expr_ok(45.5f64.atan(), "ATN(45.5)");

        check_expr_error("1:10: In call to ATN: expected n<%|#>", "ATN()");
        check_expr_error("1:10: In call to ATN: expected n<%|#>", "ATN(FALSE)");
        check_expr_error("1:10: In call to ATN: expected n<%|#>", "ATN(3, 4)");
    }

    #[test]
    fn test_cint() {
        check_expr_ok(0, "CINT(0.1)");
        check_expr_ok(0, "CINT(-0.1)");
        check_expr_ok(1, "CINT(0.9)");
        check_expr_ok(-1, "CINT(-0.9)");

        check_expr_error("1:10: In call to CINT: expected expr<%|#>", "CINT()");
        check_expr_error("1:10: In call to CINT: expected expr<%|#>", "CINT(FALSE)");
        check_expr_error("1:10: In call to CINT: expected expr<%|#>", "CINT(3.0, 4)");

        check_expr_error(
            "1:10: In call to CINT: 1:15: Cannot cast -1234567890123456 to integer due to overflow",
            "CINT(-1234567890123456.0)",
        );
    }

    #[test]
    fn test_cos() {
        check_expr_ok(123f64.cos(), "COS(123)");
        check_expr_ok(45.5f64.cos(), "COS(45.5)");

        check_expr_error("1:10: In call to COS: expected angle<%|#>", "COS()");
        check_expr_error("1:10: In call to COS: 1:14: FALSE is not a number", "COS(FALSE)");
        check_expr_error("1:10: In call to COS: expected angle<%|#>", "COS(3, 4)");
    }

    #[test]
    fn test_deg_rad_commands() {
        let mut t = Tester::default();
        t.run("result = SIN(90)").expect_var("result", 90f64.sin()).check();
        t.run("DEG: result = SIN(90)").expect_var("result", 1.0).check();
        t.run("RAD: result = SIN(90)").expect_var("result", 90f64.sin()).check();
    }

    #[test]
    fn test_deg_rad_reset_on_clear() {
        let mut t = Tester::default();
        t.run("DEG").check();
        t.get_machine().clear();
        t.run("result = SIN(90)").expect_clear().expect_var("result", 90f64.sin()).check();
    }

    #[test]
    fn test_deg_rad_errors() {
        check_stmt_err("1:1: In call to DEG: expected no arguments", "DEG 1");
        check_stmt_err("1:1: In call to RAD: expected no arguments", "RAD 1");
    }

    #[test]
    fn test_int() {
        check_expr_ok(0, "INT(0.1)");
        check_expr_ok(-1, "INT(-0.1)");
        check_expr_ok(0, "INT(0.9)");
        check_expr_ok(-1, "INT(-0.9)");

        check_expr_error("1:10: In call to INT: expected expr<%|#>", "INT()");
        check_expr_error("1:10: In call to INT: expected expr<%|#>", "INT(FALSE)");
        check_expr_error("1:10: In call to INT: expected expr<%|#>", "INT(3.0, 4)");

        check_expr_error(
            "1:10: In call to INT: 1:14: Cannot cast -1234567890123456 to integer due to overflow",
            "INT(-1234567890123456.0)",
        );
    }

    #[test]
    fn test_max() {
        check_expr_ok(0.0, "MAX(0)");
        check_expr_ok(0.0, "MAX(0, 0)");

        check_expr_ok(0.0, "MAX(0.0)");
        check_expr_ok(0.0, "MAX(0.0, 0.0)");

        check_expr_ok(1.0, "MAX(1)");
        check_expr_ok(5.0, "MAX(5, 3, 4)");
        check_expr_ok(-3.0, "MAX(-5, -3, -4)");

        check_expr_ok(1.0, "MAX(1.0)");
        check_expr_ok(5.3, "MAX(5.3, 3.5, 4.2)");
        check_expr_ok(-3.5, "MAX(-5.3, -3.5, -4.2)");

        check_expr_ok(2.5, "MAX(1, 0.5, 2.5, 2)");

        check_expr_error("1:10: In call to MAX: expected expr<%|#>[, .., expr<%|#>]", "MAX()");
        check_expr_error("1:10: In call to MAX: 1:14: FALSE is not a number", "MAX(FALSE)");
    }

    #[test]
    fn test_min() {
        check_expr_ok(0.0, "MIN(0)");
        check_expr_ok(0.0, "MIN(0, 0)");

        check_expr_ok(0.0, "MIN(0.0)");
        check_expr_ok(0.0, "MIN(0.0, 0.0)");

        check_expr_ok(1.0, "MIN(1)");
        check_expr_ok(3.0, "MIN(5, 3, 4)");
        check_expr_ok(-5.0, "MIN(-5, -3, -4)");

        check_expr_ok(1.0, "MIN(1.0)");
        check_expr_ok(3.5, "MIN(5.3, 3.5, 4.2)");
        check_expr_ok(-5.3, "MIN(-5.3, -3.5, -4.2)");

        check_expr_ok(0.5, "MIN(1, 0.5, 2.5, 2)");

        check_expr_error("1:10: In call to MIN: expected expr<%|#>[, .., expr<%|#>]", "MIN()");
        check_expr_error("1:10: In call to MIN: 1:14: FALSE is not a number", "MIN(FALSE)");
    }

    #[test]
    fn test_pi() {
        check_expr_ok(std::f64::consts::PI, "PI");

        check_expr_error("1:10: In call to PI: expected no arguments nor parenthesis", "PI()");
        check_expr_error("1:10: In call to PI: expected no arguments nor parenthesis", "PI(3)");
    }

    #[test]
    fn test_randomize_and_rnd() {
        // These tests could lead to flakiness if the PRNG happens to yield the same number twice
        // in a row because we did not previously configure the seed.  It is very unlikely though,
        // and we need a way to test that the PRNG was initialized before we call RANDOMIZE.
        check_expr_ok(false, "RND(1) = RND(1)");
        check_expr_ok(false, "RND(1) = RND(10)");
        check_expr_ok(true, "RND(0) = RND(0)");

        let mut t = Tester::default();
        t.run("RANDOMIZE 10").check();

        t.run("result = RND(1)").expect_var("result", 0.7097578208683426).check();
        t.run("result = RND(1.1)").expect_var("result", 0.2205558922655312).check();
        t.run("result = RND(0)").expect_var("result", 0.2205558922655312).check();
        t.run("result = RND(10)").expect_var("result", 0.8273883964464507).check();

        t.run("RANDOMIZE 10.2").expect_var("result", 0.8273883964464507).check();

        t.run("result = RND(1)").expect_var("result", 0.7097578208683426).check();

        check_expr_error("1:10: In call to RND: expected n%", "RND(1, 7)");
        check_expr_error("1:10: In call to RND: 1:14: FALSE is not a number", "RND(FALSE)");
        check_expr_error("1:10: In call to RND: 1:14: n% cannot be negative", "RND(-1)");

        check_stmt_err("1:1: In call to RANDOMIZE: expected [seed%]", "RANDOMIZE ,");
        check_stmt_err("1:1: In call to RANDOMIZE: 1:11: TRUE is not a number", "RANDOMIZE TRUE");
    }

    #[test]
    fn test_sin() {
        check_expr_ok(123f64.sin(), "SIN(123)");
        check_expr_ok(45.5f64.sin(), "SIN(45.5)");

        check_expr_error("1:10: In call to SIN: expected angle<%|#>", "SIN()");
        check_expr_error("1:10: In call to SIN: 1:14: FALSE is not a number", "SIN(FALSE)");
        check_expr_error("1:10: In call to SIN: expected angle<%|#>", "SIN(3, 4)");
    }

    #[test]
    fn test_sqr() {
        check_expr_ok(0f64.sqrt(), "SQR(0)");
        check_expr_ok(0f64.sqrt(), "SQR(-0.0)");
        check_expr_ok(9f64.sqrt(), "SQR(9)");
        check_expr_ok(100.50f64.sqrt(), "SQR(100.50)");

        check_expr_error("1:10: In call to SQR: expected num<%|#>", "SQR()");
        check_expr_error("1:10: In call to SQR: expected num<%|#>", "SQR(FALSE)");
        check_expr_error("1:10: In call to SQR: expected num<%|#>", "SQR(3, 4)");
        check_expr_error(
            "1:10: In call to SQR: 1:14: Cannot take square root of a negative number",
            "SQR(-3)",
        );
        check_expr_error(
            "1:10: In call to SQR: 1:14: Cannot take square root of a negative number",
            "SQR(-0.1)",
        );
    }

    #[test]
    fn test_tan() {
        check_expr_ok(123f64.tan(), "TAN(123)");
        check_expr_ok(45.5f64.tan(), "TAN(45.5)");

        check_expr_error("1:10: In call to TAN: expected angle<%|#>", "TAN()");
        check_expr_error("1:10: In call to TAN: 1:14: FALSE is not a number", "TAN(FALSE)");
        check_expr_error("1:10: In call to TAN: expected angle<%|#>", "TAN(3, 4)");
    }
}
