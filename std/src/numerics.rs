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
use endbasic_core::ast::{ArgSep, Expr, Value, VarType};
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
    let args = eval_all(args, symbols).await?;
    let angle = match args.as_slice() {
        [Value::Double(n)] => *n,
        [Value::Integer(n)] => *n as f64,
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
                .with_syntax("n%|n#")
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

    async fn exec(&self, args: &[Expr], symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(args, symbols).await?;
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
                .with_syntax("angle%|angle#")
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

    async fn exec(&self, args: &[Expr], symbols: &mut Symbols) -> FunctionResult {
        let angle = get_angle(args, symbols, &self.angle_mode.borrow()).await?;
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

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], _machine: &mut Machine) -> CommandResult {
        if !args.is_empty() {
            return Err(CallError::ArgumentError("DEG takes no arguments".to_owned()));
        }
        *self.angle_mode.borrow_mut() = AngleMode::Degrees;
        Ok(())
    }
}

/// The `DTOI` function.
pub struct DtoiFunction {
    metadata: CallableMetadata,
}

impl DtoiFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("DTOI", VarType::Integer)
                .with_syntax("expr#")
                .with_category(CATEGORY)
                .with_description(
                    "Rounds the given double to the closest integer.
If the value is too small or too big to fit in the integer's range, returns the smallest or \
biggest possible integer that fits, respectively.",
                )
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for DtoiFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[Expr], symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(args, symbols).await?;
        match args.as_slice() {
            [Value::Double(n)] => Ok(Value::Integer(*n as i32)),
            _ => Err(CallError::SyntaxError),
        }
    }
}

/// The `ITOD` function.
pub struct ItodFunction {
    metadata: CallableMetadata,
}

impl ItodFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("ITOD", VarType::Double)
                .with_syntax("expr%")
                .with_category(CATEGORY)
                .with_description("Converts the given integer to a double.")
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for ItodFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[Expr], symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(args, symbols).await?;
        match args.as_slice() {
            [Value::Integer(n)] => Ok(Value::Double(*n as f64)),
            _ => Err(CallError::SyntaxError),
        }
    }
}

/// The `MIND` function.
pub struct MindFunction {
    metadata: CallableMetadata,
}

impl MindFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("MIND", VarType::Double)
                .with_syntax("expr#[, .., expr#]")
                .with_category(CATEGORY)
                .with_description("Returns the minimum number out of a set of doubles.")
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for MindFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[Expr], symbols: &mut Symbols) -> FunctionResult {
        if args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        let args = eval_all(args, symbols).await?;
        let mut min = f64::MAX;
        for arg in args {
            match arg {
                Value::Double(n) if n < min => min = n,
                Value::Double(_) => (),
                _ => return Err(CallError::SyntaxError),
            }
        }
        Ok(Value::Double(min))
    }
}

/// The `MINI` function.
pub struct MiniFunction {
    metadata: CallableMetadata,
}

impl MiniFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("MINI", VarType::Integer)
                .with_syntax("expr%[, .., expr%]")
                .with_category(CATEGORY)
                .with_description("Returns the minimum number out of a set of integers.")
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for MiniFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[Expr], symbols: &mut Symbols) -> FunctionResult {
        if args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        let args = eval_all(args, symbols).await?;
        let mut min = i32::MAX;
        for arg in args {
            match arg {
                Value::Integer(n) if n < min => min = n,
                Value::Integer(_) => (),
                _ => return Err(CallError::SyntaxError),
            }
        }
        Ok(Value::Integer(min))
    }
}

/// The `MAXD` function.
pub struct MaxdFunction {
    metadata: CallableMetadata,
}

impl MaxdFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("MAXD", VarType::Double)
                .with_syntax("expr#[, .., expr#]")
                .with_category(CATEGORY)
                .with_description("Returns the maximum number out of a set of doubles.")
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for MaxdFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[Expr], symbols: &mut Symbols) -> FunctionResult {
        if args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        let args = eval_all(args, symbols).await?;
        let mut max = f64::MIN;
        for arg in args {
            match arg {
                Value::Double(n) if n > max => max = n,
                Value::Double(_) => (),
                _ => return Err(CallError::SyntaxError),
            }
        }
        Ok(Value::Double(max))
    }
}

/// The `MAXI` function.
pub struct MaxiFunction {
    metadata: CallableMetadata,
}

impl MaxiFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("MAXI", VarType::Integer)
                .with_syntax("expr%[, .., expr%]")
                .with_category(CATEGORY)
                .with_description("Returns the maximum number out of a set of integers.")
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for MaxiFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[Expr], symbols: &mut Symbols) -> FunctionResult {
        if args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        let args = eval_all(args, symbols).await?;
        let mut max = i32::MIN;
        for arg in args {
            match arg {
                Value::Integer(n) if n > max => max = n,
                Value::Integer(_) => (),
                _ => return Err(CallError::SyntaxError),
            }
        }
        Ok(Value::Integer(max))
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

    async fn exec(&self, args: &[Expr], _symbols: &mut Symbols) -> FunctionResult {
        if !args.is_empty() {
            return Err(CallError::ArgumentError("no arguments allowed".to_owned()));
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

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], _machine: &mut Machine) -> CommandResult {
        if !args.is_empty() {
            return Err(CallError::ArgumentError("RAD takes no arguments".to_owned()));
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

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        match args {
            [] => {
                *self.prng.borrow_mut() = Prng::new_from_entryopy();
            }
            [(Some(expr), ArgSep::End)] => match expr.eval(machine.get_mut_symbols()).await? {
                Value::Integer(n) => {
                    *self.prng.borrow_mut() = Prng::new_from_seed(n);
                }
                _ => {
                    return Err(CallError::ArgumentError(
                        "Random seed must be an integer".to_owned(),
                    ))
                }
            },
            _ => {
                return Err(CallError::ArgumentError(
                    "RANDOMIZE takes zero or one argument".to_owned(),
                ))
            }
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
with an expression like DTOI%(RND#(1) * 100.0).
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

    async fn exec(&self, args: &[Expr], symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(args, symbols).await?;
        match args.as_slice() {
            [] => Ok(Value::Double(self.prng.borrow_mut().next())),
            [Value::Integer(n)] => match n.cmp(&0) {
                Ordering::Equal => Ok(Value::Double(self.prng.borrow_mut().last())),
                Ordering::Greater => Ok(Value::Double(self.prng.borrow_mut().next())),
                Ordering::Less => Err(CallError::ArgumentError("n% cannot be negative".to_owned())),
            },
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
                .with_syntax("angle%|angle#")
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

    async fn exec(&self, args: &[Expr], symbols: &mut Symbols) -> FunctionResult {
        let angle = get_angle(args, symbols, &self.angle_mode.borrow()).await?;
        Ok(Value::Double(angle.sin()))
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
                .with_syntax("angle%|angle#")
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

    async fn exec(&self, args: &[Expr], symbols: &mut Symbols) -> FunctionResult {
        let angle = get_angle(args, symbols, &self.angle_mode.borrow()).await?;
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
    machine.add_function(CosFunction::new(angle_mode.clone()));
    machine.add_function(DtoiFunction::new());
    machine.add_function(ItodFunction::new());
    machine.add_function(MindFunction::new());
    machine.add_function(MiniFunction::new());
    machine.add_function(MaxdFunction::new());
    machine.add_function(MaxiFunction::new());
    machine.add_function(PiFunction::new());
    machine.add_command(RadCommand::new(angle_mode.clone()));
    machine.add_function(RndFunction::new(prng));
    machine.add_function(SinFunction::new(angle_mode.clone()));
    machine.add_function(TanFunction::new(angle_mode));
}

#[cfg(test)]
mod tests {
    use crate::testutils::*;

    #[test]
    fn test_atn() {
        check_expr_ok(123f64.atan(), "ATN(123)");
        check_expr_ok(45.5f64.atan(), "ATN(45.5)");

        check_expr_error("Syntax error in call to ATN: expected n%|n#", "ATN()");
        check_expr_error("Syntax error in call to ATN: expected n%|n#", "ATN(FALSE)");
        check_expr_error("Syntax error in call to ATN: expected n%|n#", "ATN(3, 4)");
    }

    #[test]
    fn test_cos() {
        check_expr_ok(123f64.cos(), "COS(123)");
        check_expr_ok(45.5f64.cos(), "COS(45.5)");

        check_expr_error("Syntax error in call to COS: expected angle%|angle#", "COS()");
        check_expr_error("Syntax error in call to COS: expected angle%|angle#", "COS(FALSE)");
        check_expr_error("Syntax error in call to COS: expected angle%|angle#", "COS(3, 4)");
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
        check_stmt_err("DEG takes no arguments", "DEG 1");
        check_stmt_err("RAD takes no arguments", "RAD 1");
    }

    #[test]
    fn test_dtoi() {
        check_expr_ok(0, "DTOI( 0.1)");
        check_expr_ok(0, "DTOI(-0.1)");
        check_expr_ok(0, "DTOI( 0.9)");
        check_expr_ok(0, "DTOI(-0.9)");

        check_expr_ok(100, "DTOI( 100.1)");
        check_expr_ok(-100, "DTOI(-100.1)");
        check_expr_ok(100, "DTOI( 100.9)");
        check_expr_ok(-100, "DTOI(-100.9)");

        check_expr_ok(std::i32::MAX, "DTOI(12345678901234567890.0)");
        check_expr_ok(std::i32::MIN, "DTOI(-12345678901234567890.0)");

        check_expr_error("Syntax error in call to DTOI: expected expr#", "DTOI()");
        check_expr_error("Syntax error in call to DTOI: expected expr#", "DTOI(3)");
        check_expr_error("Syntax error in call to DTOI: expected expr#", "DTOI(3.0, 4)");
    }

    #[test]
    fn test_itod() {
        check_expr_ok(0.0, "ITOD(0)");
        check_expr_ok(10.0, "ITOD(10)");
        check_expr_ok(-10.0, "ITOD(-10)");

        check_expr_ok(std::i32::MAX as f64, &format!("ITOD({})", std::i32::MAX));
        // TODO(jmmv): Due to limitations in the lexer/parser, we cannot represent the minimum
        // value of an i32 in the code as a literal.
        check_expr_ok(std::i32::MIN as f64, &format!("ITOD({} - 1)", std::i32::MIN + 1));

        check_expr_error("Syntax error in call to ITOD: expected expr%", "ITOD()");
        check_expr_error("Syntax error in call to ITOD: expected expr%", "ITOD(3.0)");
        check_expr_error("Syntax error in call to ITOD: expected expr%", "ITOD(3, 4)");
    }

    #[test]
    fn test_mind() {
        check_expr_ok(0.0, "MIND(0.0)");
        check_expr_ok(0.0, "MIND(0.0, 0.0)");

        check_expr_ok(1.0, "MIND(1.0)");
        check_expr_ok(3.5, "MIND(5.3, 3.5, 4.2)");
        check_expr_ok(-5.3, "MIND(-5.3, -3.5, -4.2)");

        check_expr_error("Syntax error in call to MIND: expected expr#[, .., expr#]", "MIND()");
        check_expr_error("Syntax error in call to MIND: expected expr#[, .., expr#]", "MIND(3)");
    }

    #[test]
    fn test_mini() {
        check_expr_ok(0, "MINI(0)");
        check_expr_ok(0, "MINI(0, 0)");

        check_expr_ok(1, "MINI(1)");
        check_expr_ok(3, "MINI(5, 3, 4)");
        check_expr_ok(-5, "MINI(-5, -3, -4)");

        check_expr_error("Syntax error in call to MINI: expected expr%[, .., expr%]", "MINI()");
        check_expr_error("Syntax error in call to MINI: expected expr%[, .., expr%]", "MINI(3.0)");
    }

    #[test]
    fn test_maxd() {
        check_expr_ok(0.0, "MAXD(0.0)");
        check_expr_ok(0.0, "MAXD(0.0, 0.0)");

        check_expr_ok(1.0, "MAXD(1.0)");
        check_expr_ok(5.3, "MAXD(5.3, 3.5, 4.2)");
        check_expr_ok(-3.5, "MAXD(-5.3, -3.5, -4.2)");

        check_expr_error("Syntax error in call to MAXD: expected expr#[, .., expr#]", "MAXD()");
        check_expr_error("Syntax error in call to MAXD: expected expr#[, .., expr#]", "MAXD(3)");
    }

    #[test]
    fn test_maxi() {
        check_expr_ok(0, "MAXI(0)");
        check_expr_ok(0, "MAXI(0, 0)");

        check_expr_ok(1, "MAXI(1)");
        check_expr_ok(5, "MAXI(5, 3, 4)");
        check_expr_ok(-3, "MAXI(-5, -3, -4)");

        check_expr_error("Syntax error in call to MAXI: expected expr%[, .., expr%]", "MAXI()");
        check_expr_error("Syntax error in call to MAXI: expected expr%[, .., expr%]", "MAXI(3.0)");
    }

    #[test]
    fn test_pi() {
        check_expr_ok(std::f64::consts::PI, "PI()");

        check_expr_error("Syntax error in call to PI: no arguments allowed", "PI(3)");
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
        t.run("result = RND(1)").expect_var("result", 0.2205558922655312).check();
        t.run("result = RND(0)").expect_var("result", 0.2205558922655312).check();
        t.run("result = RND(1)").expect_var("result", 0.8273883964464507).check();

        check_expr_error("Syntax error in call to RND: expected n%", "RND(3.0)");
        check_expr_error("Syntax error in call to RND: expected n%", "RND(1, 7)");
        check_expr_error("Syntax error in call to RND: n% cannot be negative", "RND(-1)");

        check_stmt_err("Random seed must be an integer", "RANDOMIZE 3.0");
        check_stmt_err("RANDOMIZE takes zero or one argument", "RANDOMIZE ,");
    }

    #[test]
    fn test_sin() {
        check_expr_ok(123f64.sin(), "SIN(123)");
        check_expr_ok(45.5f64.sin(), "SIN(45.5)");

        check_expr_error("Syntax error in call to SIN: expected angle%|angle#", "SIN()");
        check_expr_error("Syntax error in call to SIN: expected angle%|angle#", "SIN(FALSE)");
        check_expr_error("Syntax error in call to SIN: expected angle%|angle#", "SIN(3, 4)");
    }

    #[test]
    fn test_tan() {
        check_expr_ok(123f64.tan(), "TAN(123)");
        check_expr_ok(45.5f64.tan(), "TAN(45.5)");

        check_expr_error("Syntax error in call to TAN: expected angle%|angle#", "TAN()");
        check_expr_error("Syntax error in call to TAN: expected angle%|angle#", "TAN(FALSE)");
        check_expr_error("Syntax error in call to TAN: expected angle%|angle#", "TAN(3, 4)");
    }
}
