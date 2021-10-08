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
use endbasic_core::exec::Machine;
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

/// Adds all symbols provided by this module to the given `machine`.
pub fn add_all(machine: &mut Machine) {
    let prng = Rc::from(RefCell::from(Prng::new_from_entryopy()));
    machine.add_command(RandomizeCommand::new(prng.clone()));
    machine.add_function(DtoiFunction::new());
    machine.add_function(ItodFunction::new());
    machine.add_function(RndFunction::new(prng));
}

#[cfg(test)]
mod tests {
    use crate::testutils::*;

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
}
