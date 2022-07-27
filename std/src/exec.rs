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

//! Commands that manipulate the machine's state or the program's execution.

use async_trait::async_trait;
use endbasic_core::ast::{ArgSep, Expr, Value, VarType};
use endbasic_core::exec::Machine;
use endbasic_core::syms::{
    CallError, CallableMetadata, CallableMetadataBuilder, Command, CommandResult,
};
use futures_lite::future::{BoxedLocal, FutureExt};
use std::rc::Rc;
use std::thread;
use std::time::Duration;

/// Category description for all symbols provided by this module.
pub(crate) const CATEGORY: &str = "Interpreter";

/// The `CLEAR` command.
pub struct ClearCommand {
    metadata: CallableMetadata,
}

impl ClearCommand {
    /// Creates a new `CLEAR` command that resets the state of the machine.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("CLEAR", VarType::Void)
                .with_syntax("")
                .with_category(CATEGORY)
                .with_description(
                    "Restores initial machine state but keeps the stored program.
This command resets the machine to a semi-pristine state by clearing all user-defined variables \
and restoring the state of shared resources.  These resources include: the console, whose color \
and video syncing bit are reset; and the GPIO pins, which are set to their default state.
The stored program is kept in memory.  To clear that too, use NEW (but don't forget to first \
SAVE your program!).",
                )
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Command for ClearCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        if !args.is_empty() {
            return Err(CallError::ArgumentError("CLEAR takes no arguments".to_owned()));
        }
        machine.clear();
        Ok(())
    }
}

/// The `EXIT` command.
pub struct ExitCommand {
    metadata: CallableMetadata,
}

impl ExitCommand {
    /// Creates a new command that terminates execution once called.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("EXIT", VarType::Void)
                .with_syntax("[code%]")
                .with_category(CATEGORY)
                .with_description(
                    "Exits the interpreter.
The optional code indicates the return value to return to the system.",
                )
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Command for ExitCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        let arg = match args {
            [] => 0,
            [(Some(expr), ArgSep::End)] => match expr.eval(machine.get_mut_symbols()).await? {
                Value::Integer(n) => {
                    if n < 0 {
                        return Err(CallError::ArgumentError(
                            "Exit code must be a positive integer".to_owned(),
                        ));
                    }
                    if n >= 128 {
                        return Err(CallError::ArgumentError(
                            "Exit code cannot be larger than 127".to_owned(),
                        ));
                    }
                    n as u8
                }
                _ => {
                    return Err(CallError::ArgumentError(
                        "Exit code must be a positive integer".to_owned(),
                    ))
                }
            },
            _ => {
                return Err(CallError::ArgumentError("EXIT takes zero or one argument".to_owned()))
            }
        };
        machine.exit(arg);
        Ok(())
    }
}

/// Type of the sleep function used by the `SLEEP` command to actually suspend execution.
pub type SleepFn = Box<dyn Fn(Duration) -> BoxedLocal<CommandResult>>;

/// An implementation of a `SleepFn` that stops the current thread.
fn system_sleep(d: Duration) -> BoxedLocal<CommandResult> {
    async move {
        thread::sleep(d);
        Ok(())
    }
    .boxed_local()
}

/// The `SLEEP` command.
pub struct SleepCommand {
    metadata: CallableMetadata,
    sleep_fn: SleepFn,
}

impl SleepCommand {
    /// Creates a new instance of the command.
    pub fn new(sleep_fn: SleepFn) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("SLEEP", VarType::Void)
                .with_syntax("seconds%|seconds#")
                .with_category(CATEGORY)
                .with_description(
                    "Suspends program execution.
Pauses program execution for the given number of seconds, which can be specified either as an \
integer or as a floating point number for finer precision.",
                )
                .build(),
            sleep_fn,
        })
    }
}

#[async_trait(?Send)]
impl Command for SleepCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        let duration = match args {
            [(Some(expr), ArgSep::End)] => match expr.eval(machine.get_mut_symbols()).await? {
                Value::Integer(n) => {
                    if n < 0 {
                        return Err(CallError::ArgumentError(
                            "Sleep time must be positive".to_owned(),
                        ));
                    }
                    Duration::from_secs(n as u64)
                }
                Value::Double(n) => {
                    if n < 0.0 {
                        return Err(CallError::ArgumentError(
                            "Sleep time must be positive".to_owned(),
                        ));
                    }
                    Duration::from_secs_f64(n)
                }
                _ => {
                    return Err(CallError::ArgumentError(
                        "Sleep time must be an integer or a double".to_owned(),
                    ))
                }
            },
            _ => return Err(CallError::ArgumentError("SLEEP takes one argument".to_owned())),
        };
        (self.sleep_fn)(duration).await
    }
}

/// Instantiates all REPL commands and adds them to the `machine`.
///
/// `sleep_fn` is an async function that implements a pause given a `Duration`.  If not provided,
/// uses the `std::thread::sleep` function.
pub fn add_all(machine: &mut Machine, sleep_fn: Option<SleepFn>) {
    machine.add_command(ClearCommand::new());
    machine.add_command(ExitCommand::new());
    machine.add_command(SleepCommand::new(sleep_fn.unwrap_or_else(|| Box::from(system_sleep))));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;
    use endbasic_core::exec::StopReason;
    use std::time::Instant;

    #[test]
    fn test_clear_ok() {
        Tester::default().run("a = 1: CLEAR").expect_clear().check();
        Tester::default()
            .run("DIM a(2): CLEAR: DIM a(5) AS STRING: CLEAR")
            .expect_clear()
            .expect_clear()
            .check();
    }

    #[test]
    fn test_clear_errors() {
        check_stmt_err("CLEAR takes no arguments", "CLEAR 123");
    }

    #[test]
    fn test_exit_no_code() {
        Tester::default()
            .run("a = 3: EXIT: a = 4")
            .expect_ok(StopReason::Exited(0))
            .expect_var("a", 3)
            .check();
    }

    fn do_exit_with_code_test(code: u8) {
        Tester::default()
            .run(format!("a = 3: EXIT {}: a = 4", code))
            .expect_ok(StopReason::Exited(code))
            .expect_var("a", 3)
            .check();
    }

    #[test]
    fn text_exit_with_code() {
        do_exit_with_code_test(0);
        do_exit_with_code_test(1);
        do_exit_with_code_test(42);
        do_exit_with_code_test(127);
    }

    #[test]
    fn test_exit_errors() {
        check_stmt_err("EXIT takes zero or one argument", "EXIT 1, 2");
        check_stmt_err("Exit code must be a positive integer", "EXIT -3");
        check_stmt_err("Exit code cannot be larger than 127", "EXIT 128");
    }

    #[test]
    fn test_sleep_ok_int() {
        let sleep_fake = |d: Duration| -> BoxedLocal<CommandResult> {
            async move { Err(CallError::InternalError(format!("Got {} ms", d.as_millis()))) }
                .boxed_local()
        };

        let mut t = Tester::empty().add_command(SleepCommand::new(Box::from(sleep_fake)));
        t.run("SLEEP 123").expect_err("Got 123000 ms").check();
    }

    #[test]
    fn test_sleep_ok_float() {
        let sleep_fake = |d: Duration| -> BoxedLocal<CommandResult> {
            async move {
                let ms = d.as_millis();
                if ms > 123095 && ms < 123105 {
                    Err(CallError::InternalError("Good".to_owned()))
                } else {
                    Err(CallError::InternalError(format!("Bad {}", ms)))
                }
            }
            .boxed_local()
        };

        let mut t = Tester::empty().add_command(SleepCommand::new(Box::from(sleep_fake)));
        t.run("SLEEP 123.1").expect_err("Good").check();
    }

    #[test]
    fn test_sleep_real() {
        let before = Instant::now();
        Tester::default().run("SLEEP 0.010").check();
        assert!(before.elapsed() >= Duration::from_millis(10));
    }

    #[test]
    fn test_sleep_errors() {
        check_stmt_err("SLEEP takes one argument", "SLEEP");
        check_stmt_err("SLEEP takes one argument", "SLEEP 2, 3");
        check_stmt_err("SLEEP takes one argument", "SLEEP 2; 3");
        check_stmt_err("Sleep time must be an integer or a double", "SLEEP \"foo\"");
        check_stmt_err("Sleep time must be positive", "SLEEP -1");
        check_stmt_err("Sleep time must be positive", "SLEEP -0.001");
    }
}
