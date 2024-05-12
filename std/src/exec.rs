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
use endbasic_core::ast::{Value, VarType};
use endbasic_core::exec::Machine;
use endbasic_core::syms::{
    CallError, CallResult, Callable, CallableMetadata, CallableMetadataBuilder, Symbol,
};
use endbasic_core::LineCol;
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
SAVE your program!).
This command is for interactive use only.",
                )
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for ClearCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, machine: &mut Machine) -> CallResult {
        if !args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        machine.clear();
        Ok(Value::Void)
    }
}

/// The `ERRMSG` function.
pub struct ErrmsgFunction {
    metadata: CallableMetadata,
}

impl ErrmsgFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("ERRMSG", VarType::Text)
                .with_syntax("")
                .with_category(CATEGORY)
                .with_description(
                    "Returns the last captured error message.
When used in combination of ON ERROR to set an error handler, this function returns the string \
representation of the last captured error.  If this is called before any error is captured, \
returns the empty string.",
                )
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for ErrmsgFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, machine: &mut Machine) -> CallResult {
        if !args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        // TODO(jmmv): Instead of abusing a private variable to propagate the error message from
        // the machine to here, we should query the last error message from the machine itself via
        // a method, but this is difficult (from a refactoring perspective) because a function's
        // exec() does not have access to the Machine.
        match machine.get_symbols().get_auto("0errmsg") {
            Some(Symbol::Variable(v @ Value::Text(_))) => Ok(v.clone()),
            Some(_) => panic!("Internal symbol must be of a specific type"),
            None => Ok(Value::Text("".to_owned())),
        }
    }
}

/// Type of the sleep function used by the `SLEEP` command to actually suspend execution.
pub type SleepFn = Box<dyn Fn(Duration, LineCol) -> BoxedLocal<CallResult>>;

/// An implementation of a `SleepFn` that stops the current thread.
fn system_sleep(d: Duration, _pos: LineCol) -> BoxedLocal<CallResult> {
    async move {
        thread::sleep(d);
        Ok(Value::Void)
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
                .with_syntax("seconds<%|#>")
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
impl Callable for SleepCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, machine: &mut Machine) -> CallResult {
        let mut iter = machine.load_all(args)?.into_iter();

        let (duration, pos) = match iter.next() {
            Some((value, pos)) => {
                let n =
                    value.as_f64().map_err(|e| CallError::ArgumentError(pos, format!("{}", e)))?;
                if n < 0.0 {
                    return Err(CallError::ArgumentError(
                        pos,
                        "Sleep time must be positive".to_owned(),
                    ));
                }
                (Duration::from_secs_f64(n), pos)
            }
            _ => return Err(CallError::SyntaxError),
        };

        if iter.next().is_some() {
            return Err(CallError::SyntaxError);
        }

        (self.sleep_fn)(duration, pos).await
    }
}

/// Instantiates all REPL commands for the scripting machine and adds them to the `machine`.
///
/// `sleep_fn` is an async function that implements a pause given a `Duration`.  If not provided,
/// uses the `std::thread::sleep` function.
pub fn add_scripting(machine: &mut Machine, sleep_fn: Option<SleepFn>) {
    machine.add_callable(ErrmsgFunction::new());
    machine.add_callable(SleepCommand::new(sleep_fn.unwrap_or_else(|| Box::from(system_sleep))));
}

/// Instantiates all REPL commands for the interactive machine and adds them to the `machine`.
pub fn add_interactive(machine: &mut Machine) {
    machine.add_callable(ClearCommand::new());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;
    use std::time::Instant;

    #[test]
    fn test_clear_ok() {
        Tester::default().run("a = 1: CLEAR").expect_clear().check();
        Tester::default()
            .run_n(&["DIM a(2): CLEAR", "DIM a(5) AS STRING: CLEAR"])
            .expect_clear()
            .expect_clear()
            .check();
    }

    #[test]
    fn test_clear_errors() {
        check_stmt_err("1:1: In call to CLEAR: expected no arguments", "CLEAR 123");
    }

    #[test]
    fn test_errmsg_before_error() {
        check_expr_ok("", r#"ERRMSG"#);
    }

    #[test]
    fn test_errmsg_after_error() {
        Tester::default()
            .run("ON ERROR RESUME NEXT: INPUT 3: PRINT \"Captured: \"; ERRMSG")
            .expect_var(
                "0ERRMSG",
                "1:23: In call to INPUT: 1:29: INPUT requires a variable reference",
            )
            .expect_prints([
                "Captured: 1:23: In call to INPUT: 1:29: INPUT requires a variable reference",
            ])
            .check();
    }

    #[test]
    fn test_errmsg_errors() {
        check_expr_compilation_error(
            "1:10: In call to ERRMSG: expected no arguments nor parenthesis",
            r#"ERRMSG()"#,
        );
        check_expr_compilation_error(
            "1:10: In call to ERRMSG: expected no arguments nor parenthesis",
            r#"ERRMSG(3)"#,
        );
    }

    #[test]
    fn test_sleep_ok_int() {
        let sleep_fake = |d: Duration, pos: LineCol| -> BoxedLocal<CallResult> {
            async move { Err(CallError::InternalError(pos, format!("Got {} ms", d.as_millis()))) }
                .boxed_local()
        };

        let mut t = Tester::empty().add_callable(SleepCommand::new(Box::from(sleep_fake)));
        t.run("SLEEP 123").expect_err("1:1: In call to SLEEP: 1:7: Got 123000 ms").check();
    }

    #[test]
    fn test_sleep_ok_float() {
        let sleep_fake = |d: Duration, pos: LineCol| -> BoxedLocal<CallResult> {
            async move {
                let ms = d.as_millis();
                if ms > 123095 && ms < 123105 {
                    Err(CallError::InternalError(pos, "Good".to_owned()))
                } else {
                    Err(CallError::InternalError(pos, format!("Bad {}", ms)))
                }
            }
            .boxed_local()
        };

        let mut t = Tester::empty().add_callable(SleepCommand::new(Box::from(sleep_fake)));
        t.run("SLEEP 123.1").expect_err("1:1: In call to SLEEP: 1:7: Good").check();
    }

    #[test]
    fn test_sleep_real() {
        let before = Instant::now();
        Tester::default().run("SLEEP 0.010").check();
        assert!(before.elapsed() >= Duration::from_millis(10));
    }

    #[test]
    fn test_sleep_errors() {
        check_stmt_err("1:1: In call to SLEEP: expected seconds<%|#>", "SLEEP");
        check_stmt_err("1:1: In call to SLEEP: expected seconds<%|#>", "SLEEP 2, 3");
        check_stmt_err("1:1: In call to SLEEP: expected seconds<%|#>", "SLEEP 2; 3");
        check_stmt_err("1:1: In call to SLEEP: 1:7: \"foo\" is not a number", "SLEEP \"foo\"");
        check_stmt_err("1:1: In call to SLEEP: 1:7: Sleep time must be positive", "SLEEP -1");
        check_stmt_err("1:1: In call to SLEEP: 1:7: Sleep time must be positive", "SLEEP -0.001");
    }
}
