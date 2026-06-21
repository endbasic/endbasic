// EndBASIC
// Copyright 2026 Julio Merino
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

//! Time manipulation primitives.

use async_trait::async_trait;
use endbasic_core::{
    ArgSepSyntax, CallError, CallResult, Callable, CallableMetadata, CallableMetadataBuilder,
    ExprType, RequiredValueSyntax, Scope, SingularArgSyntax,
};
use futures_lite::future::{BoxedLocal, FutureExt};
use std::borrow::Cow;
use std::rc::Rc;
use std::thread;
use std::time::Duration;

use crate::MachineBuilder;

/// Category description for all symbols provided by this module.
pub(crate) const CATEGORY: &str = "Date and time";

/// Type of the sleep function used by the `SLEEP` command to actually suspend execution.
pub type SleepFn = Box<dyn Fn(Duration) -> BoxedLocal<Result<(), String>>>;

/// An implementation of a `SleepFn` that stops the current thread.
fn system_sleep(d: Duration) -> BoxedLocal<Result<(), String>> {
    async move {
        thread::sleep(d);
        Ok(())
    }
    .boxed_local()
}

/// The `SLEEP` command.
pub struct SleepCommand {
    metadata: Rc<CallableMetadata>,
    sleep_fn: SleepFn,
}

impl SleepCommand {
    /// Creates a new instance of the command.
    pub fn new(sleep_fn: SleepFn) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("SLEEP")
                .with_async(true)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax {
                            name: Cow::Borrowed("seconds"),
                            vtype: ExprType::Double,
                        },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
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
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn async_exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(1, scope.nargs());
        let n = scope.get_double(0);

        if n < 0.0 {
            return Err(CallError::Syntax(
                scope.get_pos(0),
                "Sleep time must be positive".to_owned(),
            ));
        }

        (self.sleep_fn)(Duration::from_secs_f64(n))
            .await
            .map_err(|e| CallError::Syntax(scope.get_pos(0), e))
    }
}

/// Adds all symbols provided by this module to the given `machine`.
///
/// `sleep_fn` is an async function that implements a pause given a `Duration`.  If not provided,
/// uses the `std::thread::sleep` function.
pub fn add_all(machine: &mut MachineBuilder, sleep_fn: Option<SleepFn>) {
    machine.add_callable(SleepCommand::new(sleep_fn.unwrap_or_else(|| Box::from(system_sleep))));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::MachineBuilder;
    use crate::testutils::*;
    use futures_lite::future::block_on;
    use std::time::Instant;

    #[test]
    fn test_sleep_ok_int() {
        let sleep_fake = |d: Duration| -> BoxedLocal<Result<(), String>> {
            async move { Err(format!("Got {} ms", d.as_millis())) }.boxed_local()
        };

        let mut machine = MachineBuilder::default().with_sleep_fn(Box::from(sleep_fake)).build();
        machine.compile(&mut "SLEEP 123".as_bytes()).unwrap();
        assert_eq!("1:7: Got 123000 ms", format!("{}", block_on(machine.exec()).unwrap_err()));
    }

    #[test]
    fn test_sleep_ok_float() {
        let sleep_fake = |d: Duration| -> BoxedLocal<Result<(), String>> {
            async move {
                let ms = d.as_millis();
                if ms > 123095 && ms < 123105 {
                    Err("Good".to_owned())
                } else {
                    Err(format!("Bad {}", ms))
                }
            }
            .boxed_local()
        };

        let mut machine = MachineBuilder::default().with_sleep_fn(Box::from(sleep_fake)).build();
        machine.compile(&mut "SLEEP 123.1".as_bytes()).unwrap();
        assert_eq!("1:7: Good", format!("{}", block_on(machine.exec()).unwrap_err()));
    }

    #[test]
    fn test_sleep_real() {
        let before = Instant::now();
        Tester::default().run("SLEEP 0.010").check();
        assert!(before.elapsed() >= Duration::from_millis(10));
    }

    #[test]
    fn test_sleep_errors() {
        check_stmt_compilation_err("1:1: SLEEP expected seconds#", "SLEEP");
        check_stmt_compilation_err("1:1: SLEEP expected seconds#", "SLEEP 2, 3");
        check_stmt_compilation_err("1:1: SLEEP expected seconds#", "SLEEP 2; 3");
        check_stmt_compilation_err("1:7: STRING is not a number", "SLEEP \"foo\"");
        check_stmt_err("1:7: Sleep time must be positive", "SLEEP -1");
        check_stmt_err("1:7: Sleep time must be positive", "SLEEP -0.001");
    }
}
