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
use std::borrow::Cow;
use std::rc::Rc;
use std::thread;
use std::time::Duration;

use crate::MachineBuilder;

/// Category description for all symbols provided by this module.
pub(crate) const CATEGORY: &str = "Date and time";

/// Interface to date and time functionality provided by the host.
#[async_trait(?Send)]
pub trait DateTime {
    /// Suspends execution for the given duration.
    async fn sleep(&self, d: Duration) -> Result<(), String>;
}

/// Default host-backed implementation of the `DateTime` trait.
pub struct SystemDateTime;

#[async_trait(?Send)]
impl DateTime for SystemDateTime {
    async fn sleep(&self, d: Duration) -> Result<(), String> {
        thread::sleep(d);
        Ok(())
    }
}

/// The `SLEEP` command.
pub struct SleepCommand {
    metadata: Rc<CallableMetadata>,
    datetime: Rc<dyn DateTime>,
}

impl SleepCommand {
    /// Creates a new instance of the command.
    pub fn new(datetime: Rc<dyn DateTime>) -> Rc<Self> {
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
            datetime,
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

        self.datetime
            .sleep(Duration::from_secs_f64(n))
            .await
            .map_err(|e| CallError::Syntax(scope.get_pos(0), e))
    }
}

/// Adds all symbols provided by this module to the given `machine`.
///
/// `datetime` provides access to date and time functionality.
pub fn add_all(machine: &mut MachineBuilder, datetime: Rc<dyn DateTime>) {
    machine.add_callable(SleepCommand::new(datetime));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::MachineBuilder;
    use crate::testutils::*;
    use async_trait::async_trait;
    use futures_lite::future::block_on;
    use std::rc::Rc;
    use std::time::Instant;

    struct MockDateTime {
        sleep_fn: Box<dyn Fn(Duration) -> Result<(), String>>,
    }

    #[async_trait(?Send)]
    impl DateTime for MockDateTime {
        async fn sleep(&self, d: Duration) -> Result<(), String> {
            (self.sleep_fn)(d)
        }
    }

    #[test]
    fn test_sleep_ok_int() {
        let datetime = Rc::from(MockDateTime {
            sleep_fn: Box::from(|d: Duration| Err(format!("Got {} ms", d.as_millis()))),
        });

        let mut machine = MachineBuilder::default().with_datetime(datetime).build();
        machine.compile(&mut "SLEEP 123".as_bytes()).unwrap();
        assert_eq!("1:7: Got 123000 ms", format!("{}", block_on(machine.exec()).unwrap_err()));
    }

    #[test]
    fn test_sleep_ok_float() {
        let datetime = Rc::from(MockDateTime {
            sleep_fn: Box::from(|d: Duration| {
                let ms = d.as_millis();
                if ms > 123095 && ms < 123105 {
                    Err("Good".to_owned())
                } else {
                    Err(format!("Bad {}", ms))
                }
            }),
        });

        let mut machine = MachineBuilder::default().with_datetime(datetime).build();
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
