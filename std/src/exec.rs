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

//! Commands that directly manipulate the machine's state.

use async_trait::async_trait;
use endbasic_core::ast::{ArgSep, Expr, Value, VarType};
use endbasic_core::eval::{CallableMetadata, CallableMetadataBuilder};
use endbasic_core::exec::{new_usage_error, Command, Machine, Result};
use std::rc::Rc;

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
                .with_category("Interpreter manipulation")
                .with_description("Clears all variables to restore initial state.")
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Command for ClearCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Result<()> {
        if !args.is_empty() {
            return new_usage_error("CLEAR takes no arguments");
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
                .with_category("Interpreter manipulation")
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

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Result<()> {
        let arg = match args {
            [] => 0,
            [(Some(expr), ArgSep::End)] => {
                match expr.eval(machine.get_vars(), machine.get_functions())? {
                    Value::Integer(n) => {
                        if n < 0 {
                            return new_usage_error("Exit code must be a positive integer");
                        }
                        if n >= 128 {
                            return new_usage_error("Exit code cannot be larger than 127");
                        }
                        n as u8
                    }
                    _ => return new_usage_error("Exit code must be a positive integer"),
                }
            }
            _ => return new_usage_error("EXIT takes zero or one argument"),
        };
        machine.exit(arg);
        Ok(())
    }
}

/// Instantiates all REPL commands and adds them to the `machine`.
pub fn add_all(machine: &mut Machine) {
    machine.add_command(ClearCommand::new());
    machine.add_command(ExitCommand::new());
}

#[cfg(test)]
mod tests {
    use super::*;
    use endbasic_core::exec::StopReason;
    use futures_lite::future::block_on;

    /// Runs the `input` code on a new test machine and verifies that it fails with `expected_err`.
    fn do_error_test(input: &str, expected_err: &str) {
        let mut machine = Machine::default();
        machine.add_command(ExitCommand::new());
        let err =
            block_on(machine.exec(&mut input.as_bytes())).expect_err("Execution did not fail");
        assert_eq!(expected_err, format!("{}", err));
    }

    #[test]
    fn test_clear_ok() {
        let mut machine = Machine::default();
        machine.add_command(ClearCommand::new());
        assert_eq!(StopReason::Eof, block_on(machine.exec(&mut b"a = 1".as_ref())).unwrap());
        assert!(machine.get_var_as_int("a").is_ok());
        assert_eq!(StopReason::Eof, block_on(machine.exec(&mut b"CLEAR".as_ref())).unwrap());
        assert!(machine.get_var_as_int("a").is_err());
    }

    #[test]
    fn test_clear_errors() {
        let mut machine = Machine::default();
        machine.add_command(ClearCommand::new());
        assert_eq!(
            "CLEAR takes no arguments",
            format!("{}", block_on(machine.exec(&mut b"CLEAR 123".as_ref())).unwrap_err())
        );
    }

    #[test]
    fn test_exit_no_code() {
        let mut machine = Machine::default();
        machine.add_command(ExitCommand::new());
        assert_eq!(
            StopReason::Exited(0),
            block_on(machine.exec(&mut b"a = 3: EXIT: a = 4".as_ref())).unwrap()
        );
        assert_eq!(3, machine.get_var_as_int("a").unwrap());
    }

    fn do_exit_with_code_test(code: u8) {
        let mut machine = Machine::default();
        machine.add_command(ExitCommand::new());
        assert_eq!(
            StopReason::Exited(code),
            block_on(machine.exec(&mut format!("a = 3: EXIT {}: a = 4", code).as_bytes())).unwrap()
        );
        assert_eq!(3, machine.get_var_as_int("a").unwrap());
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
        do_error_test("EXIT 1, 2", "EXIT takes zero or one argument");
        do_error_test("EXIT -3", "Exit code must be a positive integer");
        do_error_test("EXIT 128", "Exit code cannot be larger than 127");
    }
}
