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
use endbasic_core::exec::{new_usage_error, Command, Machine, Result};
use endbasic_core::syms::{CallableMetadata, CallableMetadataBuilder};
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
            [(Some(expr), ArgSep::End)] => match expr.eval(machine.get_symbols())? {
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
            },
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
    use crate::testutils::*;
    use endbasic_core::exec::StopReason;

    #[test]
    fn test_clear_ok() {
        Tester::default().run("a = 1: CLEAR").check();
        Tester::default().run("DIM a(2): CLEAR: DIM a(5) AS STRING: CLEAR").check();
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
}
