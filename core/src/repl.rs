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

//! Interactive interpreter for the EndBASIC language.

use crate::ast::{ArgSep, Expr, Value, VarType};
use crate::console::{self, Console};
use crate::eval::{CallableMetadata, CallableMetadataBuilder};
use crate::exec::{self, Command, Machine, MachineBuilder, StopReason};
use crate::store::Store;
use async_trait::async_trait;
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

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

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        machine: &mut Machine,
    ) -> exec::Result<()> {
        let arg = match args {
            [] => 0,
            [(Some(expr), ArgSep::End)] => {
                match expr.eval(machine.get_vars(), machine.get_functions())? {
                    Value::Integer(n) => {
                        if n < 0 {
                            return exec::new_usage_error("Exit code must be a positive integer");
                        }
                        if n >= 128 {
                            return exec::new_usage_error("Exit code cannot be larger than 127");
                        }
                        n as u8
                    }
                    _ => return exec::new_usage_error("Exit code must be a positive integer"),
                }
            }
            _ => return exec::new_usage_error("EXIT takes zero or one argument"),
        };
        machine.exit(arg);
        Ok(())
    }
}

/// Instantiates all REPL commands.
pub fn add_all(builder: MachineBuilder) -> MachineBuilder {
    builder.add_command(ExitCommand::new())
}

/// Enters the interactive interpreter.
///
/// `dir` specifies the directory that the interpreter will use for any commands that manipulate
/// files.
pub async fn run_repl_loop(
    console: Rc<RefCell<dyn Console>>,
    store: Rc<RefCell<dyn Store>>,
) -> io::Result<i32> {
    let mut machine = crate::interactive_machine_builder(console.clone(), store).build();

    {
        let mut console = console.borrow_mut();
        console.print("")?;
        console.print(&format!("    Welcome to EndBASIC {}.", env!("CARGO_PKG_VERSION")))?;
        console.print("")?;
        console.print("    Type HELP for interactive usage information.")?;
        console.print("    Type LOAD \"DEMO:TOUR.BAS\": RUN for a guided tour.")?;
        console.print("")?;
    }

    let mut stop_reason = StopReason::Eof;
    while stop_reason == StopReason::Eof {
        let line = {
            let mut console = console.borrow_mut();
            if console.is_interactive() {
                console.print("Ready")?;
            }
            console::read_line(&mut *console, "", "").await
        };

        match line {
            Ok(line) => match machine.exec(&mut line.as_bytes()).await {
                Ok(reason) => stop_reason = reason,
                Err(e) => {
                    let mut console = console.borrow_mut();
                    console.print(format!("ERROR: {}", e).as_str())?;
                }
            },
            Err(e) => {
                if e.kind() == io::ErrorKind::Interrupted {
                    let mut console = console.borrow_mut();
                    console.print("Interrupted by CTRL-C")?;
                    // TODO(jmmv): This should cause the interpreter to exit with a signal.
                    stop_reason = StopReason::Exited(1);
                } else if e.kind() == io::ErrorKind::UnexpectedEof {
                    let mut console = console.borrow_mut();
                    console.print("End of input by CTRL-D")?;
                    stop_reason = StopReason::Exited(0);
                    break;
                } else {
                    stop_reason = StopReason::Exited(1);
                }
            }
        }
    }
    Ok(stop_reason.as_exit_code())
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures_lite::future::block_on;

    /// Runs the code `input` and expects it to fail with `expected_err`.
    fn do_error_test(input: &str, expected_err: &str) {
        let mut machine = MachineBuilder::default().add_command(ExitCommand::new()).build();
        let err = block_on(machine.exec(&mut input.as_bytes())).unwrap_err();
        assert_eq!(expected_err, format!("{}", err));
    }

    #[test]
    fn test_exit_no_code() {
        let mut machine = MachineBuilder::default().add_command(ExitCommand::new()).build();
        assert_eq!(
            StopReason::Exited(0),
            block_on(machine.exec(&mut b"a = 3: EXIT: a = 4".as_ref())).unwrap()
        );
        assert_eq!(3, machine.get_var_as_int("a").unwrap());
    }

    fn do_exit_with_code_test(code: u8) {
        let mut machine = MachineBuilder::default().add_command(ExitCommand::new()).build();
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
