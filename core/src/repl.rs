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

use crate::ast::{ArgSep, Expr, Value};
use crate::console::{self, Console};
use crate::exec::{self, BuiltinCommand, ClearCommand, Machine, MachineBuilder};
use crate::help::HelpCommand;
use crate::program::{self, Store};
use async_trait::async_trait;
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

/// The `EXIT` command.
pub struct ExitCommand {
    code: Rc<RefCell<Option<i32>>>,
}

impl ExitCommand {
    /// Creates a new command that updates `code` with the exit code once called.
    pub fn new(code: Rc<RefCell<Option<i32>>>) -> Self {
        Self { code }
    }
}

#[async_trait(?Send)]
impl BuiltinCommand for ExitCommand {
    fn name(&self) -> &'static str {
        "EXIT"
    }

    fn category(&self) -> &'static str {
        "Interpreter manipulation"
    }

    fn syntax(&self) -> &'static str {
        "[code%]"
    }

    fn description(&self) -> &'static str {
        "Exits the interpreter.
The optional code indicates the return value to return to the system."
    }

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        machine: &mut Machine,
    ) -> exec::Result<()> {
        let arg = match args {
            [] => 0,
            [(Some(expr), ArgSep::End)] => match expr.eval(machine.get_vars())? {
                Value::Integer(n) => {
                    if n < 0 {
                        return exec::new_usage_error("Exit code must be a positive integer");
                    }
                    if n >= 128 {
                        return exec::new_usage_error("Exit code cannot be larger than 127");
                    }
                    n
                }
                _ => return exec::new_usage_error("Exit code must be a positive integer"),
            },
            _ => return exec::new_usage_error("EXIT takes zero or one argument"),
        };
        let mut code = self.code.borrow_mut();
        debug_assert!(code.is_none(), "EXIT called multiple times without exiting");
        *code = Some(arg);

        // TODO(jmmv): This is ugly, but we need a way to abort execution when we feed a line with
        // multiple statements to the interpreter.  Maybe this will be nicer with custom error
        // codes.
        Err(io::Error::new(io::ErrorKind::UnexpectedEof, "").into())
    }
}

/// Enters the interactive interpreter.
///
/// `dir` specifies the directory that the interpreter will use for any commands that manipulate
/// files.
pub async fn run_repl_loop(
    console: Rc<RefCell<dyn Console>>,
    store: Rc<RefCell<dyn Store>>,
) -> io::Result<i32> {
    let exit_code = Rc::from(RefCell::from(None));
    let mut machine = MachineBuilder::default()
        .add_builtin(Rc::from(ClearCommand::default()))
        .add_builtin(Rc::from(ExitCommand::new(exit_code.clone())))
        .add_builtin(Rc::from(HelpCommand::new(console.clone())))
        .add_builtins(console::all_commands(console.clone()))
        .add_builtins(program::all_commands(console.clone(), store))
        .build();

    {
        let mut console = console.borrow_mut();
        console.print("")?;
        console.print(&format!("    Welcome to EndBASIC {}.", env!("CARGO_PKG_VERSION")))?;
        console.print("    Type HELP for interactive usage information.")?;
        console.print("")?;
    }

    while exit_code.borrow().is_none() {
        let line = {
            let mut console = console.borrow_mut();
            if console.is_interactive() {
                console.print("Ready")?;
            }
            console::read_line(&mut *console, "", "").await
        };

        match line {
            Ok(line) => match machine.exec(&mut line.as_bytes()).await {
                Ok(()) => (),
                Err(e) => {
                    if exit_code.borrow().is_some() {
                        if let exec::Error::IoError(e) = e {
                            debug_assert!(e.kind() == io::ErrorKind::UnexpectedEof);
                        }
                    } else {
                        let mut console = console.borrow_mut();
                        console.print(format!("ERROR: {}", e).as_str())?;
                    }
                }
            },
            Err(e) => {
                if e.kind() == io::ErrorKind::Interrupted {
                    let mut console = console.borrow_mut();
                    console.print("Interrupted by CTRL-C")?;
                    // TODO(jmmv): This should cause the interpreter to exit with a signal.
                    *exit_code.borrow_mut() = Some(1);
                } else if e.kind() == io::ErrorKind::UnexpectedEof {
                    let mut console = console.borrow_mut();
                    console.print("End of input by CTRL-D")?;
                    *exit_code.borrow_mut() = Some(0);
                } else {
                    *exit_code.borrow_mut() = Some(1);
                }
            }
        }
    }
    let exit_code = exit_code.borrow();
    Ok(exit_code.expect("Some code path above did not set an exit code"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures_lite::future::block_on;

    /// Runs the code `input` and expects it to fail with `expected_err`.
    fn do_error_test(input: &str, expected_err: &str) {
        let exit_code = Rc::from(RefCell::from(None));
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(ExitCommand::new(exit_code.clone())))
            .build();
        let err = block_on(machine.exec(&mut input.as_bytes())).unwrap_err();
        assert_eq!(expected_err, format!("{}", err));
        assert!(exit_code.borrow().is_none());
    }

    #[test]
    fn test_exit_no_code() {
        let exit_code = Rc::from(RefCell::from(None));
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(ExitCommand::new(exit_code.clone())))
            .build();
        block_on(machine.exec(&mut b"a = 3: EXIT: a = 4".as_ref())).unwrap_err();
        assert_eq!(0, exit_code.borrow().unwrap());
        assert_eq!(3, machine.get_var_as_int("a").unwrap());
    }

    fn do_exit_with_code_test(code: i32) {
        let exit_code = Rc::from(RefCell::from(None));
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(ExitCommand::new(exit_code.clone())))
            .build();
        block_on(machine.exec(&mut format!("a = 3: EXIT {}: a = 4", code).as_bytes())).unwrap_err();
        assert_eq!(code, exit_code.borrow().unwrap());
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
