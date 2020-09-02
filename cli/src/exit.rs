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

//! Implementation of the command to exit the interpreter.

use async_trait::async_trait;
use endbasic_core::ast::{ArgSep, Expr, Value};
use endbasic_core::exec::{self, BuiltinCommand, Machine};
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

#[cfg(test)]
mod tests {
    use super::*;
    use endbasic_core::exec::MachineBuilder;

    /// Runs the code `input` and expects it to fail with `expected_err`.
    fn do_error_test(input: &str, expected_err: &str) {
        let exit_code = Rc::from(RefCell::from(None));
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(ExitCommand::new(exit_code.clone())))
            .build();
        let err = machine.exec(&mut input.as_bytes()).unwrap_err();
        assert_eq!(expected_err, format!("{}", err));
        assert!(exit_code.borrow().is_none());
    }

    #[test]
    fn test_exit_no_code() {
        let exit_code = Rc::from(RefCell::from(None));
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(ExitCommand::new(exit_code.clone())))
            .build();
        machine.exec(&mut b"a = 3: EXIT: a = 4".as_ref()).unwrap_err();
        assert_eq!(0, exit_code.borrow().unwrap());
        assert_eq!(3, machine.get_var_as_int("a").unwrap());
    }

    fn do_exit_with_code_test(code: i32) {
        let exit_code = Rc::from(RefCell::from(None));
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(ExitCommand::new(exit_code.clone())))
            .build();
        machine.exec(&mut format!("a = 3: EXIT {}: a = 4", code).as_bytes()).unwrap_err();
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
