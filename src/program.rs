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

//! Stored program manipulation and interactive editor.

use crate::ast::{ArgSep, Expr, Value};
use crate::console::Console;
use crate::exec::{BuiltinCommand, Machine};
use failure::Fallible;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::io;
use std::rc::Rc;

/// Representation of a stored program.
///
/// Stored programs are kept as a mapping of line numbers to their contents.  The reason is that the
/// line numbers are not consecutive during editing.
type ProgramImpl = BTreeMap<usize, String>;

/// Mutable reference to a `ProgramImpl` to serve as the state of all commands.
type Program = Rc<RefCell<ProgramImpl>>;

/// Interactively edits line `n` of the stored `program` via the `console`.
///
/// Returns true if the entered line was empty and false otherwise.
fn edit_one(program: &mut ProgramImpl, n: usize, console: &mut dyn Console) -> io::Result<bool> {
    let prompt = format!("{} ", n);

    let previous = match program.get(&n) {
        Some(line) => line,
        None => "",
    };

    let line = console.input(&prompt, &previous)?;
    debug_assert!(!line.ends_with('\n'));
    if line.is_empty() {
        program.remove(&n);
        Ok(false)
    } else {
        program.insert(n, line);
        Ok(true)
    }
}

/// Starts interactive editing after the last line of the program and ends on the first empty line.
/// Uses the `console` for input/output.
fn append(program: &mut ProgramImpl, console: &mut dyn Console) -> io::Result<()> {
    let mut last_n = match program.iter().next_back() {
        Some((k, _)) => (*k / 10) * 10 + 10,
        None => 10,
    };
    while edit_one(program, last_n, console)? {
        last_n += 10;
    }
    Ok(())
}

/// The `EDIT` command.
struct EditCommand {
    console: Rc<RefCell<dyn Console>>,
    program: Program,
}

impl BuiltinCommand for EditCommand {
    fn name(&self) -> &'static str {
        "EDIT"
    }

    fn syntax(&self) -> &'static str {
        "[lineno%]"
    }

    fn description(&self) -> &'static str {
        "Edits the stored program.
Without a line number, starts interactive editing at the last line of the stored program (or the \
first line if there is no program yet).  Editing ends on the first empty line.
With a line number, and if the line does not yet exist, enters interactive editing for that line \
only.  Otherwise, if the line already exists, presents the contents of that line for interactive \
editing.  Editing terminates upon an ENTER key press."
    }

    fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
        let mut console = self.console.borrow_mut();
        match args {
            [] => append(&mut self.program.borrow_mut(), &mut *console)?,
            [(Some(expr), ArgSep::End)] => match expr.eval(machine.get_vars())? {
                Value::Integer(n) => {
                    ensure!(n > 0, "Line numbers must be a positive integer");
                    edit_one(&mut self.program.borrow_mut(), n as usize, &mut *console)?;
                }
                _ => bail!("Line numbers must be a positive integer"),
            },
            _ => bail!("EDIT takes no arguments or a line number"),
        }
        Ok(())
    }
}

/// The `LIST` command.
struct ListCommand {
    console: Rc<RefCell<dyn Console>>,
    program: Program,
}

impl BuiltinCommand for ListCommand {
    fn name(&self) -> &'static str {
        "LIST"
    }

    fn syntax(&self) -> &'static str {
        ""
    }

    fn description(&self) -> &'static str {
        "Lists the contents of the stored program."
    }

    fn exec(&self, args: &[(Option<Expr>, ArgSep)], _machine: &mut Machine) -> Fallible<()> {
        ensure!(args.is_empty(), "LIST takes no arguments");
        let mut console = self.console.borrow_mut();
        let program = self.program.borrow();
        for (k, v) in program.iter() {
            console.print(&format!("{} {}", k, v))?;
        }
        console.print("")?;
        Ok(())
    }
}

/// The `NEW` command.
struct NewCommand {
    program: Program,
}

impl BuiltinCommand for NewCommand {
    fn name(&self) -> &'static str {
        "NEW"
    }

    fn syntax(&self) -> &'static str {
        ""
    }

    fn description(&self) -> &'static str {
        "Clears the stored program from memory."
    }

    fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
        ensure!(args.is_empty(), "NEW takes no arguments");
        *self.program.borrow_mut() = BTreeMap::default();
        machine.clear();
        Ok(())
    }
}

/// The `RENUM` command.
struct RenumCommand {
    program: Program,
}

impl BuiltinCommand for RenumCommand {
    fn name(&self) -> &'static str {
        "RENUM"
    }

    fn syntax(&self) -> &'static str {
        ""
    }

    fn description(&self) -> &'static str {
        "Reassigns line numbers to make them all multiples of ten."
    }

    fn exec(&self, args: &[(Option<Expr>, ArgSep)], _machine: &mut Machine) -> Fallible<()> {
        ensure!(args.is_empty(), "RENUM takes no arguments");
        let mut program = self.program.borrow_mut();
        let numbers: Vec<usize> = program.keys().cloned().collect();
        let mut lines = numbers.len();
        let mut new_program = BTreeMap::default();
        for k in numbers.iter().rev() {
            let new_line = lines * 10;
            let content = program.remove(k).unwrap();
            new_program.insert(new_line, content);
            lines -= 1;
        }
        *program = new_program;
        Ok(())
    }
}

/// The `RUN` command.
struct RunCommand {
    program: Program,
}

impl BuiltinCommand for RunCommand {
    fn name(&self) -> &'static str {
        "RUN"
    }

    fn syntax(&self) -> &'static str {
        ""
    }

    fn description(&self) -> &'static str {
        "Runs the stored program.
Note that the program runs in the context of the interpreter so it will pick up any variables \
and other state that may already be set."
    }

    fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
        ensure!(args.is_empty(), "RUN takes no arguments");
        let program = self.program.borrow();
        let mut text = String::new();
        for (_, v) in program.iter() {
            text += v;
            text += "\n";
        }
        machine.exec(&mut text.as_bytes())
    }
}

/// Instantiates all program editing commands against the stored `program`.
fn all_commands_for(
    program: Program,
    console: Rc<RefCell<dyn Console>>,
) -> Vec<Rc<dyn BuiltinCommand>> {
    vec![
        Rc::from(EditCommand {
            console: console.clone(),
            program: program.clone(),
        }),
        Rc::from(ListCommand {
            console: console.clone(),
            program: program.clone(),
        }),
        Rc::from(NewCommand {
            program: program.clone(),
        }),
        Rc::from(RenumCommand {
            program: program.clone(),
        }),
        Rc::from(RunCommand { program: program }),
    ]
}

/// Instantiates all program editing commands against a new (empty) stored program.
pub fn all_commands(console: Rc<RefCell<dyn Console>>) -> Vec<Rc<dyn BuiltinCommand>> {
    all_commands_for(Program::default(), console)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::console::testutils::*;
    use crate::exec::testutils::*;
    use crate::exec::MachineBuilder;

    /// Runs the `input` code on a new machine and verifies its output.
    ///
    /// `golden_in` is a sequence of pairs each containing an expected prompt printed by `INPUT`
    /// and the reply to feed to that prompt.
    ///
    /// `expected_out` is a sequence of expected calls to `PRINT`.
    ///
    /// `exp_program` is the expected state of `program` after execution, as a collection of line
    /// number and content pairs.
    fn do_ok_test(
        program: Program,
        input: &str,
        golden_in: &'static [(&'static str, &'static str, &'static str)],
        expected_out: &'static [&'static str],
        exp_program: &'static [(usize, &'static str)],
    ) {
        let console = Rc::from(RefCell::from(MockConsole::new(golden_in)));
        let mut machine = MachineBuilder::default()
            .add_builtins(all_commands_for(program.clone(), console.clone()))
            .build();
        machine
            .exec(&mut input.as_bytes())
            .expect("Execution failed");
        assert_eq!(expected_out, console.borrow().captured_out());

        let program = program.borrow();
        let flat_program: Vec<(usize, &str)> =
            program.iter().map(|(k, v)| (*k, v.as_str())).collect();
        assert_eq!(exp_program, flat_program.as_slice());
    }

    /// Runs the `input` code on a new machine and verifies that it fails with `expected_err`.
    ///
    /// Ensures that this does not touch the console.
    fn do_error_test(input: &str, expected_err: &str) {
        let console = Rc::from(RefCell::from(MockConsole::new(&[])));
        let mut machine = MachineBuilder::default()
            .add_builtins(all_commands_for(Program::default(), console.clone()))
            .build();
        assert_eq!(
            expected_err,
            format!(
                "{}",
                machine
                    .exec(&mut input.as_bytes())
                    .expect_err("Execution did not fail")
            )
        );
        assert!(console.borrow().captured_out().is_empty());
    }

    #[test]
    fn test_edit_append_empty() {
        let program = Program::default();
        do_ok_test(
            program,
            "EDIT",
            &[("10 ", "", "first"), ("20 ", "", "second"), ("30 ", "", "")],
            &[],
            &[(10, "first"), (20, "second")],
        );
    }

    #[test]
    fn test_edit_append_resume() {
        let program = Program::default();
        do_ok_test(
            program.clone(),
            "EDIT",
            &[("10 ", "", "first"), ("20 ", "", "")],
            &[],
            &[(10, "first")],
        );
        do_ok_test(
            program,
            "EDIT",
            &[("20 ", "", "second"), ("30 ", "", "third"), ("40 ", "", "")],
            &[],
            &[(10, "first"), (20, "second"), (30, "third")],
        );
    }

    #[test]
    fn test_edit_append_to_arbitrary_number() {
        let program = Program::default();
        program.borrow_mut().insert(28, "next is 30".to_owned());
        do_ok_test(
            program,
            "EDIT",
            &[("30 ", "", "correct"), ("40 ", "", "")],
            &[],
            &[(28, "next is 30"), (30, "correct")],
        );
    }

    #[test]
    fn test_edit_one_empty() {
        let program = Program::default();
        program.borrow_mut().insert(7, "before".to_owned());
        program.borrow_mut().insert(9, "after".to_owned());
        do_ok_test(
            program,
            "EDIT 8",
            &[("8 ", "", "some text")],
            &[],
            &[(7, "before"), (8, "some text"), (9, "after")],
        );
    }

    #[test]
    fn test_edit_one_existing() {
        let program = Program::default();
        program.borrow_mut().insert(7, "before".to_owned());
        program.borrow_mut().insert(8, "some text".to_owned());
        program.borrow_mut().insert(9, "after".to_owned());
        do_ok_test(
            program,
            "EDIT 8",
            &[("8 ", "some text", "new")],
            &[],
            &[(7, "before"), (8, "new"), (9, "after")],
        );
    }

    #[test]
    fn test_edit_delete() {
        let program = Program::default();
        program.borrow_mut().insert(7, "before".to_owned());
        program.borrow_mut().insert(8, "some text".to_owned());
        program.borrow_mut().insert(9, "after".to_owned());
        do_ok_test(
            program,
            "EDIT 8",
            &[("8 ", "some text", "")],
            &[],
            &[(7, "before"), (9, "after")],
        );
    }

    #[test]
    fn test_edit_errors() {
        do_error_test("EDIT 1, 2", "EDIT takes no arguments or a line number");
        do_error_test("EDIT 0", "Line numbers must be a positive integer");
        do_error_test("EDIT -9", "Line numbers must be a positive integer");
        do_error_test("EDIT \"foo\"", "Line numbers must be a positive integer");
    }

    #[test]
    fn test_list_nothing() {
        let program = Program::default();
        do_ok_test(program, "LIST", &[], &[""], &[]);
    }

    #[test]
    fn test_list_something() {
        let program = Program::default();
        program.borrow_mut().insert(10, "first".to_owned());
        program
            .borrow_mut()
            .insert(1023, "    second line".to_owned());
        do_ok_test(
            program,
            "LIST",
            &[],
            &["10 first", "1023     second line", ""],
            &[(10, "first"), (1023, "    second line")],
        );
    }

    #[test]
    fn test_list_errors() {
        do_error_test("LIST 10", "LIST takes no arguments");
    }

    #[test]
    fn test_new_nothing() {
        let program = Program::default();
        do_ok_test(program, "NEW", &[], &[], &[]);
    }

    #[test]
    fn test_new_clears_program_and_variables() {
        let program = Program::default();
        program.borrow_mut().insert(10, "some stuff".to_owned());

        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(NewCommand {
                program: program.clone(),
            }))
            .build();

        machine.exec(&mut b"NEW".as_ref()).unwrap();
        assert!(program.borrow().is_empty());
        assert!(machine.get_vars().is_empty());
    }

    #[test]
    fn test_new_errors() {
        do_error_test("NEW 10", "NEW takes no arguments");
    }

    #[test]
    fn test_renum_no_changes() {
        let program = Program::default();
        program.borrow_mut().insert(10, "one".to_owned());
        program.borrow_mut().insert(20, "two".to_owned());
        program.borrow_mut().insert(30, "three".to_owned());
        do_ok_test(
            program,
            "RENUM",
            &[],
            &[],
            &[(10, "one"), (20, "two"), (30, "three")],
        );
    }

    #[test]
    fn test_renum_insertion() {
        let program = Program::default();
        program.borrow_mut().insert(10, "one".to_owned());
        program.borrow_mut().insert(15, "two".to_owned());
        program.borrow_mut().insert(20, "three".to_owned());
        do_ok_test(
            program,
            "RENUM",
            &[],
            &[],
            &[(10, "one"), (20, "two"), (30, "three")],
        );
    }

    #[test]
    fn test_renum_deletion() {
        let program = Program::default();
        program.borrow_mut().insert(10, "one".to_owned());
        program.borrow_mut().insert(30, "three".to_owned());
        do_ok_test(program, "RENUM", &[], &[], &[(10, "one"), (20, "three")]);
    }

    #[test]
    fn test_renum_shift() {
        let program = Program::default();
        program.borrow_mut().insert(10, "one".to_owned());
        program.borrow_mut().insert(78, "two".to_owned());
        program.borrow_mut().insert(1294, "three".to_owned());
        do_ok_test(
            program,
            "RENUM",
            &[],
            &[],
            &[(10, "one"), (20, "two"), (30, "three")],
        );
    }

    #[test]
    fn test_renum_errors() {
        do_error_test("RENUM 10", "RENUM takes no arguments");
    }

    #[test]
    fn test_run_nothing() {
        let program = Program::default();
        do_ok_test(program, "RUN", &[], &[], &[]);
    }

    #[test]
    fn test_run_something_that_shares_state() {
        let program = Program::default();
        program.borrow_mut().insert(23, "OUT var".to_owned());
        program.borrow_mut().insert(72, "var = var + 1".to_owned());

        let captured_out = Rc::from(RefCell::from(vec![]));
        let out_cmd = OutCommand::from(captured_out.clone());
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(out_cmd))
            .add_builtin(Rc::from(RunCommand { program }))
            .build();

        machine.exec(&mut b"var = 7: RUN".as_ref()).unwrap();
        assert_eq!(&["7"], captured_out.borrow().as_slice());

        captured_out.borrow_mut().clear();
        machine.exec(&mut b"RUN".as_ref()).unwrap();
        assert_eq!(&["8"], captured_out.borrow().as_slice());
    }

    #[test]
    fn test_run_errors() {
        do_error_test("RUN 10", "RUN takes no arguments");
    }
}
