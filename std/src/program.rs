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

//! Stored program manipulation.

use crate::console::Console;
use crate::storage::Storage;
use async_trait::async_trait;
use endbasic_core::ast::{ArgSep, Expr, Value, VarType};
use endbasic_core::exec::Machine;
use endbasic_core::syms::{
    CallError, CallableMetadata, CallableMetadataBuilder, Command, CommandResult,
};
use std::cell::RefCell;
use std::io;
use std::path::PathBuf;
use std::rc::Rc;
use std::str;

/// Category description for all symbols provided by this module.
const CATEGORY: &str = "Stored program
The EndBASIC interpreter has a piece of read/write memory called the \"stored program\".  This \
memory serves to maintain the code of a program you edit and manipulate right from the \
interpreter.
The common flow to interact with a stored program is to load a program from disk using the LOAD \
command, modify its contents via the EDIT command, execute the program via the RUN command, and \
finally save the new or modified program via the SAVE command.
Be aware that the stored program's content is lost whenever you load a program, exit the \
interpreter, or use the NEW command, so don't forget to save it.
See the \"File system\" help topic for information on where the programs can be saved and loaded \
from.";

/// Representation of the single program that we can keep in memory.
#[async_trait(?Send)]
pub trait Program {
    /// Edits the program interactively via the given `console`.
    async fn edit(&mut self, console: &mut dyn Console) -> io::Result<()>;

    /// Reloads the contents of the stored program with the given `text`.
    fn load(&mut self, text: &str);

    /// Gets the contents of the stored program as a single string.
    fn text(&self) -> String;
}

/// Adds an extension to `path` if one is not present.
fn add_extension<S: Into<PathBuf>>(path: S) -> io::Result<String> {
    let mut path = path.into();

    if let Some(ext) = path.extension() {
        if ext != "bas" && ext != "BAS" {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "Invalid filename extension"));
        }
    } else {
        // Attempt to determine a sensible extension based on the case of the basename, assuming
        // that an all-uppercase basename wants an all-uppercase extension.  This is fragile on
        // case-sensitive file systems, but there is not a lot we can do.
        let mut ext = "BAS";
        for ch in path.to_string_lossy().chars() {
            if ch.is_ascii_lowercase() {
                ext = "bas";
                break;
            }
        }
        path.set_extension(ext);
    }
    Ok(path.to_str().expect("Path came from a String").to_owned())
}

/// The `DEL` command.
// TODO(jmmv): This should be in the storage module because it isn't really tied to the stored
// program.  However, this currently relies on the automatic addition of extensions to file names,
// which is logic that should only exist here.  Maybe we should remove that from this command.
pub struct DelCommand {
    metadata: CallableMetadata,
    storage: Rc<RefCell<Storage>>,
}

impl DelCommand {
    /// Creates a new `DEL` command that deletes a file from `storage`.
    pub fn new(storage: Rc<RefCell<Storage>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("DEL", VarType::Void)
                .with_syntax("filename")
                .with_category(CATEGORY)
                .with_description(
                    "Deletes the given program.
The filename must be a string and must be a basename (no directory components).  The .BAS \
extension is optional, but if present, it must be .BAS.",
                )
                .build(),
            storage,
        })
    }
}

#[async_trait(?Send)]
impl Command for DelCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        if args.len() != 1 {
            return Err(CallError::ArgumentError("DEL requires a filename".to_owned()));
        }
        let arg0 = args[0].0.as_ref().expect("Single argument must be present");
        match arg0.eval(machine.get_mut_symbols())? {
            Value::Text(t) => {
                let name = add_extension(t)?;
                self.storage.borrow_mut().delete(&name).await?;
            }
            _ => {
                return Err(CallError::ArgumentError(
                    "DEL requires a string as the filename".to_owned(),
                ))
            }
        }
        Ok(())
    }
}

/// The `EDIT` command.
pub struct EditCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
    program: Rc<RefCell<dyn Program>>,
}

impl EditCommand {
    /// Creates a new `EDIT` command that edits the stored `program` in the `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>, program: Rc<RefCell<dyn Program>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("EDIT", VarType::Void)
                .with_syntax("")
                .with_category(CATEGORY)
                .with_description("Interactively edits the stored program.")
                .build(),
            console,
            program,
        })
    }
}

#[async_trait(?Send)]
impl Command for EditCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], _machine: &mut Machine) -> CommandResult {
        if !args.is_empty() {
            return Err(CallError::ArgumentError("EDIT takes no arguments".to_owned()));
        }

        let mut console = self.console.borrow_mut();
        let mut program = self.program.borrow_mut();
        program.edit(&mut *console).await?;
        Ok(())
    }
}

/// The `LIST` command.
pub struct ListCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
    program: Rc<RefCell<dyn Program>>,
}

impl ListCommand {
    /// Creates a new `LIST` command that dumps the `program` to the `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>, program: Rc<RefCell<dyn Program>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("LIST", VarType::Void)
                .with_syntax("")
                .with_category(CATEGORY)
                .with_description("Prints the currently-loaded program.")
                .build(),
            console,
            program,
        })
    }
}

#[async_trait(?Send)]
impl Command for ListCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], _machine: &mut Machine) -> CommandResult {
        if !args.is_empty() {
            return Err(CallError::ArgumentError("LIST takes no arguments".to_owned()));
        }
        let program = self.program.borrow().text();
        let program: Vec<&str> = program.lines().collect();
        let digits = {
            let mut digits = 0;
            let mut count = program.len();
            while count > 0 {
                digits += 1;
                count /= 10;
            }
            digits
        };
        let mut console = self.console.borrow_mut();
        for (i, line) in program.into_iter().enumerate() {
            let formatted = format!("{:digits$} | {}", i + 1, line, digits = digits);
            console.print(&formatted)?;
        }
        Ok(())
    }
}

/// The `LOAD` command.
pub struct LoadCommand {
    metadata: CallableMetadata,
    storage: Rc<RefCell<Storage>>,
    program: Rc<RefCell<dyn Program>>,
}

impl LoadCommand {
    /// Creates a new `LOAD` command that loads a program from `storage` into `program`.
    pub fn new(storage: Rc<RefCell<Storage>>, program: Rc<RefCell<dyn Program>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("LOAD", VarType::Void)
                .with_syntax("filename")
                .with_category(CATEGORY)
                .with_description(
                    "Loads the given program.
The filename must be a string and must be a basename (no directory components).  The .BAS \
extension is optional, but if present, it must be .BAS.",
                )
                .build(),
            storage,
            program,
        })
    }
}

#[async_trait(?Send)]
impl Command for LoadCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        if args.len() != 1 {
            return Err(CallError::ArgumentError("LOAD requires a filename".to_owned()));
        }
        let arg0 = args[0].0.as_ref().expect("Single argument must be present");
        match arg0.eval(machine.get_mut_symbols())? {
            Value::Text(t) => {
                let name = add_extension(t)?;
                let content = self.storage.borrow().get(&name).await?;
                self.program.borrow_mut().load(&content);
                machine.clear();
            }
            _ => {
                return Err(CallError::ArgumentError(
                    "LOAD requires a string as the filename".to_owned(),
                ))
            }
        }
        Ok(())
    }
}

/// The `NEW` command.
pub struct NewCommand {
    metadata: CallableMetadata,
    program: Rc<RefCell<dyn Program>>,
}

impl NewCommand {
    /// Creates a new `NEW` command that clears the contents of `program`.
    pub fn new(program: Rc<RefCell<dyn Program>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("NEW", VarType::Void)
                .with_syntax("")
                .with_category(CATEGORY)
                .with_description("Clears the stored program from memory.")
                .build(),
            program,
        })
    }
}

#[async_trait(?Send)]
impl Command for NewCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        if !args.is_empty() {
            return Err(CallError::ArgumentError("NEW takes no arguments".to_owned()));
        }
        self.program.borrow_mut().load("");
        machine.clear();
        Ok(())
    }
}

/// The `RUN` command.
pub struct RunCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
    program: Rc<RefCell<dyn Program>>,
}

impl RunCommand {
    /// Creates a new `RUN` command that executes the `program`.
    ///
    /// Reports any non-successful return codes from the program to the console.
    pub fn new(console: Rc<RefCell<dyn Console>>, program: Rc<RefCell<dyn Program>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("RUN", VarType::Void)
                .with_syntax("")
                .with_category(CATEGORY)
                .with_description(
                    "Runs the stored program.
Note that the program runs in the context of the interpreter so it will pick up any variables \
and other state that may already be set.",
                )
                .build(),
            console,
            program,
        })
    }
}

#[async_trait(?Send)]
impl Command for RunCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        if !args.is_empty() {
            return Err(CallError::ArgumentError("RUN takes no arguments".to_owned()));
        }
        let program = self.program.borrow().text();
        let stop_reason = match machine.exec(&mut program.as_bytes()).await {
            Ok(stop_reason) => stop_reason,
            Err(e) => {
                // TODO(jmmv): This conversion to an internal error is not great and is just a
                // workaround for the mess that CallError currently is in the context of commands.
                return Err(CallError::InternalError(format!("{}", e)));
            }
        };
        if stop_reason.as_exit_code() != 0 {
            self.console
                .borrow_mut()
                .print(&format!("Program exited with code {}", stop_reason.as_exit_code()))?;
        }
        Ok(())
    }
}

/// The `SAVE` command.
pub struct SaveCommand {
    metadata: CallableMetadata,
    storage: Rc<RefCell<Storage>>,
    program: Rc<RefCell<dyn Program>>,
}

impl SaveCommand {
    /// Creates a new `SAVE` command that saves the contents of the `program` into `storage`.
    pub fn new(storage: Rc<RefCell<Storage>>, program: Rc<RefCell<dyn Program>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("SAVE", VarType::Void)
                .with_syntax("filename")
                .with_category(CATEGORY)
                .with_description(
                    "Saves the current program in memory to the given filename.
The filename must be a string and must be a basename (no directory components).  The .BAS \
extension is optional, but if present, it must be .BAS.",
                )
                .build(),
            storage,
            program,
        })
    }
}

#[async_trait(?Send)]
impl Command for SaveCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        if args.len() != 1 {
            return Err(CallError::ArgumentError("SAVE requires a filename".to_owned()));
        }
        let arg0 = args[0].0.as_ref().expect("Single argument must be present");
        match arg0.eval(machine.get_mut_symbols())? {
            Value::Text(t) => {
                let name = add_extension(t)?;
                let content = self.program.borrow().text();
                self.storage.borrow_mut().put(&name, &content).await?;
            }
            _ => {
                return Err(CallError::ArgumentError(
                    "SAVE requires a string as the filename".to_owned(),
                ))
            }
        }
        Ok(())
    }
}

/// Adds all program editing commands against the stored `program` to the `machine`, using
/// `console` for interactive editing and using `storage` as the on-disk storage for the programs.
pub fn add_all(
    machine: &mut Machine,
    program: Rc<RefCell<dyn Program>>,
    console: Rc<RefCell<dyn Console>>,
    storage: Rc<RefCell<Storage>>,
) {
    machine.add_command(DelCommand::new(storage.clone()));
    machine.add_command(EditCommand::new(console.clone(), program.clone()));
    machine.add_command(ListCommand::new(console.clone(), program.clone()));
    machine.add_command(LoadCommand::new(storage.clone(), program.clone()));
    machine.add_command(NewCommand::new(program.clone()));
    machine.add_command(RunCommand::new(console, program.clone()));
    machine.add_command(SaveCommand::new(storage, program));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;

    #[test]
    fn test_del_ok() {
        for p in &["foo", "foo.bas"] {
            Tester::default()
                .set_program("Leave me alone")
                .write_file("bar.bas", "")
                .write_file("foo.bas", "line 1\n  line 2\n")
                .run(format!(r#"DEL "{}""#, p))
                .expect_program("Leave me alone")
                .expect_file("MEMORY:/bar.bas", "")
                .check();
        }
    }

    #[test]
    fn test_del_errors() {
        check_load_save_common_errors("DEL");

        check_stmt_err("Entry not found", r#"DEL "missing-file""#);

        Tester::default()
            .write_file("mismatched-extension.bat", "")
            .run(r#"DEL "mismatched-extension""#)
            .expect_err("Entry not found")
            .expect_file("MEMORY:/mismatched-extension.bat", "")
            .check();
    }

    #[test]
    fn test_edit_ok() {
        Tester::default()
            .set_program("previous\n")
            .add_input_chars("new line\n")
            .run("EDIT")
            .expect_program("previous\nnew line\n")
            .check();
    }

    #[test]
    fn test_edit_errors() {
        check_stmt_err("EDIT takes no arguments", "EDIT 1");
    }

    #[test]
    fn test_list_ok() {
        Tester::default().run("LIST").check();

        Tester::default()
            .set_program("one\n\nthree\n")
            .run("LIST")
            .expect_prints(["1 | one", "2 | ", "3 | three"])
            .expect_program("one\n\nthree\n")
            .check();

        Tester::default()
            .set_program("a\nb\nc\nd\ne\nf\ng\nh\ni\nj\n")
            .run("LIST")
            .expect_prints([
                " 1 | a", " 2 | b", " 3 | c", " 4 | d", " 5 | e", " 6 | f", " 7 | g", " 8 | h",
                " 9 | i", "10 | j",
            ])
            .expect_program("a\nb\nc\nd\ne\nf\ng\nh\ni\nj\n")
            .check();
    }

    #[test]
    fn test_list_errors() {
        check_stmt_err("LIST takes no arguments", "LIST 2");
    }

    #[test]
    fn test_load_ok() {
        let content = "line 1\n\n  line 2\n";
        for p in &["foo", "foo.bas", "BAR", "BAR.BAS", "Baz"] {
            Tester::default()
                .write_file("foo.bas", content)
                .write_file("foo.bak", "")
                .write_file("BAR.BAS", content)
                .write_file("Baz.bas", content)
                .run(format!(r#"LOAD "{}""#, p))
                .expect_program("line 1\n\n  line 2\n")
                .expect_file("MEMORY:/foo.bas", content)
                .expect_file("MEMORY:/foo.bak", "")
                .expect_file("MEMORY:/BAR.BAS", content)
                .expect_file("MEMORY:/Baz.bas", content)
                .check();
        }
    }

    /// Checks errors that should be handled the same way by `LOAD` and `SAVE`.
    fn check_load_save_common_errors(cmd: &str) {
        Tester::default().run(cmd).expect_err(format!("{} requires a filename", cmd)).check();

        Tester::default()
            .run(format!("{} 3", cmd))
            .expect_err(format!("{} requires a string as the filename", cmd))
            .check();

        Tester::default()
            .run(format!(r#"{} "a/b.bas""#, cmd))
            .expect_err("Too many / separators in path 'a/b.bas'".to_owned())
            .check();

        for p in &["foo.bak", "foo.ba", "foo.basic"] {
            Tester::default()
                .run(format!(r#"{} "{}""#, cmd, p))
                .expect_err("Invalid filename extension".to_owned())
                .check();
        }
    }

    #[test]
    fn test_load_errors() {
        check_load_save_common_errors("LOAD");

        check_stmt_err("Entry not found", r#"LOAD "missing-file""#);

        Tester::default()
            .write_file("mismatched-extension.bat", "")
            .run(r#"LOAD "mismatched-extension""#)
            .expect_err("Entry not found")
            .expect_file("MEMORY:/mismatched-extension.bat", "")
            .check();
    }

    #[test]
    fn test_new_nothing() {
        Tester::default().run("NEW").check();
    }

    #[test]
    fn test_new_clears_program_and_variables() {
        Tester::default().set_program("some stuff").run("a = 3: NEW").check();
    }

    #[test]
    fn test_new_errors() {
        check_stmt_err("NEW takes no arguments", "NEW 10");
    }

    #[test]
    fn test_run_nothing() {
        Tester::default().run("RUN").check();
    }

    #[test]
    fn test_run_something_that_shares_state() {
        let program = "PRINT var: var = var + 1";
        let mut t = Tester::default().set_program(program);
        t.run("var = 7: RUN")
            .expect_prints(["7"])
            .expect_var("var", 8)
            .expect_program(program)
            .check();
        t.run("RUN").expect_prints(["7", "8"]).expect_var("var", 9).expect_program(program).check();
    }

    #[test]
    fn test_run_something_that_exits() {
        let program = "PRINT 5: EXIT 1: PRINT 4";
        Tester::default()
            .set_program(program)
            .run(r#"RUN: PRINT "after""#)
            .expect_prints(["5", "Program exited with code 1", "after"])
            .expect_program(program)
            .check();
    }

    #[test]
    fn test_run_errors() {
        check_stmt_err("RUN takes no arguments", "RUN 10");
    }

    #[test]
    fn test_save_ok() {
        let content = "\n some line   \n ";
        for (explicit, actual) in &[
            ("first", "MEMORY:/first.bas"),
            ("second.bas", "MEMORY:/second.bas"),
            ("THIRD", "MEMORY:/THIRD.BAS"),
            ("FOURTH.BAS", "MEMORY:/FOURTH.BAS"),
            ("Fifth", "MEMORY:/Fifth.bas"),
        ] {
            Tester::default()
                .set_program(content)
                .run(format!(r#"SAVE "{}""#, explicit))
                .expect_program(content)
                .expect_file(*actual, content)
                .check();
        }
    }

    #[test]
    fn test_save_errors() {
        check_load_save_common_errors("SAVE");
    }
}
