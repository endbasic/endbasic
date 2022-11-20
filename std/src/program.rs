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

use crate::console::{read_line, Console};
use crate::storage::Storage;
use async_trait::async_trait;
use endbasic_core::ast::{ArgSep, ArgSpan, BuiltinCallSpan, Value, VarType};
use endbasic_core::exec::{Machine, StopReason};
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
interpreter, or use the NEW command.  These operations will ask you to save the program if you \
have forgotten to do so, but it's better to get in the habit of saving often.
See the \"File system\" help topic for information on where the programs can be saved and loaded \
from.";

/// Representation of the single program that we can keep in memory.
#[async_trait(?Send)]
pub trait Program {
    /// Returns true if the program was modified since it was last saved (as indicated by a call to
    /// `set_name`).
    fn is_dirty(&self) -> bool;

    /// Edits the program interactively via the given `console`.
    async fn edit(&mut self, console: &mut dyn Console) -> io::Result<()>;

    /// Reloads the contents of the stored program with the given `text` and tracks them as coming
    /// from the file given in `name`.
    fn load(&mut self, name: Option<&str>, text: &str);

    /// Path of the loaded program.  Should be `None` if the program has never been saved yet.
    fn name(&self) -> Option<&str>;

    /// Resets the name of the program.  Used when saving it.
    fn set_name(&mut self, name: &str);

    /// Gets the contents of the stored program as a single string.
    fn text(&self) -> String;
}

/// Trivial implementation of a recorded program that doesn't support editing.
#[derive(Default)]
pub(crate) struct ImmutableProgram {
    name: Option<String>,
    text: String,
}

#[async_trait(?Send)]
impl Program for ImmutableProgram {
    fn is_dirty(&self) -> bool {
        false
    }

    async fn edit(&mut self, _console: &mut dyn Console) -> io::Result<()> {
        Err(io::Error::new(io::ErrorKind::Other, "Editing not supported"))
    }

    fn load(&mut self, name: Option<&str>, text: &str) {
        self.name = name.map(str::to_owned);
        self.text = text.to_owned();
    }

    fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    fn set_name(&mut self, name: &str) {
        self.name = Some(name.to_owned());
    }

    fn text(&self) -> String {
        self.text.clone()
    }
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

/// If the `program` is dirty, asks if it's OK to continue on `console` and discard its changes.
pub async fn continue_if_modified(
    program: &dyn Program,
    console: &mut dyn Console,
) -> io::Result<bool> {
    if !program.is_dirty() {
        return Ok(true);
    }

    match program.name() {
        Some(name) => console.print(&format!("Current program {} has unsaved changes!", name))?,
        None => console.print("Current program has unsaved changes and has never been saved!")?,
    }
    let answer = read_line(console, "Discard and continue (y/N)? ", "", None).await?;
    match Value::parse_as(VarType::Boolean, answer) {
        Ok(Value::Boolean(b)) => Ok(b),
        _ => Ok(false),
    }
}

/// The `KILL` command.
// TODO(jmmv): This should be in the storage module because it isn't really tied to the stored
// program.  However, this currently relies on the automatic addition of extensions to file names,
// which is logic that should only exist here.  Maybe we should remove that from this command.
pub struct KillCommand {
    metadata: CallableMetadata,
    storage: Rc<RefCell<Storage>>,
}

impl KillCommand {
    /// Creates a new `KILL` command that deletes a file from `storage`.
    pub fn new(storage: Rc<RefCell<Storage>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("KILL", VarType::Void)
                .with_syntax("filename$")
                .with_category(CATEGORY)
                .with_description(
                    "Deletes the given program.
The filename must be a string and must be a valid EndBASIC path.  The .BAS extension is optional \
but, if present, it must be .BAS.
See the \"File system\" help topic for information on the path syntax.",
                )
                .build(),
            storage,
        })
    }
}

#[async_trait(?Send)]
impl Command for KillCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        if span.args.len() != 1 {
            return Err(CallError::SyntaxError);
        }
        let arg0 = span.args[0].expr.as_ref().expect("Single argument must be present");
        match arg0.eval(machine.get_mut_symbols()).await? {
            Value::Text(t) => {
                let name = add_extension(t)?;
                self.storage.borrow_mut().delete(&name).await?;
            }
            _ => {
                return Err(CallError::ArgumentError(
                    arg0.start_pos(),
                    "KILL requires a string as the filename".to_owned(),
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

    async fn exec(&self, span: &BuiltinCallSpan, _machine: &mut Machine) -> CommandResult {
        if !span.args.is_empty() {
            return Err(CallError::SyntaxError);
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

    async fn exec(&self, span: &BuiltinCallSpan, _machine: &mut Machine) -> CommandResult {
        if !span.args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        let mut console = self.console.borrow_mut();
        for line in self.program.borrow().text().lines() {
            console.print(line)?;
        }
        Ok(())
    }
}

/// The `LOAD` command.
pub struct LoadCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
    storage: Rc<RefCell<Storage>>,
    program: Rc<RefCell<dyn Program>>,
}

impl LoadCommand {
    /// Creates a new `LOAD` command that loads a program from `storage` into `program` and that
    /// uses `console` to communicate unsaved changes.
    pub fn new(
        console: Rc<RefCell<dyn Console>>,
        storage: Rc<RefCell<Storage>>,
        program: Rc<RefCell<dyn Program>>,
    ) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("LOAD", VarType::Void)
                .with_syntax("filename$")
                .with_category(CATEGORY)
                .with_description(
                    "Loads the given program.
The filename must be a string and must be a valid EndBASIC path.  The .BAS extension is optional \
but, if present, it must be .BAS.
Any previously stored program is discarded from memory, but LOAD will pause to ask before \
discarding any unsaved modifications.
See the \"File system\" help topic for information on the path syntax.",
                )
                .build(),
            console,
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

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        if span.args.len() != 1 {
            return Err(CallError::SyntaxError);
        }
        let arg0 = span.args[0].expr.as_ref().expect("Single argument must be present");
        let name = match arg0.eval(machine.get_mut_symbols()).await? {
            Value::Text(t) => add_extension(t)?,
            _ => {
                return Err(CallError::ArgumentError(
                    arg0.start_pos(),
                    "LOAD requires a string as the filename".to_owned(),
                ))
            }
        };

        if continue_if_modified(&*self.program.borrow(), &mut *self.console.borrow_mut()).await? {
            let content = self.storage.borrow().get(&name).await?;
            let full_name = self.storage.borrow().make_canonical(&name)?;
            self.program.borrow_mut().load(Some(&full_name), &content);
            machine.clear();
        } else {
            self.console
                .borrow_mut()
                .print("LOAD aborted; use SAVE to save your current changes.")?;
        }
        Ok(())
    }
}

/// The `NEW` command.
pub struct NewCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
    program: Rc<RefCell<dyn Program>>,
}

impl NewCommand {
    /// Creates a new `NEW` command that clears the contents of `program` and that uses `console`
    /// to communicate unsaved changes.
    pub fn new(console: Rc<RefCell<dyn Console>>, program: Rc<RefCell<dyn Program>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("NEW", VarType::Void)
                .with_syntax("")
                .with_category(CATEGORY)
                .with_description(
                    "Restores initial machine state and creates a new program.
This command resets the machine to a pristine state by clearing all user-defined variables \
and restoring the state of shared resources.  These resources include: the console, whose color \
and video syncing bit are reset; and the GPIO pins, which are set to their default state.
The stored program is also discarded from memory, but NEW will pause to ask before discarding \
any unsaved modifications.  To reset resources but avoid clearing the stored program, use CLEAR \
instead.",
                )
                .build(),
            console,
            program,
        })
    }
}

#[async_trait(?Send)]
impl Command for NewCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        if !span.args.is_empty() {
            return Err(CallError::SyntaxError);
        }

        if continue_if_modified(&*self.program.borrow(), &mut *self.console.borrow_mut()).await? {
            self.program.borrow_mut().load(None, "");
            machine.clear();
        } else {
            self.console
                .borrow_mut()
                .print("NEW aborted; use SAVE to save your current changes.")?;
        }
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
This issues a CLEAR operation before starting the program to prevent previous leftover state \
from interfering with the new execution.",
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

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        if !span.args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        machine.clear();
        let program = self.program.borrow().text();
        let stop_reason = match machine.exec(&mut program.as_bytes()).await {
            Ok(stop_reason) => stop_reason,
            Err(e) => return Err(CallError::NestedError(format!("{}", e))),
        };
        match stop_reason {
            StopReason::Break => self.console.borrow_mut().print("**** BREAK ****")?,
            stop_reason => {
                if stop_reason.as_exit_code() != 0 {
                    self.console.borrow_mut().print(&format!(
                        "Program exited with code {}",
                        stop_reason.as_exit_code()
                    ))?;
                }
            }
        }
        Ok(())
    }
}

/// The `SAVE` command.
pub struct SaveCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
    storage: Rc<RefCell<Storage>>,
    program: Rc<RefCell<dyn Program>>,
}

impl SaveCommand {
    /// Creates a new `SAVE` command that saves the contents of the `program` into `storage`.
    pub fn new(
        console: Rc<RefCell<dyn Console>>,
        storage: Rc<RefCell<Storage>>,
        program: Rc<RefCell<dyn Program>>,
    ) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("SAVE", VarType::Void)
                .with_syntax("[filename$]")
                .with_category(CATEGORY)
                .with_description(
                    "Saves the current program in memory to the given filename.
The filename must be a string and must be a valid EndBASIC path.  The .BAS extension is optional \
but, if present, it must be .BAS.
If no filename is given, SAVE will try to use the filename of the loaded program (if any) and \
will fail if no name has been given yet.
See the \"File system\" help topic for information on the path syntax.",
                )
                .build(),
            console,
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

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        let name = match span.args.as_slice() {
            [] => match self.program.borrow().name() {
                Some(name) => name.to_owned(),
                None => {
                    return Err(CallError::ArgumentError(
                        span.name_pos,
                        "Unnamed program; please provide a filename".to_owned(),
                    ))
                }
            },
            [ArgSpan { expr: Some(expr), sep: ArgSep::End, .. }] => {
                match expr.eval(machine.get_mut_symbols()).await? {
                    Value::Text(t) => add_extension(t)?,
                    _ => {
                        return Err(CallError::ArgumentError(
                            expr.start_pos(),
                            "SAVE requires a string as the filename".to_owned(),
                        ))
                    }
                }
            }
            _ => return Err(CallError::SyntaxError),
        };

        let full_name = self.storage.borrow().make_canonical(&name)?;
        let content = self.program.borrow().text();
        self.storage.borrow_mut().put(&name, &content).await?;
        self.program.borrow_mut().set_name(&full_name);

        self.console.borrow_mut().print(&format!("Saved as {}", full_name))?;

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
    machine.add_command(EditCommand::new(console.clone(), program.clone()));
    machine.add_command(KillCommand::new(storage.clone()));
    machine.add_command(ListCommand::new(console.clone(), program.clone()));
    machine.add_command(LoadCommand::new(console.clone(), storage.clone(), program.clone()));
    machine.add_command(NewCommand::new(console.clone(), program.clone()));
    machine.add_command(RunCommand::new(console.clone(), program.clone()));
    machine.add_command(SaveCommand::new(console, storage, program));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;

    const NO_ANSWERS: &[&str] =
        &["n\n", "N\n", "no\n", "NO\n", "false\n", "FALSE\n", "xyz\n", "\n", "1\n"];

    const YES_ANSWERS: &[&str] = &["y\n", "yes\n", "Y\n", "YES\n", "true\n", "TRUE\n"];

    #[test]
    fn test_kill_ok() {
        for p in &["foo", "foo.bas"] {
            Tester::default()
                .set_program(Some("foo.bas"), "Leave me alone")
                .write_file("bar.bas", "")
                .write_file("foo.bas", "line 1\n  line 2\n")
                .run(format!(r#"KILL "{}""#, p))
                .expect_program(Some("foo.bas"), "Leave me alone")
                .expect_file("MEMORY:/bar.bas", "")
                .check();
        }
    }

    #[test]
    fn test_kill_errors() {
        check_load_save_common_errors("KILL");

        Tester::default()
            .run("KILL")
            .expect_err("1:1: In call to KILL: expected filename$")
            .check();

        check_stmt_err("1:1: In call to KILL: Entry not found", r#"KILL "missing-file""#);

        Tester::default()
            .write_file("mismatched-extension.bat", "")
            .run(r#"KILL "mismatched-extension""#)
            .expect_err("1:1: In call to KILL: Entry not found")
            .expect_file("MEMORY:/mismatched-extension.bat", "")
            .check();
    }

    #[test]
    fn test_edit_ok() {
        Tester::default()
            .set_program(Some("foo.bas"), "previous\n")
            .add_input_chars("new line\n")
            .run("EDIT")
            .expect_program(Some("foo.bas"), "previous\nnew line\n")
            .check();
    }

    #[test]
    fn test_edit_errors() {
        check_stmt_err("1:1: In call to EDIT: expected no arguments", "EDIT 1");
    }

    #[test]
    fn test_list_ok() {
        Tester::default().run("LIST").check();

        Tester::default()
            .set_program(None, "one\n\nthree\n")
            .run("LIST")
            .expect_prints(["one", "", "three"])
            .expect_program(None as Option<&str>, "one\n\nthree\n")
            .check();
    }

    #[test]
    fn test_list_errors() {
        check_stmt_err("1:1: In call to LIST: expected no arguments", "LIST 2");
    }

    #[test]
    fn test_load_ok() {
        let content = "line 1\n\n  line 2\n";
        for (explicit, canonical) in &[
            ("foo", "MEMORY:foo.bas"),
            ("foo.bas", "MEMORY:foo.bas"),
            ("BAR", "MEMORY:BAR.BAS"),
            ("BAR.BAS", "MEMORY:BAR.BAS"),
            ("Baz", "MEMORY:Baz.bas"),
        ] {
            Tester::default()
                .write_file("foo.bas", content)
                .write_file("foo.bak", "")
                .write_file("BAR.BAS", content)
                .write_file("Baz.bas", content)
                .run(format!(r#"LOAD "{}""#, explicit))
                .expect_clear()
                .expect_program(Some(*canonical), "line 1\n\n  line 2\n")
                .expect_file("MEMORY:/foo.bas", content)
                .expect_file("MEMORY:/foo.bak", "")
                .expect_file("MEMORY:/BAR.BAS", content)
                .expect_file("MEMORY:/Baz.bas", content)
                .check();
        }
    }

    #[test]
    fn test_load_dirty_no_name_abort() {
        for answer in NO_ANSWERS {
            Tester::default()
                .add_input_chars("modified unnamed file\n")
                .add_input_chars(answer)
                .write_file("other.bas", "other file\n")
                .run("EDIT: LOAD \"other.bas\"")
                .expect_prints([
                    "Current program has unsaved changes and has never been saved!",
                    "LOAD aborted; use SAVE to save your current changes.",
                ])
                .expect_program(None as Option<&str>, "modified unnamed file\n")
                .expect_file("MEMORY:/other.bas", "other file\n")
                .check();
        }
    }

    #[test]
    fn test_load_dirty_no_name_continue() {
        for answer in YES_ANSWERS {
            Tester::default()
                .add_input_chars("modified unnamed file\n")
                .add_input_chars(answer)
                .write_file("other.bas", "other file\n")
                .run("EDIT: LOAD \"other.bas\"")
                .expect_prints(["Current program has unsaved changes and has never been saved!"])
                .expect_clear()
                .expect_program(Some("MEMORY:other.bas"), "other file\n")
                .expect_file("MEMORY:/other.bas", "other file\n")
                .check();
        }
    }

    #[test]
    fn test_load_dirty_with_name_abort() {
        for answer in NO_ANSWERS {
            Tester::default()
                .add_input_chars("modified named file\n")
                .add_input_chars(answer)
                .write_file("other.bas", "other file\n")
                .set_program(Some("MEMORY:/named.bas"), "previous contents\n")
                .run("EDIT: LOAD \"other.bas\"")
                .expect_prints([
                    "Current program MEMORY:/named.bas has unsaved changes!",
                    "LOAD aborted; use SAVE to save your current changes.",
                ])
                .expect_program(
                    Some("MEMORY:/named.bas"),
                    "previous contents\nmodified named file\n",
                )
                .expect_file("MEMORY:/other.bas", "other file\n")
                .check();
        }
    }

    #[test]
    fn test_load_dirty_with_name_continue() {
        for answer in YES_ANSWERS {
            Tester::default()
                .add_input_chars("modified unnamed file\n")
                .add_input_chars(answer)
                .write_file("other.bas", "other file\n")
                .set_program(Some("MEMORY:/named.bas"), "previous contents\n")
                .run("EDIT: LOAD \"other.bas\"")
                .expect_prints(["Current program MEMORY:/named.bas has unsaved changes!"])
                .expect_clear()
                .expect_program(Some("MEMORY:other.bas"), "other file\n")
                .expect_file("MEMORY:/other.bas", "other file\n")
                .check();
        }
    }

    /// Checks errors that should be handled the same way by `LOAD` and `SAVE`.
    fn check_load_save_common_errors(cmd: &str) {
        Tester::default()
            .run(format!("{} 3", cmd))
            .expect_err(format!(
                "1:1: In call to {}: 1:{}: {} requires a string as the filename",
                cmd,
                cmd.len() + 2,
                cmd
            ))
            .check();

        Tester::default()
            .run(format!(r#"{} "a/b.bas""#, cmd))
            .expect_err(format!("1:1: In call to {}: Too many / separators in path 'a/b.bas'", cmd))
            .check();

        for p in &["foo.bak", "foo.ba", "foo.basic"] {
            Tester::default()
                .run(format!(r#"{} "{}""#, cmd, p))
                .expect_err(format!("1:1: In call to {}: Invalid filename extension", cmd))
                .check();
        }
    }

    #[test]
    fn test_load_errors() {
        check_load_save_common_errors("LOAD");

        Tester::default()
            .run("LOAD")
            .expect_err("1:1: In call to LOAD: expected filename$")
            .check();

        check_stmt_err("1:1: In call to LOAD: Entry not found", r#"LOAD "missing-file""#);

        Tester::default()
            .write_file("mismatched-extension.bat", "")
            .run(r#"LOAD "mismatched-extension""#)
            .expect_err("1:1: In call to LOAD: Entry not found")
            .expect_file("MEMORY:/mismatched-extension.bat", "")
            .check();
    }

    #[test]
    fn test_new_nothing() {
        Tester::default().run("NEW").expect_clear().check();
    }

    #[test]
    fn test_new_clears_program_and_variables() {
        Tester::default()
            .set_program(Some("previous.bas"), "some stuff")
            .run("a = 3: NEW")
            .expect_clear()
            .check();
    }

    #[test]
    fn test_new_dirty_no_name_abort() {
        for answer in NO_ANSWERS {
            Tester::default()
                .add_input_chars("modified unnamed file\n")
                .add_input_chars(answer)
                .run("EDIT: NEW")
                .expect_prints([
                    "Current program has unsaved changes and has never been saved!",
                    "NEW aborted; use SAVE to save your current changes.",
                ])
                .expect_program(None as Option<&str>, "modified unnamed file\n")
                .check();
        }
    }

    #[test]
    fn test_new_dirty_no_name_continue() {
        for answer in YES_ANSWERS {
            Tester::default()
                .add_input_chars("modified unnamed file\n")
                .add_input_chars(answer)
                .run("EDIT: NEW")
                .expect_prints(["Current program has unsaved changes and has never been saved!"])
                .expect_clear()
                .check();
        }
    }

    #[test]
    fn test_new_dirty_with_name_abort() {
        for answer in NO_ANSWERS {
            Tester::default()
                .add_input_chars("modified named file\n")
                .add_input_chars(answer)
                .set_program(Some("MEMORY:/named.bas"), "previous contents\n")
                .run("EDIT: NEW")
                .expect_prints([
                    "Current program MEMORY:/named.bas has unsaved changes!",
                    "NEW aborted; use SAVE to save your current changes.",
                ])
                .expect_program(
                    Some("MEMORY:/named.bas"),
                    "previous contents\nmodified named file\n",
                )
                .check();
        }
    }

    #[test]
    fn test_new_dirty_with_name_continue() {
        for answer in YES_ANSWERS {
            Tester::default()
                .add_input_chars("modified named file\n")
                .add_input_chars(answer)
                .set_program(Some("MEMORY:/named.bas"), "previous contents\n")
                .run("EDIT: NEW")
                .expect_prints(["Current program MEMORY:/named.bas has unsaved changes!"])
                .expect_clear()
                .check();
        }
    }

    #[test]
    fn test_new_errors() {
        check_stmt_err("1:1: In call to NEW: expected no arguments", "NEW 10");
    }

    #[test]
    fn test_run_nothing() {
        Tester::default().run("RUN").expect_clear().check();
    }

    #[test]
    fn test_run_clears_before_execution_only() {
        let program = "DIM a(1) AS INTEGER: a(0) = 123";
        let mut t = Tester::default().set_program(Some("untouched.bas"), program);
        t.run("DIM a(1) AS STRING: RUN")
            .expect_array_simple("a", VarType::Integer, vec![123.into()])
            .expect_clear()
            .expect_program(Some("untouched.bas"), program)
            .check();
        t.run("RUN")
            .expect_array_simple("a", VarType::Integer, vec![123.into()])
            .expect_clear()
            .expect_clear()
            .expect_program(Some("untouched.bas"), program)
            .check();
    }

    #[test]
    fn test_run_something_that_exits() {
        let program = "PRINT 5: EXIT 1: PRINT 4";
        Tester::default()
            .set_program(Some("untouched.bas"), program)
            .run(r#"RUN: PRINT "after""#)
            .expect_clear()
            .expect_prints(["5", "Program exited with code 1", "after"])
            .expect_program(Some("untouched.bas"), program)
            .check();
    }

    #[test]
    fn test_run_errors() {
        check_stmt_err("1:1: In call to RUN: expected no arguments", "RUN 10");
    }

    #[test]
    fn test_save_ok_explicit_name() {
        let content = "\n some line   \n ";
        for (explicit, actual, canonical) in &[
            ("first", "MEMORY:/first.bas", "MEMORY:first.bas"),
            ("second.bas", "MEMORY:/second.bas", "MEMORY:second.bas"),
            ("THIRD", "MEMORY:/THIRD.BAS", "MEMORY:THIRD.BAS"),
            ("FOURTH.BAS", "MEMORY:/FOURTH.BAS", "MEMORY:FOURTH.BAS"),
            ("Fifth", "MEMORY:/Fifth.bas", "MEMORY:Fifth.bas"),
        ] {
            Tester::default()
                .set_program(Some("before.bas"), content)
                .run(format!(r#"SAVE "{}""#, explicit))
                .expect_program(Some(*canonical), content)
                .expect_prints([format!("Saved as {}", canonical)])
                .expect_file(*actual, content)
                .check();
        }
    }

    #[test]
    fn test_save_reuse_name() {
        Tester::default()
            .set_program(Some("loaded.bas"), "content\n")
            .run("SAVE")
            .expect_program(Some("MEMORY:loaded.bas"), "content\n")
            .expect_prints(["Saved as MEMORY:loaded.bas"])
            .expect_file("MEMORY:/loaded.bas", "content\n")
            .check();
    }

    #[test]
    fn test_save_unnamed_error() {
        Tester::default()
            .add_input_chars("modified file\n")
            .run("EDIT: SAVE")
            .expect_program(None as Option<&str>, "modified file\n")
            .expect_err("1:7: In call to SAVE: 1:7: Unnamed program; please provide a filename")
            .check();
    }

    #[test]
    fn test_save_errors() {
        check_load_save_common_errors("SAVE");
    }
}
