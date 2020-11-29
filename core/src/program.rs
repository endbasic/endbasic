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
use crate::editor::Editor;
use crate::exec::{self, BuiltinCommand, Machine};
use async_trait::async_trait;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::io;
use std::path::PathBuf;
use std::rc::Rc;

/// Metadata of an entry in the store.
#[derive(Debug, Eq, PartialEq)]
pub struct Metadata {
    /// Last modification time of the entry.
    pub date: time::OffsetDateTime,

    /// Total size of the entry.
    pub length: u64,
}

/// Abstract operations to load and store programs on persistent storage.
pub trait Store {
    /// Deletes the program given by `name`.
    fn delete(&mut self, name: &str) -> io::Result<()>;

    /// Returns a sorted list of the entries in the store and their metadata.
    fn enumerate(&self) -> io::Result<BTreeMap<String, Metadata>>;

    /// Loads the contents of the program given by `name`.
    fn get(&self, name: &str) -> io::Result<String>;

    /// Saves the in-memory program given by `content` into `name`.
    fn put(&mut self, name: &str, content: &str) -> io::Result<()>;
}

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

/// Computes the path to a source file given the `dir` where it lives and a `basename`.
fn to_filename<S: Into<PathBuf>>(basename: S) -> io::Result<String> {
    let mut basename = basename.into();

    if basename.components().fold(0, |count, _| count + 1) != 1 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "Filename must be a single path component",
        ));
    }

    if let Some(ext) = basename.extension() {
        if ext != "bas" && ext != "BAS" {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "Invalid filename extension"));
        }
    } else {
        // Attempt to determine a sensible extension based on the case of the basename, assuming
        // that an all-uppercase basename wants an all-uppercase extension.  This is fragile on
        // case-sensitive file systems, but there is not a lot we can do.
        let mut ext = "BAS";
        for ch in basename.to_string_lossy().chars() {
            if ch.is_ascii_lowercase() {
                ext = "bas";
                break;
            }
        }
        basename.set_extension(ext);
    }
    Ok(basename.to_str().expect("Path came from a String").to_owned())
}

/// Shows the contents of directory `path`.
fn show_dir(store: &dyn Store, console: &mut dyn Console) -> io::Result<()> {
    let entries = store.enumerate()?;

    console.print("")?;
    console.print("    Modified              Size    Name")?;
    let mut total_files = 0;
    let mut total_bytes = 0;
    for (name, details) in entries {
        console.print(&format!(
            "    {}    {:6}    {}",
            details.date.format("%F %H:%M"),
            details.length,
            name,
        ))?;
        total_files += 1;
        total_bytes += details.length;
    }
    if total_files > 0 {
        console.print("")?;
    }
    console.print(&format!("    {} file(s), {} bytes", total_files, total_bytes))?;
    console.print("")?;
    Ok(())
}

/// The `DEL` command.
struct DelCommand {
    store: Rc<RefCell<dyn Store>>,
}

#[async_trait(?Send)]
impl BuiltinCommand for DelCommand {
    fn name(&self) -> &'static str {
        "DEL"
    }

    fn category(&self) -> &'static str {
        "Stored program manipulation"
    }

    fn syntax(&self) -> &'static str {
        "filename"
    }

    fn description(&self) -> &'static str {
        "Deletes the given program.
The filename must be a string and must be a basename (no directory components).  The .BAS \
extension is optional, but if present, it must be .BAS."
    }

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        machine: &mut Machine,
    ) -> exec::Result<()> {
        if args.len() != 1 {
            return exec::new_usage_error("DEL requires a filename");
        }
        let arg0 = args[0].0.as_ref().expect("Single argument must be present");
        match arg0.eval(machine.get_vars())? {
            Value::Text(t) => {
                let name = to_filename(t)?;
                self.store.borrow_mut().delete(&name)?;
            }
            _ => return exec::new_usage_error("DEL requires a string as the filename"),
        }
        Ok(())
    }
}

/// The `DIR` command.
struct DirCommand {
    console: Rc<RefCell<dyn Console>>,
    store: Rc<RefCell<dyn Store>>,
}

#[async_trait(?Send)]
impl BuiltinCommand for DirCommand {
    fn name(&self) -> &'static str {
        "DIR"
    }

    fn category(&self) -> &'static str {
        "Stored program manipulation"
    }

    fn syntax(&self) -> &'static str {
        ""
    }

    fn description(&self) -> &'static str {
        "Displays the list of files on disk."
    }

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        _machine: &mut Machine,
    ) -> exec::Result<()> {
        if !args.is_empty() {
            return exec::new_usage_error("DIR takes no arguments");
        }
        show_dir(&*self.store.borrow(), &mut *self.console.borrow_mut())?;
        Ok(())
    }
}

/// The `EDIT` command.
struct EditCommand {
    console: Rc<RefCell<dyn Console>>,
    program: Rc<RefCell<dyn Program>>,
}

#[async_trait(?Send)]
impl BuiltinCommand for EditCommand {
    fn name(&self) -> &'static str {
        "EDIT"
    }

    fn category(&self) -> &'static str {
        "Stored program manipulation"
    }

    fn syntax(&self) -> &'static str {
        "[lineno%]"
    }

    fn description(&self) -> &'static str {
        "Interactively edits the stored program."
    }

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        _machine: &mut Machine,
    ) -> exec::Result<()> {
        if !args.is_empty() {
            return exec::new_usage_error("EDIT takes no arguments");
        }

        let mut console = self.console.borrow_mut();
        let mut program = self.program.borrow_mut();
        program.edit(&mut *console).await?;
        Ok(())
    }
}

/// The `LOAD` command.
struct LoadCommand {
    store: Rc<RefCell<dyn Store>>,
    program: Rc<RefCell<dyn Program>>,
}

#[async_trait(?Send)]
impl BuiltinCommand for LoadCommand {
    fn name(&self) -> &'static str {
        "LOAD"
    }

    fn category(&self) -> &'static str {
        "Stored program manipulation"
    }

    fn syntax(&self) -> &'static str {
        "filename"
    }

    fn description(&self) -> &'static str {
        "Loads the given program.
The filename must be a string and must be a basename (no directory components).  The .BAS \
extension is optional, but if present, it must be .BAS."
    }

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        machine: &mut Machine,
    ) -> exec::Result<()> {
        if args.len() != 1 {
            return exec::new_usage_error("LOAD requires a filename");
        }
        let arg0 = args[0].0.as_ref().expect("Single argument must be present");
        match arg0.eval(machine.get_vars())? {
            Value::Text(t) => {
                let name = to_filename(t)?;
                let content = self.store.borrow().get(&name)?;
                self.program.borrow_mut().load(&content);
                machine.clear();
            }
            _ => return exec::new_usage_error("LOAD requires a string as the filename"),
        }
        Ok(())
    }
}

/// The `NEW` command.
struct NewCommand {
    program: Rc<RefCell<dyn Program>>,
}

#[async_trait(?Send)]
impl BuiltinCommand for NewCommand {
    fn name(&self) -> &'static str {
        "NEW"
    }

    fn category(&self) -> &'static str {
        "Stored program manipulation"
    }

    fn syntax(&self) -> &'static str {
        ""
    }

    fn description(&self) -> &'static str {
        "Clears the stored program from memory."
    }

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        machine: &mut Machine,
    ) -> exec::Result<()> {
        if !args.is_empty() {
            return exec::new_usage_error("NEW takes no arguments");
        }
        self.program.borrow_mut().load("");
        machine.clear();
        Ok(())
    }
}

/// The `RUN` command.
struct RunCommand {
    program: Rc<RefCell<dyn Program>>,
}

#[async_trait(?Send)]
impl BuiltinCommand for RunCommand {
    fn name(&self) -> &'static str {
        "RUN"
    }

    fn category(&self) -> &'static str {
        "Stored program manipulation"
    }

    fn syntax(&self) -> &'static str {
        ""
    }

    fn description(&self) -> &'static str {
        "Runs the stored program.
Note that the program runs in the context of the interpreter so it will pick up any variables \
and other state that may already be set."
    }

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        machine: &mut Machine,
    ) -> exec::Result<()> {
        if !args.is_empty() {
            return exec::new_usage_error("RUN takes no arguments");
        }
        let program = self.program.borrow().text();
        machine.exec(&mut program.as_bytes()).await
    }
}

/// The `SAVE` command.
struct SaveCommand {
    store: Rc<RefCell<dyn Store>>,
    program: Rc<RefCell<dyn Program>>,
}

#[async_trait(?Send)]
impl BuiltinCommand for SaveCommand {
    fn name(&self) -> &'static str {
        "SAVE"
    }

    fn category(&self) -> &'static str {
        "Stored program manipulation"
    }

    fn syntax(&self) -> &'static str {
        "filename"
    }

    fn description(&self) -> &'static str {
        "Saves the current program in memory to the given filename.
The filename must be a string and must be a basename (no directory components).  The .BAS \
extension is optional, but if present, it must be .BAS."
    }

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        machine: &mut Machine,
    ) -> exec::Result<()> {
        if args.len() != 1 {
            return exec::new_usage_error("SAVE requires a filename");
        }
        let arg0 = args[0].0.as_ref().expect("Single argument must be present");
        match arg0.eval(machine.get_vars())? {
            Value::Text(t) => {
                let name = to_filename(t)?;
                let content = self.program.borrow().text();
                self.store.borrow_mut().put(&name, &content)?;
            }
            _ => return exec::new_usage_error("SAVE requires a string as the filename"),
        }
        Ok(())
    }
}

/// Instantiates all program editing commands against the stored `program`, using `console` for
/// interactive editing, and using `dir` as the on-disk storage for the programs.
fn all_commands_for(
    program: Rc<RefCell<dyn Program>>,
    console: Rc<RefCell<dyn Console>>,
    store: Rc<RefCell<dyn Store>>,
) -> Vec<Rc<dyn BuiltinCommand>> {
    vec![
        Rc::from(DelCommand { store: store.clone() }),
        Rc::from(DirCommand { console: console.clone(), store: store.clone() }),
        Rc::from(EditCommand { console: console.clone(), program: program.clone() }),
        Rc::from(LoadCommand { store: store.clone(), program: program.clone() }),
        Rc::from(NewCommand { program: program.clone() }),
        Rc::from(RunCommand { program: program.clone() }),
        Rc::from(SaveCommand { store: store.clone(), program }),
    ]
}

/// Instantiates all program editing commands against a new (empty) program, using `console` for
/// interactive editing, and using `dir` as the on-disk storage for the programs.
pub fn all_commands(
    console: Rc<RefCell<dyn Console>>,
    store: Rc<RefCell<dyn Store>>,
) -> Vec<Rc<dyn BuiltinCommand>> {
    all_commands_for(Rc::from(RefCell::from(Editor::new())), console, store)
}

#[cfg(test)]
mod testutils {
    use super::*;
    use crate::console;
    use std::collections::HashMap;

    #[derive(Default)]
    pub(crate) struct InMemoryStore {
        programs: HashMap<String, String>,
    }

    impl Store for InMemoryStore {
        fn delete(&mut self, name: &str) -> io::Result<()> {
            match self.programs.remove(name) {
                Some(_) => Ok(()),
                None => Err(io::Error::new(io::ErrorKind::NotFound, "Entry not found")),
            }
        }

        fn enumerate(&self) -> io::Result<BTreeMap<String, Metadata>> {
            let date = time::OffsetDateTime::from_unix_timestamp(1_588_757_875);

            let mut entries = BTreeMap::new();
            for (name, contents) in &self.programs {
                entries.insert(name.clone(), Metadata { date, length: contents.len() as u64 });
            }
            Ok(entries)
        }

        fn get(&self, name: &str) -> io::Result<String> {
            match self.programs.get(name) {
                Some(content) => Ok(content.to_owned()),
                None => Err(io::Error::new(io::ErrorKind::NotFound, "Entry not found")),
            }
        }

        fn put(&mut self, name: &str, content: &str) -> io::Result<()> {
            self.programs.insert(name.to_owned(), content.to_owned());
            Ok(())
        }
    }

    pub(crate) struct RecordedProgram {
        content: String,
    }

    impl RecordedProgram {
        pub fn new(content: &'static str) -> Self {
            Self { content: content.to_owned() }
        }
    }

    #[async_trait(?Send)]
    impl Program for RecordedProgram {
        async fn edit(&mut self, console: &mut dyn Console) -> io::Result<()> {
            let append = console::read_line(console, "", "").await?;
            self.content.push_str(&append);
            self.content.push('\n');
            Ok(())
        }

        fn load(&mut self, text: &str) {
            self.content = text.to_owned();
        }

        fn text(&self) -> String {
            self.content.clone()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::testutils::*;
    use super::*;
    use crate::console::testutils::*;
    use crate::exec::testutils::*;
    use crate::exec::MachineBuilder;
    use futures_lite::future::block_on;

    /// Runs the `input` code on a new machine that stores programs in `store` and verifies its
    /// output.
    ///
    /// `golden_in` is a sequence of keys to feed to the commands that request console input.
    ///
    /// `expected_out` is a sequence of expected calls to `PRINT`.
    ///
    /// `exp_program` is the expected state of `program` after execution.
    fn do_ok_test_with_store(
        program: Rc<RefCell<dyn Program>>,
        store: Rc<RefCell<dyn Store>>,
        input: &str,
        golden_in: &'static str,
        expected_out: &'static [&'static str],
        exp_program: &'static str,
    ) {
        let console =
            Rc::from(RefCell::from(MockConsoleBuilder::new().add_input_chars(golden_in).build()));
        let mut machine = MachineBuilder::default()
            .add_builtins(all_commands_for(program.clone(), console.clone(), store))
            .build();
        block_on(machine.exec(&mut input.as_bytes())).expect("Execution failed");
        let expected_out: Vec<CapturedOut> =
            expected_out.iter().map(|x| CapturedOut::Print((*x).to_owned())).collect();
        assert_eq!(expected_out, console.borrow().captured_out());
        assert_eq!(exp_program, program.borrow().text());
    }

    /// Same as `do_ok_test_with_store` but with an automatic `store`.
    fn do_ok_test(
        program: Rc<RefCell<dyn Program>>,
        input: &str,
        golden_in: &'static str,
        expected_out: &'static [&'static str],
        exp_program: &'static str,
    ) {
        let store = Rc::from(RefCell::from(InMemoryStore::default()));
        do_ok_test_with_store(program, store, input, golden_in, expected_out, exp_program)
    }

    /// Runs the `input` code on a new machine and verifies that it fails with `expected_err`.
    ///
    /// Ensures that this does not touch the console.
    fn do_error_test_with_store(store: Rc<RefCell<dyn Store>>, input: &str, expected_err: &str) {
        let console = Rc::from(RefCell::from(MockConsoleBuilder::new().build()));
        let program = Rc::from(RefCell::from(RecordedProgram::new("")));
        let mut machine = MachineBuilder::default()
            .add_builtins(all_commands_for(program, console.clone(), store))
            .build();
        assert_eq!(
            expected_err,
            format!(
                "{}",
                block_on(machine.exec(&mut input.as_bytes())).expect_err("Execution did not fail")
            )
        );
        assert!(console.borrow().captured_out().is_empty());
    }

    /// Same as `do_error_test_with_store` but with an automatic (and inaccessible) `dir`.
    fn do_error_test(input: &str, expected_err: &str) {
        let store = Rc::from(RefCell::from(InMemoryStore::default()));
        do_error_test_with_store(store, input, expected_err)
    }

    #[test]
    fn test_del_ok() {
        let mut store = InMemoryStore::default();
        store.put("bar.bas", "").unwrap();
        let store = Rc::from(RefCell::from(store));

        let program = Rc::from(RefCell::from(RecordedProgram::new("Leave me alone")));

        for p in &["foo", "foo.bas"] {
            store.borrow_mut().put("foo.bas", "line 1\n  line 2\n").unwrap();
            do_ok_test_with_store(
                program.clone(),
                store.clone(),
                &("DEL \"".to_owned() + p + "\""),
                "",
                &[],
                "Leave me alone",
            );
        }

        store.borrow().get("bar.bas").unwrap(); // Check that unrelated entries were not touched.
    }

    #[test]
    fn test_del_errors() {
        let store = Rc::from(RefCell::from(InMemoryStore::default()));
        check_load_save_common_errors("DEL", store.clone());

        do_error_test_with_store(store.clone(), "DEL \"missing-file\"", "Entry not found");

        store.borrow_mut().put("mismatched-extension.bat", "").unwrap();
        do_error_test_with_store(store, "DEL \"mismatched-extension\"", "Entry not found");
    }

    #[test]
    fn test_dir_empty() {
        let store = Rc::from(RefCell::from(InMemoryStore::default()));
        do_ok_test_with_store(
            Rc::from(RefCell::from(RecordedProgram::new(""))),
            store,
            "DIR",
            "",
            &["", "    Modified              Size    Name", "    0 file(s), 0 bytes", ""],
            "",
        );
    }

    #[test]
    fn test_dir_entries_are_sorted() {
        let mut store = InMemoryStore::default();
        store.put("empty.bas", "").unwrap();
        store.put("some other file.bas", "not empty\n").unwrap();
        store.put("00AAA.BAS", "first\nfile\n").unwrap();
        store.put("not a bas.txt", "").unwrap();
        let store = Rc::from(RefCell::from(store));

        do_ok_test_with_store(
            Rc::from(RefCell::from(RecordedProgram::new(""))),
            store,
            "DIR",
            "",
            &[
                "",
                "    Modified              Size    Name",
                "    2020-05-06 09:37        11    00AAA.BAS",
                "    2020-05-06 09:37         0    empty.bas",
                "    2020-05-06 09:37         0    not a bas.txt",
                "    2020-05-06 09:37        10    some other file.bas",
                "",
                "    4 file(s), 21 bytes",
                "",
            ],
            "",
        );
    }

    #[test]
    fn test_dir_errors() {
        let store = Rc::from(RefCell::from(InMemoryStore::default()));
        do_error_test_with_store(store, "DIR 2", "DIR takes no arguments");
    }

    #[test]
    fn test_edit_ok() {
        do_ok_test(
            Rc::from(RefCell::from(RecordedProgram::new("previous\n"))),
            "EDIT",
            "new line\n",
            &[],
            "previous\nnew line\n",
        );
    }

    #[test]
    fn test_edit_errors() {
        do_error_test("EDIT 1", "EDIT takes no arguments");
    }

    #[test]
    fn test_load_ok() {
        let mut store = InMemoryStore::default();
        store.put("foo.bas", "line 1\n\n  line 2\n").unwrap();
        store.put("foo.bak", "").unwrap();
        store.put("BAR.BAS", "line 1\n\n  line 2\n").unwrap();
        store.put("Baz.bas", "line 1\n\n  line 2\n").unwrap();
        let store = Rc::from(RefCell::from(store));

        for p in &["foo", "foo.bas", "BAR", "BAR.BAS", "Baz"] {
            do_ok_test_with_store(
                Rc::from(RefCell::from(RecordedProgram::new(""))),
                store.clone(),
                &("LOAD \"".to_owned() + p + "\""),
                "",
                &[],
                "line 1\n\n  line 2\n",
            );
        }
    }

    /// Checks errors that should be handled the same way by `LOAD` and `SAVE`.
    fn check_load_save_common_errors(cmd: &str, store: Rc<RefCell<dyn Store>>) {
        do_error_test_with_store(store.clone(), &cmd, &format!("{} requires a filename", cmd));
        do_error_test_with_store(
            store.clone(),
            &format!("{} 3", cmd),
            &format!("{} requires a string as the filename", cmd),
        );

        let mut non_basenames = vec!["./foo.bas", "a/b.bas", "a/b"];
        if cfg!(target_os = "windows") {
            non_basenames.push("c:foo.bas");
        }
        for p in non_basenames.as_slice() {
            do_error_test_with_store(
                store.clone(),
                &format!("{} \"{}\"", cmd, p),
                "Filename must be a single path component",
            );
        }

        for p in &["foo.bak", "foo.ba", "foo.basic"] {
            do_error_test_with_store(
                store.clone(),
                &format!("{} \"{}\"", cmd, p),
                "Invalid filename extension",
            );
        }
    }

    #[test]
    fn test_load_errors() {
        let store = Rc::from(RefCell::from(InMemoryStore::default()));
        check_load_save_common_errors("LOAD", store.clone());

        do_error_test_with_store(store.clone(), "LOAD \"missing-file\"", "Entry not found");

        store.borrow_mut().put("mismatched-extension.bat", "").unwrap();
        do_error_test_with_store(store, "LOAD \"mismatched-extension\"", "Entry not found");
    }

    #[test]
    fn test_new_nothing() {
        do_ok_test(Rc::from(RefCell::from(RecordedProgram::new(""))), "NEW", "", &[], "");
    }

    #[test]
    fn test_new_clears_program_and_variables() {
        let program = Rc::from(RefCell::from(RecordedProgram::new("some stuff")));

        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(NewCommand { program: program.clone() }))
            .build();

        block_on(machine.exec(&mut b"NEW".as_ref())).unwrap();
        assert!(program.borrow().text().is_empty());
        assert!(machine.get_vars().is_empty());
    }

    #[test]
    fn test_new_errors() {
        do_error_test("NEW 10", "NEW takes no arguments");
    }

    #[test]
    fn test_run_nothing() {
        do_ok_test(Rc::from(RefCell::from(RecordedProgram::new(""))), "RUN", "", &[], "");
    }

    #[test]
    fn test_run_something_that_shares_state() {
        let program = Rc::from(RefCell::from(RecordedProgram::new("OUT var\nvar = var + 1")));

        let captured_out = Rc::from(RefCell::from(vec![]));
        let out_cmd = OutCommand::from(captured_out.clone());
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(out_cmd))
            .add_builtin(Rc::from(RunCommand { program }))
            .build();

        block_on(machine.exec(&mut b"var = 7: RUN".as_ref())).unwrap();
        assert_eq!(&["7"], captured_out.borrow().as_slice());

        captured_out.borrow_mut().clear();
        block_on(machine.exec(&mut b"RUN".as_ref())).unwrap();
        assert_eq!(&["8"], captured_out.borrow().as_slice());
    }

    #[test]
    fn test_run_errors() {
        do_error_test("RUN 10", "RUN takes no arguments");
    }

    #[test]
    fn test_save_ok() {
        let store = Rc::from(RefCell::from(InMemoryStore::default()));

        let program = Rc::from(RefCell::from(RecordedProgram::new("line 1\n  line 2\n")));

        for p in &["first", "second.bas", "THIRD", "FOURTH.BAS", "Fifth"] {
            do_ok_test_with_store(
                program.clone(),
                store.clone(),
                &("SAVE \"".to_owned() + p + "\""),
                "",
                &[],
                "line 1\n  line 2\n",
            );
        }

        for p in &["first.bas", "second.bas", "THIRD.BAS", "FOURTH.BAS", "Fifth.bas"] {
            let content = store.borrow().get(p).unwrap();
            assert_eq!(content, "line 1\n  line 2\n");
        }
    }

    #[test]
    fn test_save_errors() {
        let store = Rc::from(RefCell::from(InMemoryStore::default()));
        check_load_save_common_errors("SAVE", store);
    }
}
