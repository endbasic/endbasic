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
use async_trait::async_trait;
use failure::Fallible;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufRead, Write};
use std::path::{Path, PathBuf};
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

/// Computes the path to a source file given the `dir` where it lives and a `basename`.
fn to_filename(dir: &Path, basename: &str) -> Fallible<PathBuf> {
    let mut basename = PathBuf::from(basename);

    ensure!(
        basename.components().fold(0, |count, _| count + 1) == 1,
        "Filename must be a single path component"
    );

    if let Some(ext) = basename.extension() {
        if ext != "bas" && ext != "BAS" {
            bail!("Invalid filename extension");
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
    Ok(dir.join(basename))
}

/// Directory entry after processing all of its data.
struct Entry {
    file_type: fs::FileType,
    date: time::OffsetDateTime,
    len: u64,
}

/// Fully scans a directory, returning a sorted collection of processed `Entry`s.
fn do_read_dir(path: &Path) -> io::Result<BTreeMap<String, Entry>> {
    let mut entries = BTreeMap::default();
    match fs::read_dir(&path) {
        Ok(dirents) => {
            for de in dirents {
                let de = de?;

                let file_type = de.file_type()?;

                // TODO(jmmv): This follows symlinks for cross-platform simplicity, but it is ugly.
                // I don't expect symlinks in the programs directory anyway.
                let metadata = fs::metadata(de.path())?;
                let date = time::OffsetDateTime::from(metadata.modified()?)
                    .to_offset(time::UtcOffset::current_local_offset());
                let len = metadata.len();

                entries.insert(
                    de.file_name().to_string_lossy().to_string(),
                    Entry { file_type, date, len },
                );
            }
        }
        Err(e) => {
            if e.kind() != io::ErrorKind::NotFound {
                return Err(e);
            }
        }
    }
    Ok(entries)
}

/// Shows the contents of directory `path`.
fn show_dir(path: &Path, console: &mut dyn Console) -> io::Result<()> {
    let entries = do_read_dir(path)?;

    console.print("")?;
    console.print("    Modified            Type       Size    Name")?;
    let mut total_files = 0;
    let mut total_bytes = 0;
    for (name, details) in entries {
        let type_name = {
            if details.file_type.is_dir() {
                continue; // LOAD/SAVE don't support directories so skip them.
            } else if details.file_type.is_file() {
                "     "
            } else if details.file_type.is_symlink() {
                "<LNK>"
            } else {
                "<UKN>"
            }
        };

        console.print(&format!(
            "    {}    {}    {:6}    {}",
            details.date.format("%F %H:%M"),
            type_name,
            details.len,
            name,
        ))?;
        total_files += 1;
        total_bytes += details.len;
    }
    if total_files > 0 {
        console.print("")?;
    }
    console.print(&format!("    {} file(s), {} bytes", total_files, total_bytes))?;
    console.print("")?;
    Ok(())
}

/// Loads the contents of the program given by `path`.
fn load_program(path: &Path) -> io::Result<BTreeMap<usize, String>> {
    let input = File::open(path)?;
    let reader = io::BufReader::new(input);
    let mut n = 10;
    let mut program = BTreeMap::new();
    for line in reader.lines() {
        let line = line?;
        // TODO(jmmv): Support empty lines in editor.
        if !line.is_empty() {
            program.insert(n, line);
            n += 10;
        }
    }
    Ok(program)
}

/// Saves the in-memory program given by `lines` into `path`.
fn save_program(lines: &BTreeMap<usize, String>, path: &Path) -> io::Result<()> {
    let dir = path.parent().expect("Must be a filename with a directory");
    fs::create_dir_all(&dir)?;

    // TODO(jmmv): Should back up existing files.
    let output = OpenOptions::new().create(true).write(true).truncate(true).open(path)?;
    let mut writer = io::BufWriter::new(output);
    for l in lines.values() {
        writer.write_all(l.as_bytes())?;
        writer.write_all(b"\n")?;
    }
    Ok(())
}

/// The `DIR` command.
struct DirCommand {
    console: Rc<RefCell<dyn Console>>,
    dir: PathBuf,
}

#[async_trait(?Send)]
impl BuiltinCommand for DirCommand {
    fn name(&self) -> &'static str {
        "DIR"
    }

    fn syntax(&self) -> &'static str {
        ""
    }

    fn description(&self) -> &'static str {
        "Displays the list of files on disk."
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], _machine: &mut Machine) -> Fallible<()> {
        ensure!(args.is_empty(), "DIR takes no arguments");
        show_dir(&self.dir, &mut *self.console.borrow_mut())?;
        Ok(())
    }
}

/// The `EDIT` command.
struct EditCommand {
    console: Rc<RefCell<dyn Console>>,
    program: Program,
}

#[async_trait(?Send)]
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

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
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

#[async_trait(?Send)]
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

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], _machine: &mut Machine) -> Fallible<()> {
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

/// The `LOAD` command.
struct LoadCommand {
    dir: PathBuf,
    program: Program,
}

#[async_trait(?Send)]
impl BuiltinCommand for LoadCommand {
    fn name(&self) -> &'static str {
        "LOAD"
    }

    fn syntax(&self) -> &'static str {
        "filename"
    }

    fn description(&self) -> &'static str {
        "Loads the given program.
The filename must be a string and must be a basename (no directory components).  The .BAS \
extension is optional, but if present, it must be .BAS."
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
        ensure!(args.len() == 1, "LOAD requires a filename");
        let arg0 = args[0].0.as_ref().expect("Single argument must be present");
        match arg0.eval(machine.get_vars())? {
            Value::Text(t) => {
                let path = to_filename(&self.dir, &t)?;
                *self.program.borrow_mut() = load_program(&path)?;
                machine.clear();
            }
            _ => bail!("LOAD requires a string as the filename"),
        }
        Ok(())
    }
}

/// The `NEW` command.
struct NewCommand {
    program: Program,
}

#[async_trait(?Send)]
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

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
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

#[async_trait(?Send)]
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

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], _machine: &mut Machine) -> Fallible<()> {
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

#[async_trait(?Send)]
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

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
        ensure!(args.is_empty(), "RUN takes no arguments");
        let program = self.program.borrow();
        let mut text = String::new();
        for (_, v) in program.iter() {
            text += v;
            text += "\n";
        }
        machine.exec_async(&mut text.as_bytes()).await
    }
}

/// The `SAVE` command.
struct SaveCommand {
    dir: PathBuf,
    program: Program,
}

#[async_trait(?Send)]
impl BuiltinCommand for SaveCommand {
    fn name(&self) -> &'static str {
        "SAVE"
    }

    fn syntax(&self) -> &'static str {
        "filename"
    }

    fn description(&self) -> &'static str {
        "Saves the current program in memory to the given filename.
The filename must be a string and must be a basename (no directory components).  The .BAS \
extension is optional, but if present, it must be .BAS."
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
        ensure!(args.len() == 1, "SAVE requires a filename");
        let arg0 = args[0].0.as_ref().expect("Single argument must be present");
        match arg0.eval(machine.get_vars())? {
            Value::Text(t) => {
                let path = to_filename(&self.dir, &t)?;
                save_program(&self.program.borrow(), &path)?;
            }
            _ => bail!("SAVE requires a string as the filename"),
        }
        Ok(())
    }
}

/// Instantiates all program editing commands against the stored `program`, using `console` for
/// interactive editing, and using `dir` as the on-disk storage for the programs.
fn all_commands_for(
    program: Program,
    console: Rc<RefCell<dyn Console>>,
    dir: &Path,
) -> Vec<Rc<dyn BuiltinCommand>> {
    vec![
        Rc::from(DirCommand { console: console.clone(), dir: dir.to_owned() }),
        Rc::from(EditCommand { console: console.clone(), program: program.clone() }),
        Rc::from(ListCommand { console: console.clone(), program: program.clone() }),
        Rc::from(LoadCommand { dir: dir.to_owned(), program: program.clone() }),
        Rc::from(NewCommand { program: program.clone() }),
        Rc::from(RenumCommand { program: program.clone() }),
        Rc::from(RunCommand { program: program.clone() }),
        Rc::from(SaveCommand { dir: dir.to_owned(), program: program }),
    ]
}

/// Instantiates all program editing commands against a new (empty) program, using `console` for
/// interactive editing, and using `dir` as the on-disk storage for the programs.
pub fn all_commands(console: Rc<RefCell<dyn Console>>, dir: &Path) -> Vec<Rc<dyn BuiltinCommand>> {
    all_commands_for(Program::default(), console, dir)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::console::testutils::*;
    use crate::exec::testutils::*;
    use crate::exec::MachineBuilder;

    /// Runs the `input` code on a new machine that stores programs in `dir` and verifies its
    /// output.
    ///
    /// `golden_in` is a sequence of pairs each containing an expected prompt printed by `INPUT`
    /// and the reply to feed to that prompt.
    ///
    /// `expected_out` is a sequence of expected calls to `PRINT`.
    ///
    /// `exp_program` is the expected state of `program` after execution, as a collection of line
    /// number and content pairs.
    fn do_ok_test_with_dir(
        program: Program,
        dir: &Path,
        input: &str,
        golden_in: &'static [(&'static str, &'static str, &'static str)],
        expected_out: &'static [&'static str],
        exp_program: &'static [(usize, &'static str)],
    ) {
        let console = Rc::from(RefCell::from(MockConsole::new(golden_in)));
        let mut machine = MachineBuilder::default()
            .add_builtins(all_commands_for(program.clone(), console.clone(), dir))
            .build();
        machine.exec(&mut input.as_bytes()).expect("Execution failed");
        let expected_out: Vec<CapturedOut> =
            expected_out.iter().map(|x| CapturedOut::Print((*x).to_owned())).collect();
        assert_eq!(expected_out, console.borrow().captured_out());

        let program = program.borrow();
        let flat_program: Vec<(usize, &str)> =
            program.iter().map(|(k, v)| (*k, v.as_str())).collect();
        assert_eq!(exp_program, flat_program.as_slice());
    }

    /// Same as `do_ok_test_with_dir` but with an automatic (and inaccessible) `dir`.
    fn do_ok_test(
        program: Program,
        input: &str,
        golden_in: &'static [(&'static str, &'static str, &'static str)],
        expected_out: &'static [&'static str],
        exp_program: &'static [(usize, &'static str)],
    ) {
        let dir = tempfile::tempdir().unwrap();
        do_ok_test_with_dir(program, &dir.path(), input, golden_in, expected_out, exp_program)
    }

    /// Runs the `input` code on a new machine and verifies that it fails with `expected_err`.
    ///
    /// Ensures that this does not touch the console.
    fn do_error_test_with_dir(dir: &Path, input: &str, expected_err: &str) {
        let console = Rc::from(RefCell::from(MockConsole::new(&[])));
        let mut machine = MachineBuilder::default()
            .add_builtins(all_commands_for(Program::default(), console.clone(), dir))
            .build();
        assert_eq!(
            expected_err,
            format!("{}", machine.exec(&mut input.as_bytes()).expect_err("Execution did not fail"))
        );
        assert!(console.borrow().captured_out().is_empty());
    }

    /// Same as `do_error_test_with_dir` but with an automatic (and inaccessible) `dir`.
    fn do_error_test(input: &str, expected_err: &str) {
        let dir = tempfile::tempdir().unwrap();
        do_error_test_with_dir(&dir.path(), input, expected_err)
    }

    /// Reads `path` and checks that its contents match `exp_lines`.
    fn check_file(path: &Path, exp_lines: &[&str]) {
        let file = File::open(path).unwrap();
        let reader = io::BufReader::new(file);
        let mut lines = vec![];
        for line in reader.lines() {
            lines.push(line.unwrap());
        }
        assert_eq!(exp_lines, lines.as_slice());
    }

    /// Creates `path` with the contents in `lines` and with a deterministic modification time.
    fn write_file(path: &Path, lines: &[&str]) {
        let mut file = fs::OpenOptions::new()
            .create(true)
            .truncate(false) // Should not be creating the same file more than once.
            .write(true)
            .open(path)
            .unwrap();
        for line in lines {
            file.write_fmt(format_args!("{}\n", line)).unwrap();
        }
        drop(file);

        let offset = time::UtcOffset::current_local_offset();
        filetime::set_file_mtime(
            path,
            filetime::FileTime::from_unix_time(1_588_757_875 - (offset.as_seconds() as i64), 0),
        )
        .unwrap();
    }

    #[test]
    fn test_dir_empty() {
        let dir = tempfile::tempdir().unwrap();
        do_ok_test_with_dir(
            Program::default(),
            &dir.path(),
            "DIR",
            &[],
            &["", "    Modified            Type       Size    Name", "    0 file(s), 0 bytes", ""],
            &[],
        );
    }

    #[test]
    fn test_dir_treat_missing_as_empty() {
        let dir = tempfile::tempdir().unwrap();
        do_ok_test_with_dir(
            Program::default(),
            &dir.path().join("does-not-exist"),
            "DIR",
            &[],
            &["", "    Modified            Type       Size    Name", "    0 file(s), 0 bytes", ""],
            &[],
        );
    }

    #[test]
    fn test_dir_ignores_subdirs() {
        let dir = tempfile::tempdir().unwrap();
        fs::create_dir(dir.path().join("will-be-ignored")).unwrap();

        do_ok_test_with_dir(
            Program::default(),
            &dir.path(),
            "DIR",
            &[],
            &["", "    Modified            Type       Size    Name", "    0 file(s), 0 bytes", ""],
            &[],
        );
    }

    #[test]
    fn test_dir_entries_are_sorted() {
        let dir = tempfile::tempdir().unwrap();
        write_file(&dir.path().join("empty.bas"), &[]);
        write_file(&dir.path().join("some other file.bas"), &["not empty"]);
        write_file(&dir.path().join("00AAA.BAS"), &["first", "file"]);
        write_file(&dir.path().join("not a bas.txt"), &[]);

        do_ok_test_with_dir(
            Program::default(),
            &dir.path(),
            "DIR",
            &[],
            &[
                "",
                "    Modified            Type       Size    Name",
                "    2020-05-06 09:37                 11    00AAA.BAS",
                "    2020-05-06 09:37                  0    empty.bas",
                "    2020-05-06 09:37                  0    not a bas.txt",
                "    2020-05-06 09:37                 10    some other file.bas",
                "",
                "    4 file(s), 21 bytes",
                "",
            ],
            &[],
        );
    }

    #[cfg(not(target_os = "windows"))]
    #[test]
    fn test_dir_symlinks_are_followed() {
        use std::os::unix::fs as unix_fs;

        let dir = tempfile::tempdir().unwrap();
        write_file(&dir.path().join("some file.bas"), &["this is not empty"]);
        unix_fs::symlink(&Path::new("some file.bas"), &dir.path().join("a link.bas")).unwrap();

        do_ok_test_with_dir(
            Program::default(),
            &dir.path(),
            "DIR",
            &[],
            &[
                "",
                "    Modified            Type       Size    Name",
                "    2020-05-06 09:37    <LNK>        18    a link.bas",
                "    2020-05-06 09:37                 18    some file.bas",
                "",
                "    2 file(s), 36 bytes",
                "",
            ],
            &[],
        );
    }

    #[test]
    fn test_dir_errors() {
        let dir = tempfile::tempdir().unwrap();
        do_error_test_with_dir(&dir.path(), "DIR 2", "DIR takes no arguments");

        // TODO(jmmv): This is very ugly... need better error reporting in general, not just for
        // this one case.
        let enotdir_message = if cfg!(target_os = "windows") {
            "The directory name is invalid. (os error 267)"
        } else {
            "Not a directory (os error 20)"
        };

        let file = dir.path().join("not-a-dir");
        write_file(&file, &[]);
        do_error_test_with_dir(&file, "DIR", enotdir_message);
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
        program.borrow_mut().insert(1023, "    second line".to_owned());
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
    fn test_load_ok() {
        let dir = tempfile::tempdir().unwrap();
        write_file(&dir.path().join("foo.bas"), &["line 1", "  line 2"]);
        write_file(&dir.path().join("foo.bak"), &[]);
        write_file(&dir.path().join("BAR.BAS"), &["line 1", "  line 2"]);
        write_file(&dir.path().join("Baz.bas"), &["line 1", "  line 2"]);

        for p in &["foo", "foo.bas", "BAR", "BAR.BAS", "Baz"] {
            do_ok_test_with_dir(
                Program::default(),
                &dir.path(),
                &("LOAD \"".to_owned() + p + "\""),
                &[],
                &[],
                &[(10, "line 1"), (20, "  line 2")],
            );
        }
    }

    #[test]
    fn test_load_skip_empty_lines() {
        let dir = tempfile::tempdir().unwrap();
        write_file(&dir.path().join("data.bas"), &["a", "", "b", ""]);

        do_ok_test_with_dir(
            Program::default(),
            &dir.path(),
            &("LOAD \"data.bas\""),
            &[],
            &[],
            &[(10, "a"), (20, "b")],
        );
    }

    /// Checks errors that should be handled the same way by `LOAD` and `SAVE`.
    fn check_load_save_common_errors(cmd: &str, dir: &Path) {
        do_error_test_with_dir(&dir, &cmd, &format!("{} requires a filename", cmd));
        do_error_test_with_dir(
            &dir,
            &format!("{} 3", cmd),
            &format!("{} requires a string as the filename", cmd),
        );

        let mut non_basenames = vec!["./foo.bas", "a/b.bas", "a/b"];
        if cfg!(target_os = "windows") {
            non_basenames.push("c:foo.bas");
        }
        for p in non_basenames.as_slice() {
            do_error_test_with_dir(
                &dir,
                &format!("{} \"{}\"", cmd, p),
                "Filename must be a single path component",
            );
        }

        for p in &["foo.bak", "foo.ba", "foo.basic"] {
            do_error_test_with_dir(
                &dir,
                &format!("{} \"{}\"", cmd, p),
                "Invalid filename extension",
            );
        }
    }

    #[test]
    fn test_load_errors() {
        let dir = tempfile::tempdir().unwrap();
        check_load_save_common_errors("LOAD", &dir.path());

        // TODO(jmmv): This is very ugly... need better error reporting in general, not just for
        // this one case.
        let enoent_message = if cfg!(target_os = "windows") {
            "The system cannot find the file specified. (os error 2)"
        } else {
            "No such file or directory (os error 2)"
        };

        do_error_test_with_dir(&dir.path(), "LOAD \"missing-file\"", enoent_message);

        write_file(&dir.path().join("mismatched-extension.bat"), &[]);
        do_error_test_with_dir(&dir.path(), "LOAD \"mismatched-extension\"", enoent_message);
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
            .add_builtin(Rc::from(NewCommand { program: program.clone() }))
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
        do_ok_test(program, "RENUM", &[], &[], &[(10, "one"), (20, "two"), (30, "three")]);
    }

    #[test]
    fn test_renum_insertion() {
        let program = Program::default();
        program.borrow_mut().insert(10, "one".to_owned());
        program.borrow_mut().insert(15, "two".to_owned());
        program.borrow_mut().insert(20, "three".to_owned());
        do_ok_test(program, "RENUM", &[], &[], &[(10, "one"), (20, "two"), (30, "three")]);
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
        do_ok_test(program, "RENUM", &[], &[], &[(10, "one"), (20, "two"), (30, "three")]);
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

    #[test]
    fn test_save_ok() {
        let dir = tempfile::tempdir().unwrap();
        let dir = dir.path().join("subdir"); // Should be auto-created.

        let program = Program::default();
        program.borrow_mut().insert(10, "line 1".to_owned());
        program.borrow_mut().insert(20, "  line 2".to_owned());

        for p in &["first", "second.bas", "THIRD", "FOURTH.BAS", "Fifth"] {
            do_ok_test_with_dir(
                program.clone(),
                &dir,
                &("SAVE \"".to_owned() + p + "\""),
                &[],
                &[],
                &[(10, "line 1"), (20, "  line 2")],
            );
        }

        for p in &["first.bas", "second.bas", "THIRD.BAS", "FOURTH.BAS", "Fifth.bas"] {
            check_file(&dir.join(p), &["line 1", "  line 2"]);
        }
    }

    #[test]
    fn test_save_errors() {
        let dir = tempfile::tempdir().unwrap();
        check_load_save_common_errors("SAVE", &dir.path());
    }
}
