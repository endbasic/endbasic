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

//! Stored program manipulation.

use crate::console::Console;
use async_trait::async_trait;
use endbasic_core::ast::{ArgSep, Expr, Value, VarType};
use endbasic_core::exec::Machine;
use endbasic_core::syms::{
    CallError, CallableMetadata, CallableMetadataBuilder, Command, CommandResult,
};
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::PathBuf;
use std::rc::Rc;
use std::str;

/// Category string for all functions provided by this module.
const CATEGORY: &str = "Stored program manipulation";

/// Metadata of an entry in the store.
#[derive(Clone, Debug, Eq, PartialEq)]
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

/// An implementation of the store that records all data in memory only.
#[derive(Default)]
pub struct InMemoryStore {
    programs: HashMap<String, String>,
}

impl InMemoryStore {
    /// Returns the mapping of stored file names to their contents.
    pub fn as_hashmap(&self) -> &HashMap<String, String> {
        &self.programs
    }
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

/// An implementation of `Store` backed by an on-disk directory.
pub struct FileStore {
    /// Path to the directory containing all entries backed by this `Store`.  The directory may
    /// contain files that are not EndBASIC programs, and that's OK, but those files will not be
    /// accessible through this interface.
    dir: PathBuf,
}

impl FileStore {
    /// Creates a new store backed by the `dir` directory.
    pub fn new<P: Into<PathBuf>>(dir: P) -> Self {
        Self { dir: dir.into() }
    }
}

impl Store for FileStore {
    fn delete(&mut self, name: &str) -> io::Result<()> {
        let path = self.dir.join(name);
        fs::remove_file(path)
    }

    fn enumerate(&self) -> io::Result<BTreeMap<String, Metadata>> {
        let mut entries = BTreeMap::default();
        match fs::read_dir(&self.dir) {
            Ok(dirents) => {
                for de in dirents {
                    let de = de?;

                    let file_type = de.file_type()?;
                    if !file_type.is_file() && !file_type.is_symlink() {
                        // Silently ignore entries we cannot handle.
                        continue;
                    }

                    // This follows symlinks for cross-platform simplicity, but it is ugly.  I don't
                    // expect symlinks in the programs directory anyway.  If we want to handle this
                    // better, we'll have to add a way to report file types.
                    let metadata = fs::metadata(de.path())?;
                    let offset = match time::UtcOffset::try_current_local_offset() {
                        Ok(offset) => offset,
                        Err(_) => time::UtcOffset::UTC,
                    };
                    let date = time::OffsetDateTime::from(metadata.modified()?).to_offset(offset);
                    let length = metadata.len();

                    entries.insert(
                        de.file_name().to_string_lossy().to_string(),
                        Metadata { date, length },
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

    fn get(&self, name: &str) -> io::Result<String> {
        let path = self.dir.join(name);
        let input = File::open(&path)?;
        let mut content = String::new();
        io::BufReader::new(input).read_to_string(&mut content)?;
        Ok(content)
    }

    fn put(&mut self, name: &str, content: &str) -> io::Result<()> {
        let path = self.dir.join(name);
        let dir = path.parent().expect("Must be a filename with a directory");
        fs::create_dir_all(&dir)?;

        let output = OpenOptions::new().create(true).write(true).truncate(true).open(path)?;
        let mut writer = io::BufWriter::new(output);
        writer.write_all(content.as_bytes())
    }
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
pub struct DelCommand {
    metadata: CallableMetadata,
    store: Rc<RefCell<dyn Store>>,
}

impl DelCommand {
    /// Creates a new `DEL` command that deletes a file from the `store`.
    pub fn new(store: Rc<RefCell<dyn Store>>) -> Rc<Self> {
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
            store,
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
        match arg0.eval(machine.get_symbols())? {
            Value::Text(t) => {
                let name = to_filename(t)?;
                self.store.borrow_mut().delete(&name)?;
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

/// The `DIR` command.
pub struct DirCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
    store: Rc<RefCell<dyn Store>>,
}

impl DirCommand {
    /// Creates a new `DIR` command that lists the contents of the `store` on the `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>, store: Rc<RefCell<dyn Store>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("DIR", VarType::Void)
                .with_syntax("")
                .with_category(CATEGORY)
                .with_description("Displays the list of files on disk.")
                .build(),
            console,
            store,
        })
    }
}

#[async_trait(?Send)]
impl Command for DirCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], _machine: &mut Machine) -> CommandResult {
        if !args.is_empty() {
            return Err(CallError::ArgumentError("DIR takes no arguments".to_owned()));
        }
        show_dir(&*self.store.borrow(), &mut *self.console.borrow_mut())?;
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
    store: Rc<RefCell<dyn Store>>,
    program: Rc<RefCell<dyn Program>>,
}

impl LoadCommand {
    /// Creates a new `LOAD` command that loads a program from the `store` into `program`.
    pub fn new(store: Rc<RefCell<dyn Store>>, program: Rc<RefCell<dyn Program>>) -> Rc<Self> {
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
            store,
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
        match arg0.eval(machine.get_symbols())? {
            Value::Text(t) => {
                let name = to_filename(t)?;
                let content = self.store.borrow().get(&name)?;
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
    store: Rc<RefCell<dyn Store>>,
    program: Rc<RefCell<dyn Program>>,
}

impl SaveCommand {
    /// Creates a new `SAVE` command that saves the contents of the `program` in the `store`.
    pub fn new(store: Rc<RefCell<dyn Store>>, program: Rc<RefCell<dyn Program>>) -> Rc<Self> {
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
            store,
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
        match arg0.eval(machine.get_symbols())? {
            Value::Text(t) => {
                let name = to_filename(t)?;
                let content = self.program.borrow().text();
                self.store.borrow_mut().put(&name, &content)?;
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
/// `console` for interactive editing and using `store` as the on-disk storage for the programs.
pub fn add_all(
    machine: &mut Machine,
    program: Rc<RefCell<dyn Program>>,
    console: Rc<RefCell<dyn Console>>,
    store: Rc<RefCell<dyn Store>>,
) {
    machine.add_command(DelCommand::new(store.clone()));
    machine.add_command(DirCommand::new(console.clone(), store.clone()));
    machine.add_command(EditCommand::new(console.clone(), program.clone()));
    machine.add_command(ListCommand::new(console.clone(), program.clone()));
    machine.add_command(LoadCommand::new(store.clone(), program.clone()));
    machine.add_command(NewCommand::new(program.clone()));
    machine.add_command(RunCommand::new(console, program.clone()));
    machine.add_command(SaveCommand::new(store, program));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;
    use std::fs;
    use std::io::{BufRead, Write};
    use std::path::Path;

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

        filetime::set_file_mtime(path, filetime::FileTime::from_unix_time(1_588_757_875, 0))
            .unwrap();
    }

    #[test]
    fn test_filestore_delete_ok() {
        let dir = tempfile::tempdir().unwrap();
        write_file(&dir.path().join("a.bas"), &[]);
        write_file(&dir.path().join("a.bat"), &[]);

        let mut store = FileStore::new(&dir.path());
        store.delete("a.bas").unwrap();
        assert!(!dir.path().join("a.bas").exists());
        assert!(dir.path().join("a.bat").exists());
    }

    #[test]
    fn test_filestore_delete_missing_file() {
        let dir = tempfile::tempdir().unwrap();
        let mut store = FileStore::new(&dir.path());
        assert_eq!(io::ErrorKind::NotFound, store.delete("a.bas").unwrap_err().kind());
    }

    #[test]
    fn test_filestore_enumerate_nothing() {
        let dir = tempfile::tempdir().unwrap();

        let store = FileStore::new(&dir.path());
        assert!(store.enumerate().unwrap().is_empty());
    }

    #[test]
    fn test_filestore_enumerate_some_files() {
        let dir = tempfile::tempdir().unwrap();
        write_file(&dir.path().join("empty.bas"), &[]);
        write_file(&dir.path().join("some file.bas"), &["this is not empty"]);

        let store = FileStore::new(&dir.path());
        let entries = store.enumerate().unwrap();
        assert_eq!(2, entries.len());
        let date = time::OffsetDateTime::from_unix_timestamp(1_588_757_875);
        assert_eq!(&Metadata { date, length: 0 }, entries.get("empty.bas").unwrap());
        assert_eq!(&Metadata { date, length: 18 }, entries.get("some file.bas").unwrap());
    }

    #[test]
    fn test_filestore_enumerate_treats_missing_dir_as_empty() {
        let dir = tempfile::tempdir().unwrap();
        let store = FileStore::new(dir.path().join("does-not-exist"));
        assert!(store.enumerate().unwrap().is_empty());
    }

    #[test]
    fn test_filestore_enumerate_ignores_non_files() {
        let dir = tempfile::tempdir().unwrap();
        fs::create_dir(dir.path().join("will-be-ignored")).unwrap();
        let store = FileStore::new(&dir.path());
        assert!(store.enumerate().unwrap().is_empty());
    }

    #[cfg(not(target_os = "windows"))]
    #[test]
    fn test_filestore_enumerate_follows_symlinks() {
        use std::os::unix::fs as unix_fs;

        let dir = tempfile::tempdir().unwrap();
        write_file(&dir.path().join("some file.bas"), &["this is not empty"]);
        unix_fs::symlink(&Path::new("some file.bas"), &dir.path().join("a link.bas")).unwrap();

        let store = FileStore::new(&dir.path());
        let entries = store.enumerate().unwrap();
        assert_eq!(2, entries.len());
        let metadata =
            Metadata { date: time::OffsetDateTime::from_unix_timestamp(1_588_757_875), length: 18 };
        assert_eq!(&metadata, entries.get("some file.bas").unwrap());
        assert_eq!(&metadata, entries.get("a link.bas").unwrap());
    }

    #[test]
    fn test_filestore_enumerate_fails_on_non_directory() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("not-a-dir");
        write_file(&file, &[]);
        let store = FileStore::new(&file);
        assert_eq!(io::ErrorKind::Other, store.enumerate().unwrap_err().kind());
    }

    #[test]
    fn test_filestore_get() {
        let dir = tempfile::tempdir().unwrap();
        write_file(&dir.path().join("some file.bas"), &["one line", "two lines"]);

        let store = FileStore::new(&dir.path());
        assert_eq!("one line\ntwo lines\n", store.get("some file.bas").unwrap());
    }

    #[test]
    fn test_filestore_put() {
        let dir = tempfile::tempdir().unwrap();

        let mut store = FileStore::new(&dir.path());
        store.put("some file.bas", "a b c\nd e\n").unwrap();
        check_file(&dir.path().join("some file.bas"), &["a b c", "d e"]);
    }

    #[test]
    fn test_del_ok() {
        for p in &["foo", "foo.bas"] {
            Tester::default()
                .set_program("Leave me alone")
                .write_file("bar.bas", "")
                .write_file("foo.bas", "line 1\n  line 2\n")
                .run(format!(r#"DEL "{}""#, p))
                .expect_program("Leave me alone")
                .expect_file("bar.bas", "")
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
            .expect_file("mismatched-extension.bat", "")
            .check();
    }

    #[test]
    fn test_dir_empty() {
        Tester::default()
            .run("DIR")
            .expect_prints([
                "",
                "    Modified              Size    Name",
                "    0 file(s), 0 bytes",
                "",
            ])
            .check();
    }

    #[test]
    fn test_dir_entries_are_sorted() {
        Tester::default()
            .write_file("empty.bas", "")
            .write_file("some other file.bas", "not empty\n")
            .write_file("00AAA.BAS", "first\nfile\n")
            .write_file("not a bas.txt", "")
            .run("DIR")
            .expect_prints([
                "",
                "    Modified              Size    Name",
                "    2020-05-06 09:37        11    00AAA.BAS",
                "    2020-05-06 09:37         0    empty.bas",
                "    2020-05-06 09:37         0    not a bas.txt",
                "    2020-05-06 09:37        10    some other file.bas",
                "",
                "    4 file(s), 21 bytes",
                "",
            ])
            .expect_file("empty.bas", "")
            .expect_file("some other file.bas", "not empty\n")
            .expect_file("00AAA.BAS", "first\nfile\n")
            .expect_file("not a bas.txt", "")
            .check();
    }

    #[test]
    fn test_dir_errors() {
        check_stmt_err("DIR takes no arguments", "DIR 2");
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
                .expect_file("foo.bas", content)
                .expect_file("foo.bak", "")
                .expect_file("BAR.BAS", content)
                .expect_file("Baz.bas", content)
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

        let mut non_basenames = vec!["./foo.bas", "a/b.bas", "a/b"];
        if cfg!(target_os = "windows") {
            non_basenames.push("c:foo.bas");
        }
        for p in non_basenames.as_slice() {
            Tester::default()
                .run(format!(r#"{} "{}""#, cmd, p))
                .expect_err("Filename must be a single path component".to_owned())
                .check();
        }

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
            .expect_file("mismatched-extension.bat", "")
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
            ("first", "first.bas"),
            ("second.bas", "second.bas"),
            ("THIRD", "THIRD.BAS"),
            ("FOURTH.BAS", "FOURTH.BAS"),
            ("Fifth", "Fifth.bas"),
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
