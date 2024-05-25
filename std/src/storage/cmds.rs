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

//! File system interaction.

use crate::console::{is_narrow, Console};
use crate::storage::Storage;
use async_trait::async_trait;
use endbasic_core::ast::{ArgSep, ArgSpan, Value, VarType};
use endbasic_core::bytecode::Instruction;
use endbasic_core::compiler::{
    compile_arg_expr, CallableArgsCompiler, ExprType, NoArgsCompiler, SameTypeArgsCompiler,
    SymbolsTable,
};
use endbasic_core::exec::Machine;
use endbasic_core::syms::{
    CallError, CallResult, Callable, CallableMetadata, CallableMetadataBuilder,
};
use endbasic_core::LineCol;
use std::cell::RefCell;
use std::cmp;
use std::io;
use std::rc::Rc;
use std::str;
use time::format_description;

use super::time_format_error_to_io_error;

/// Category description for all symbols provided by this module.
const CATEGORY: &str = "File system
The EndBASIC storage subsystem is organized as a collection of drives, each identified by a \
case-insensitive name.  Drives can be backed by a multitude of file systems with different \
behaviors, and their targets are specified as URIs.  Special targets include: memory://, which \
points to an in-memory read/write drive; and demos://, which points to a read-only drive with \
sample programs.  Other targets may be available such as file:// to access a local directory or \
local:// to access web-local storage, depending on the context.  The output of the MOUNT command \
can help to identify which targets are available.
All commands that operate with files take a path.  Paths in EndBASIC can be of the form \
FILENAME.EXT, in which case they refer to a file in the current drive; or DRIVE:/FILENAME.EXT and \
DRIVE:FILENAME.EXT, in which case they refer to a file in the specified drive.  Note that the \
slash before the file name is currently optional because EndBASIC does not support directories \
yet.  Furthermore, if .EXT is missing, a .BAS extension is assumed.
Be aware that the commands below must be invoked using proper EndBASIC syntax.  In particular, \
this means that path arguments must be double-quoted and multiple arguments have to be separated \
by a comma (not a space).  If you have used commands like CD, DIR, or MOUNT in other contexts, \
this is likely to confuse you.
See the \"Stored program\" help topic for information on how to load, modify, and save programs.";

/// Shows the contents of the given storage location.
async fn show_dir(storage: &Storage, console: &mut dyn Console, path: &str) -> io::Result<()> {
    let canonical_path = storage.make_canonical(path)?;
    let files = storage.enumerate(path).await?;

    let format = format_description::parse("[year]-[month]-[day] [hour]:[minute]")
        .expect("Hardcoded format must be valid");

    console.print("")?;
    console.print(&format!("    Directory of {}", canonical_path))?;
    console.print("")?;
    if is_narrow(&*console) {
        let mut total_files = 0;
        for name in files.dirents().keys() {
            console.print(&format!("    {}", name,))?;
            total_files += 1;
        }
        if total_files > 0 {
            console.print("")?;
        }
        console.print(&format!("    {} file(s)", total_files))?;
    } else {
        let mut total_files = 0;
        let mut total_bytes = 0;
        console.print("    Modified              Size    Name")?;
        for (name, details) in files.dirents() {
            console.print(&format!(
                "    {}    {:6}    {}",
                details.date.format(&format).map_err(time_format_error_to_io_error)?,
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
        if let (Some(disk_quota), Some(disk_free)) = (files.disk_quota(), files.disk_free()) {
            console
                .print(&format!("    {} of {} bytes free", disk_free.bytes, disk_quota.bytes))?;
        }
    }
    console.print("")?;
    Ok(())
}

/// Shows the mounted drives.
fn show_drives(storage: &Storage, console: &mut dyn Console) -> io::Result<()> {
    let drive_info = storage.mounted();
    let max_length = drive_info.keys().fold("Name".len(), |max, name| cmp::max(max, name.len()));

    console.print("")?;
    let filler = " ".repeat(max_length - "Name".len());
    console.print(&format!("    Name{}    Target", filler))?;
    let num_drives = drive_info.len();
    for (name, uri) in drive_info {
        let filler = " ".repeat(max_length - name.len());
        console.print(&format!("    {}{}    {}", name, filler, uri))?;
    }
    console.print("")?;
    console.print(&format!("    {} drive(s)", num_drives))?;
    console.print("")?;
    Ok(())
}

/// The `CD` command.
pub struct CdCommand {
    metadata: CallableMetadata,
    storage: Rc<RefCell<Storage>>,
}

impl CdCommand {
    /// Creates a new `CD` command that changes the current location in `storage`.
    pub fn new(storage: Rc<RefCell<Storage>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("CD", VarType::Void)
                .with_syntax("path$")
                .with_args_compiler(SameTypeArgsCompiler::new(1, 1, ExprType::Text))
                .with_category(CATEGORY)
                .with_description("Changes the current path.")
                .build(),
            storage,
        })
    }
}

#[async_trait(?Send)]
impl Callable for CdCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, _machine: &mut Machine) -> CallResult {
        let mut iter = args.into_iter();
        let target = match iter.next() {
            Some((Value::Text(t), _pos)) => t,
            _ => unreachable!(),
        };
        debug_assert!(iter.next().is_none());

        self.storage.borrow_mut().cd(&target)?;

        Ok(Value::Void)
    }
}

/// The `DIR` command.
pub struct DirCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
    storage: Rc<RefCell<Storage>>,
}

impl DirCommand {
    /// Creates a new `DIR` command that lists `storage` contents on the `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>, storage: Rc<RefCell<Storage>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("DIR", VarType::Void)
                .with_syntax("[path$]")
                .with_args_compiler(SameTypeArgsCompiler::new(0, 1, ExprType::Text))
                .with_category(CATEGORY)
                .with_description("Displays the list of files on the current or given path.")
                .build(),
            console,
            storage,
        })
    }
}

#[async_trait(?Send)]
impl Callable for DirCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, _machine: &mut Machine) -> CallResult {
        let mut iter = args.into_iter();
        let path = match iter.next() {
            None => "".to_owned(),
            Some((Value::Text(t), _pos)) => t,
            _ => unreachable!(),
        };
        debug_assert!(iter.next().is_none());

        show_dir(&self.storage.borrow(), &mut *self.console.borrow_mut(), &path).await?;

        Ok(Value::Void)
    }
}

/// An arguments compiler for the `MOUNT` command.
#[derive(Debug, Default)]
struct MountArgsCompiler {}

impl CallableArgsCompiler for MountArgsCompiler {
    fn compile_complex(
        &self,
        instrs: &mut Vec<Instruction>,
        symtable: &mut SymbolsTable,
        _pos: LineCol,
        args: Vec<ArgSpan>,
    ) -> Result<usize, CallError> {
        let nargs = args.len();
        if nargs == 0 {
            Ok(0)
        } else if nargs == 2 {
            let mut iter = args.into_iter().rev();

            let span = iter.next().unwrap();
            debug_assert_eq!(ArgSep::End, span.sep);
            match span.expr {
                Some(expr) => {
                    compile_arg_expr(instrs, symtable, expr, ExprType::Text)?;
                }
                None => {
                    return Err(CallError::SyntaxError);
                }
            }

            let span = iter.next().unwrap();
            if span.sep != ArgSep::As {
                return Err(CallError::SyntaxError);
            }
            match span.expr {
                Some(expr) => {
                    compile_arg_expr(instrs, symtable, expr, ExprType::Text)?;
                }
                None => {
                    return Err(CallError::SyntaxError);
                }
            }

            Ok(2)
        } else {
            Err(CallError::SyntaxError)
        }
    }
}

/// The `MOUNT` command.
pub struct MountCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
    storage: Rc<RefCell<Storage>>,
}

impl MountCommand {
    /// Creates a new `MOUNT` command.
    pub fn new(console: Rc<RefCell<dyn Console>>, storage: Rc<RefCell<Storage>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("MOUNT", VarType::Void)
                .with_syntax("[target$ AS drive_name$]")
                .with_args_compiler(MountArgsCompiler::default())
                .with_category(CATEGORY)
                .with_description(
                    "Lists the mounted drives or mounts a new drive.
With no arguments, prints a list of mounted drives and their targets.
With two arguments, mounts the drive_name$ to point to the target$.  Drive names are specified \
without a colon at the end, and targets are given in the form of a URI.",
                )
                .build(),
            console,
            storage,
        })
    }
}

#[async_trait(?Send)]
impl Callable for MountCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, _machine: &mut Machine) -> CallResult {
        if args.is_empty() {
            show_drives(&self.storage.borrow_mut(), &mut *self.console.borrow_mut())?;
            return Ok(Value::Void);
        }

        let mut iter = args.into_iter();
        let target = match iter.next() {
            Some((Value::Text(t), _pos)) => t,
            _ => unreachable!(),
        };
        let name = match iter.next() {
            Some((Value::Text(t), _pos)) => t,
            _ => unreachable!(),
        };
        debug_assert!(iter.next().is_none());

        self.storage.borrow_mut().mount(&name, &target)?;

        Ok(Value::Void)
    }
}

/// The `PWD` command.
pub struct PwdCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
    storage: Rc<RefCell<Storage>>,
}

impl PwdCommand {
    /// Creates a new `PWD` command that prints the current directory of `storage` to the `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>, storage: Rc<RefCell<Storage>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("PWD", VarType::Void)
                .with_syntax("")
                .with_args_compiler(NoArgsCompiler::default())
                .with_category(CATEGORY)
                .with_description(
                    "Prints the current working location.
If the EndBASIC path representing the current location is backed by a real path that is accessible \
by the underlying operating system, displays such path as well.",
                )
                .build(),
            console,
            storage,
        })
    }
}

#[async_trait(?Send)]
impl Callable for PwdCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, _machine: &mut Machine) -> CallResult {
        debug_assert!(args.is_empty());

        let storage = self.storage.borrow();
        let cwd = storage.cwd();
        let system_cwd = storage.system_path(&cwd).expect("cwd must return a valid path");

        let console = &mut *self.console.borrow_mut();
        console.print("")?;
        console.print(&format!("    Working directory: {}", cwd))?;
        match system_cwd {
            Some(path) => console.print(&format!("    System location: {}", path.display()))?,
            None => console.print("    No system location available")?,
        }
        console.print("")?;

        Ok(Value::Void)
    }
}

/// The `UNMOUNT` command.
pub struct UnmountCommand {
    metadata: CallableMetadata,
    storage: Rc<RefCell<Storage>>,
}

impl UnmountCommand {
    /// Creates a new `UNMOUNT` command.
    pub fn new(storage: Rc<RefCell<Storage>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("UNMOUNT", VarType::Void)
                .with_syntax("drive_name$")
                .with_args_compiler(SameTypeArgsCompiler::new(1, 1, ExprType::Text))
                .with_category(CATEGORY)
                .with_description(
                    "Unmounts the given drive.
Drive names are specified without a colon at the end.",
                )
                .build(),
            storage,
        })
    }
}

#[async_trait(?Send)]
impl Callable for UnmountCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, _machine: &mut Machine) -> CallResult {
        let mut iter = args.into_iter();
        let drive = match iter.next() {
            Some((Value::Text(t), _pos)) => t,
            _ => unreachable!(),
        };
        debug_assert!(iter.next().is_none());

        self.storage.borrow_mut().unmount(&drive)?;

        Ok(Value::Void)
    }
}

/// Adds all file system manipulation commands for `storage` to the `machine`, using `console` to
/// display information.
pub fn add_all(
    machine: &mut Machine,
    console: Rc<RefCell<dyn Console>>,
    storage: Rc<RefCell<Storage>>,
) {
    machine.add_callable(CdCommand::new(storage.clone()));
    machine.add_callable(DirCommand::new(console.clone(), storage.clone()));
    machine.add_callable(MountCommand::new(console.clone(), storage.clone()));
    machine.add_callable(PwdCommand::new(console.clone(), storage.clone()));
    machine.add_callable(UnmountCommand::new(storage));
}

#[cfg(test)]
mod tests {
    use crate::console::CharsXY;
    use crate::storage::{DirectoryDriveFactory, DiskSpace, Drive, InMemoryDrive};
    use crate::testutils::*;
    use futures_lite::future::block_on;
    use std::collections::BTreeMap;

    #[test]
    fn test_cd_ok() {
        let mut t = Tester::default();
        t.get_storage().borrow_mut().mount("other", "memory://").unwrap();
        t.run("CD \"other:\"").check();
        assert_eq!("OTHER:/", t.get_storage().borrow().cwd());
        t.run("CD \"memory:/\"").check();
        assert_eq!("MEMORY:/", t.get_storage().borrow().cwd());
    }

    #[test]
    fn test_cd_errors() {
        check_stmt_err("1:1: In call to CD: Drive 'A' is not mounted", "CD \"A:\"");
        check_stmt_compilation_err("1:1: In call to CD: expected path$", "CD");
        check_stmt_compilation_err("1:1: In call to CD: expected path$", "CD 2, 3");
        check_stmt_compilation_err("1:1: In call to CD: 1:4: INTEGER is not a STRING", "CD 2");
    }

    #[test]
    fn test_dir_current_empty() {
        Tester::default()
            .run("DIR")
            .expect_prints([
                "",
                "    Directory of MEMORY:/",
                "",
                "    Modified              Size    Name",
                "    0 file(s), 0 bytes",
                "",
            ])
            .check();
    }

    #[test]
    fn test_dir_with_disk_free() {
        let mut other = InMemoryDrive::default();
        other.fake_disk_quota = Some(DiskSpace::new(456, 0));
        other.fake_disk_free = Some(DiskSpace::new(123, 0));

        let mut t = Tester::default();
        t.get_storage().borrow_mut().attach("other", "z://", Box::from(other)).unwrap();

        t.run("DIR \"OTHER:/\"")
            .expect_prints([
                "",
                "    Directory of OTHER:/",
                "",
                "    Modified              Size    Name",
                "    0 file(s), 0 bytes",
                "    123 of 456 bytes free",
                "",
            ])
            .check();
    }

    #[test]
    fn test_dir_current_entries_are_sorted() {
        Tester::default()
            .write_file("empty.bas", "")
            .write_file("some other file.bas", "not empty\n")
            .write_file("00AAA.BAS", "first\nfile\n")
            .write_file("not a bas.txt", "")
            .run("DIR")
            .expect_prints([
                "",
                "    Directory of MEMORY:/",
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
            .expect_file("MEMORY:/empty.bas", "")
            .expect_file("MEMORY:/some other file.bas", "not empty\n")
            .expect_file("MEMORY:/00AAA.BAS", "first\nfile\n")
            .expect_file("MEMORY:/not a bas.txt", "")
            .check();
    }

    #[test]
    fn test_dir_other_by_argument() {
        let mut other = InMemoryDrive::default();
        block_on(other.put("foo.bas", "hello")).unwrap();

        let mut t = Tester::default().write_file("empty.bas", "");
        t.get_storage().borrow_mut().attach("other", "z://", Box::from(other)).unwrap();

        let mut prints = vec![
            "",
            "    Directory of MEMORY:/",
            "",
            "    Modified              Size    Name",
            "    2020-05-06 09:37         0    empty.bas",
            "",
            "    1 file(s), 0 bytes",
            "",
        ];
        t.run("DIR \"memory:\"")
            .expect_prints(prints.clone())
            .expect_file("MEMORY:/empty.bas", "")
            .expect_file("OTHER:/foo.bas", "hello")
            .check();

        prints.extend([
            "",
            "    Directory of OTHER:/",
            "",
            "    Modified              Size    Name",
            "    2020-05-06 09:37         5    foo.bas",
            "",
            "    1 file(s), 5 bytes",
            "",
        ]);
        t.run("DIR \"other:/\"")
            .expect_prints(prints)
            .expect_file("MEMORY:/empty.bas", "")
            .expect_file("OTHER:/foo.bas", "hello")
            .check();
    }

    #[test]
    fn test_dir_other_by_cwd() {
        let mut other = InMemoryDrive::default();
        block_on(other.put("foo.bas", "hello")).unwrap();

        let mut t = Tester::default().write_file("empty.bas", "");
        t.get_storage().borrow_mut().attach("other", "z://", Box::from(other)).unwrap();

        let mut prints = vec![
            "",
            "    Directory of MEMORY:/",
            "",
            "    Modified              Size    Name",
            "    2020-05-06 09:37         0    empty.bas",
            "",
            "    1 file(s), 0 bytes",
            "",
        ];
        t.run("DIR")
            .expect_prints(prints.clone())
            .expect_file("MEMORY:/empty.bas", "")
            .expect_file("OTHER:/foo.bas", "hello")
            .check();

        t.get_storage().borrow_mut().cd("other:/").unwrap();
        prints.extend([
            "",
            "    Directory of OTHER:/",
            "",
            "    Modified              Size    Name",
            "    2020-05-06 09:37         5    foo.bas",
            "",
            "    1 file(s), 5 bytes",
            "",
        ]);
        t.run("DIR")
            .expect_prints(prints)
            .expect_file("MEMORY:/empty.bas", "")
            .expect_file("OTHER:/foo.bas", "hello")
            .check();
    }

    #[test]
    fn test_dir_narrow_empty() {
        let mut t = Tester::default();
        t.get_console().borrow_mut().set_size_chars(CharsXY::new(10, 1));
        t.run("DIR")
            .expect_prints(["", "    Directory of MEMORY:/", "", "    0 file(s)", ""])
            .check();
    }

    #[test]
    fn test_dir_narrow_some() {
        let mut t = Tester::default().write_file("empty.bas", "");
        t.get_console().borrow_mut().set_size_chars(CharsXY::new(10, 1));
        t.run("DIR")
            .expect_prints([
                "",
                "    Directory of MEMORY:/",
                "",
                "    empty.bas",
                "",
                "    1 file(s)",
                "",
            ])
            .expect_file("MEMORY:/empty.bas", "")
            .check();
    }

    #[test]
    fn test_dir_errors() {
        check_stmt_compilation_err("1:1: In call to DIR: expected [path$]", "DIR 2, 3");
        check_stmt_compilation_err("1:1: In call to DIR: 1:5: INTEGER is not a STRING", "DIR 2");
    }

    #[test]
    fn test_mount_list() {
        let mut t = Tester::default();
        let other = InMemoryDrive::default();
        t.get_storage().borrow_mut().attach("o", "origin://", Box::from(other)).unwrap();

        let mut prints = vec![
            "",
            "    Name      Target",
            "    MEMORY    memory://",
            "    O         origin://",
            "",
            "    2 drive(s)",
            "",
        ];
        t.run("MOUNT").expect_prints(prints.clone()).check();

        t.get_storage().borrow_mut().cd("o:").unwrap();
        t.get_storage().borrow_mut().unmount("memory").unwrap();
        prints.extend([
            "",
            "    Name    Target",
            "    O       origin://",
            "",
            "    1 drive(s)",
            "",
        ]);
        t.run("MOUNT").expect_prints(prints.clone()).check();
    }

    #[test]
    fn test_mount_mount() {
        let mut t = Tester::default();
        t.run(r#"MOUNT "memory://" AS "abc""#).check();

        let mut exp_info = BTreeMap::default();
        exp_info.insert("MEMORY", "memory://");
        exp_info.insert("ABC", "memory://");
        assert_eq!(exp_info, t.get_storage().borrow().mounted());
    }

    #[test]
    fn test_mount_errors() {
        check_stmt_compilation_err(
            "1:1: In call to MOUNT: expected [target$ AS drive_name$]",
            "MOUNT 1",
        );
        check_stmt_compilation_err(
            "1:1: In call to MOUNT: expected [target$ AS drive_name$]",
            "MOUNT 1, 2, 3",
        );

        check_stmt_compilation_err(
            "1:1: In call to MOUNT: 1:14: INTEGER is not a STRING",
            r#"MOUNT "a" AS 1"#,
        );
        check_stmt_compilation_err(
            "1:1: In call to MOUNT: 1:7: INTEGER is not a STRING",
            r#"MOUNT 1 AS "a""#,
        );

        check_stmt_err(
            "1:1: In call to MOUNT: Invalid drive name 'a:'",
            r#"MOUNT "memory://" AS "a:""#,
        );
        check_stmt_err(
            "1:1: In call to MOUNT: Mount URI must be of the form scheme://path",
            r#"MOUNT "foo//bar" AS "a""#,
        );
        check_stmt_err(
            "1:1: In call to MOUNT: Unknown mount scheme 'foo'",
            r#"MOUNT "foo://bar" AS "a""#,
        );
    }

    #[test]
    fn test_pwd_without_system_path() {
        let mut t = Tester::default();

        t.run("PWD")
            .expect_prints([
                "",
                "    Working directory: MEMORY:/",
                "    No system location available",
                "",
            ])
            .check();
    }

    #[test]
    fn test_pwd_with_system_path() {
        let dir = tempfile::tempdir().unwrap();
        let dir = dir.path().canonicalize().unwrap();

        let mut t = Tester::default();
        {
            let storage = t.get_storage();
            let storage = &mut *storage.borrow_mut();
            storage.register_scheme("file", Box::from(DirectoryDriveFactory::default()));
            storage.mount("other", &format!("file://{}", dir.display())).unwrap();
            storage.cd("other:/").unwrap();
        }

        t.run("PWD")
            .expect_prints([
                "",
                "    Working directory: OTHER:/",
                &format!("    System location: {}", dir.join("").display()),
                "",
            ])
            .check();
    }

    #[test]
    fn test_unmount_ok() {
        let mut t = Tester::default();
        t.get_storage().borrow_mut().mount("other", "memory://").unwrap();
        t.get_storage().borrow_mut().cd("other:").unwrap();
        t.run("UNMOUNT \"memory\"").check();

        let mut exp_info = BTreeMap::default();
        exp_info.insert("OTHER", "memory://");
        assert_eq!(exp_info, t.get_storage().borrow().mounted());
    }

    #[test]
    fn test_unmount_errors() {
        check_stmt_compilation_err("1:1: In call to UNMOUNT: expected drive_name$", "UNMOUNT");
        check_stmt_compilation_err("1:1: In call to UNMOUNT: expected drive_name$", "UNMOUNT 2, 3");

        check_stmt_compilation_err(
            "1:1: In call to UNMOUNT: 1:9: INTEGER is not a STRING",
            "UNMOUNT 1",
        );

        check_stmt_err("1:1: In call to UNMOUNT: Invalid drive name 'a:'", "UNMOUNT \"a:\"");
        check_stmt_err("1:1: In call to UNMOUNT: Drive 'a' is not mounted", "UNMOUNT \"a\"");
    }
}
