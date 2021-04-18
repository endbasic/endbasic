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

use crate::console::Console;
use crate::storage::Storage;
use async_trait::async_trait;
use endbasic_core::ast::{ArgSep, Expr, Value, VarType};
use endbasic_core::exec::Machine;
use endbasic_core::syms::{
    CallError, CallableMetadata, CallableMetadataBuilder, Command, CommandResult,
};
use std::cell::RefCell;
use std::cmp;
use std::io;
use std::rc::Rc;
use std::str;

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
See the \"Strored program\" help topic for information on how to load, modify, and save programs.";

/// Shows the contents of the given storage location.
async fn show_dir(storage: &Storage, console: &mut dyn Console, path: &str) -> io::Result<()> {
    let canonical_path = storage.make_canonical(path)?;
    let entries = storage.enumerate(path).await?;

    console.print("")?;
    console.print(&format!("    Directory of {}", canonical_path))?;
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
                .with_category(CATEGORY)
                .with_description("Changes the current path.")
                .build(),
            storage,
        })
    }
}

#[async_trait(?Send)]
impl Command for CdCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        if args.len() != 1 {
            return Err(CallError::ArgumentError("CD takes one argument".to_owned()));
        }
        let arg0 = args[0].0.as_ref().expect("Single argument must be present");
        match arg0.eval(machine.get_mut_symbols())? {
            Value::Text(t) => {
                self.storage.borrow_mut().cd(&t)?;
            }
            _ => {
                return Err(CallError::ArgumentError("CD requires a string as the path".to_owned()))
            }
        }
        Ok(())
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
                .with_category(CATEGORY)
                .with_description("Displays the list of files on the current or given path.")
                .build(),
            console,
            storage,
        })
    }
}

#[async_trait(?Send)]
impl Command for DirCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        match args {
            [] => {
                show_dir(&*self.storage.borrow(), &mut *self.console.borrow_mut(), "").await?;
                Ok(())
            }
            [(Some(path), ArgSep::End)] => match path.eval(machine.get_mut_symbols())? {
                Value::Text(path) => {
                    show_dir(&*self.storage.borrow(), &mut *self.console.borrow_mut(), &path)
                        .await?;
                    Ok(())
                }
                _ => {
                    return Err(CallError::ArgumentError(
                        "DIR requires a string as the path".to_owned(),
                    ))
                }
            },
            _ => Err(CallError::ArgumentError("DIR takes zero or one argument".to_owned())),
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
                .with_syntax("[drive_name$, target$]")
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
impl Command for MountCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        match args {
            [] => {
                show_drives(&*self.storage.borrow_mut(), &mut *self.console.borrow_mut())?;
                Ok(())
            }
            [(Some(name), ArgSep::Long), (Some(target), ArgSep::End)] => {
                let name = match name.eval(machine.get_mut_symbols())? {
                    Value::Text(t) => t,
                    _ => {
                        return Err(CallError::ArgumentError(
                            "Drive name must be a string".to_owned(),
                        ))
                    }
                };
                let target = match target.eval(machine.get_mut_symbols())? {
                    Value::Text(t) => t,
                    _ => {
                        return Err(CallError::ArgumentError(
                            "Mount target must be a string".to_owned(),
                        ))
                    }
                };
                self.storage.borrow_mut().mount(&name, &target)?;
                Ok(())
            }
            _ => Err(CallError::ArgumentError("MOUNT takes zero or two arguments".to_owned())),
        }
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
impl Command for PwdCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], _machine: &mut Machine) -> CommandResult {
        if !args.is_empty() {
            return Err(CallError::ArgumentError("PWD takes zero arguments".to_owned()));
        }

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

        Ok(())
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
                .with_syntax("drive_name")
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
impl Command for UnmountCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        if args.len() != 1 {
            return Err(CallError::ArgumentError("UNMOUNT takes one argument".to_owned()));
        }
        let arg0 = args[0].0.as_ref().expect("Single argument must be present");
        match arg0.eval(machine.get_mut_symbols())? {
            Value::Text(t) => {
                self.storage.borrow_mut().unmount(&t)?;
            }
            _ => return Err(CallError::ArgumentError("Drive name must be a string".to_owned())),
        }
        Ok(())
    }
}

/// Adds all file system manipulation commands for `storage` to the `machine`, using `console` to
/// display information.
pub fn add_all(
    machine: &mut Machine,
    console: Rc<RefCell<dyn Console>>,
    storage: Rc<RefCell<Storage>>,
) {
    machine.add_command(CdCommand::new(storage.clone()));
    machine.add_command(DirCommand::new(console.clone(), storage.clone()));
    machine.add_command(MountCommand::new(console.clone(), storage.clone()));
    machine.add_command(PwdCommand::new(console.clone(), storage.clone()));
    machine.add_command(UnmountCommand::new(storage));
}

#[cfg(test)]
mod tests {
    use crate::storage::{directory_drive_factory, Drive, InMemoryDrive};
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
        check_stmt_err("Drive 'A' is not mounted", "CD \"A:\"");
        check_stmt_err("CD takes one argument", "CD");
        check_stmt_err("CD takes one argument", "CD 2, 3");
        check_stmt_err("CD requires a string as the path", "CD 2");
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

        prints.extend(&[
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
        prints.extend(&[
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
    fn test_dir_errors() {
        check_stmt_err("DIR takes zero or one argument", "DIR 2, 3");
        check_stmt_err("DIR requires a string as the path", "DIR 2");
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
        prints.extend(&[
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
        t.run("MOUNT \"abc\", \"memory://\"").check();

        let mut exp_info = BTreeMap::default();
        exp_info.insert("MEMORY", "memory://");
        exp_info.insert("ABC", "memory://");
        assert_eq!(exp_info, t.get_storage().borrow().mounted());
    }

    #[test]
    fn test_mount_errors() {
        check_stmt_err("MOUNT takes zero or two arguments", "MOUNT 1");
        check_stmt_err("MOUNT takes zero or two arguments", "MOUNT 1, 2, 3");

        check_stmt_err("Drive name must be a string", "MOUNT 1, \"a\"");
        check_stmt_err("Mount target must be a string", "MOUNT \"a\", 1");

        check_stmt_err("Invalid drive name 'a:'", "MOUNT \"a:\", \"memory://\"");
        check_stmt_err("Mount URI must be of the form scheme://path", "MOUNT \"a\", \"foo//bar\"");
        check_stmt_err("Unknown mount scheme 'foo'", "MOUNT \"a\", \"foo://bar\"");
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
            storage.register_scheme("file", directory_drive_factory);
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
        check_stmt_err("UNMOUNT takes one argument", "UNMOUNT");
        check_stmt_err("UNMOUNT takes one argument", "UNMOUNT 2, 3");

        check_stmt_err("Drive name must be a string", "UNMOUNT 1");

        check_stmt_err("Invalid drive name 'a:'", "UNMOUNT \"a:\"");
        check_stmt_err("Drive 'a' is not mounted", "UNMOUNT \"a\"");
    }
}
