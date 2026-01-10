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

use super::time_format_error_to_io_error;
use crate::console::{Console, Pager, is_narrow};
use crate::storage::Storage;
use async_trait::async_trait;
use endbasic_core::ast::{ArgSep, ExprType};
use endbasic_core::compiler::{ArgSepSyntax, RequiredValueSyntax, SingularArgSyntax};
use endbasic_core::exec::{Machine, Result, Scope};
use endbasic_core::syms::{Callable, CallableMetadata, CallableMetadataBuilder};
use std::borrow::Cow;
use std::cell::RefCell;
use std::cmp;
use std::io;
use std::rc::Rc;
use std::str;
use time::format_description;

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
    let show_narrow = is_narrow(&*console);

    let mut pager = Pager::new(console)?;
    pager.print("").await?;
    pager.print(&format!("    Directory of {}", canonical_path)).await?;
    pager.print("").await?;
    if show_narrow {
        let mut total_files = 0;
        for name in files.dirents().keys() {
            pager.print(&format!("    {}", name,)).await?;
            total_files += 1;
        }
        if total_files > 0 {
            pager.print("").await?;
        }
        pager.print(&format!("    {} file(s)", total_files)).await?;
    } else {
        let mut total_files = 0;
        let mut total_bytes = 0;
        pager.print("    Modified              Size    Name").await?;
        for (name, details) in files.dirents() {
            pager
                .print(&format!(
                    "    {}    {:6}    {}",
                    details.date.format(&format).map_err(time_format_error_to_io_error)?,
                    details.length,
                    name,
                ))
                .await?;
            total_files += 1;
            total_bytes += details.length;
        }
        if total_files > 0 {
            pager.print("").await?;
        }
        pager.print(&format!("    {} file(s), {} bytes", total_files, total_bytes)).await?;
        if let (Some(disk_quota), Some(disk_free)) = (files.disk_quota(), files.disk_free()) {
            pager
                .print(&format!("    {} of {} bytes free", disk_free.bytes, disk_quota.bytes))
                .await?;
        }
    }
    pager.print("").await?;
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
            metadata: CallableMetadataBuilder::new("CD")
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax { name: Cow::Borrowed("path"), vtype: ExprType::Text },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
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

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> Result<()> {
        debug_assert_eq!(1, scope.nargs());
        let target = scope.pop_string();

        self.storage.borrow_mut().cd(&target).map_err(|e| scope.io_error(e))?;

        Ok(())
    }
}

/// The `COPY` command.
pub struct CopyCommand {
    metadata: CallableMetadata,
    storage: Rc<RefCell<Storage>>,
}

impl CopyCommand {
    /// Creates a new `COPY` command that copies a file.
    pub fn new(storage: Rc<RefCell<Storage>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("COPY")
                .with_syntax(&[(
                    &[
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("src"),
                                vtype: ExprType::Text,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("dest"),
                                vtype: ExprType::Text,
                            },
                            ArgSepSyntax::End,
                        ),
                    ],
                    None,
                )])
                .with_category(CATEGORY)
                .with_description(
                    "Copies src to dest.
If dest is a path without a name, the target file given in dest will have the same name \
as the source file in src.
See the \"File system\" help topic for information on the path syntax.",
                )
                .build(),
            storage,
        })
    }
}

#[async_trait(?Send)]
impl Callable for CopyCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> Result<()> {
        debug_assert_eq!(2, scope.nargs());
        let src = scope.pop_string();
        let dest = scope.pop_string();

        let mut storage = self.storage.borrow_mut();
        storage.copy(&src, &dest).await.map_err(|e| scope.io_error(e))?;

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
            metadata: CallableMetadataBuilder::new("DIR")
                .with_syntax(&[
                    (&[], None),
                    (
                        &[SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("path"),
                                vtype: ExprType::Text,
                            },
                            ArgSepSyntax::End,
                        )],
                        None,
                    ),
                ])
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

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> Result<()> {
        let path = if scope.nargs() == 0 {
            "".to_owned()
        } else {
            debug_assert_eq!(1, scope.nargs());
            scope.pop_string()
        };

        show_dir(&self.storage.borrow(), &mut *self.console.borrow_mut(), &path)
            .await
            .map_err(|e| scope.io_error(e))?;

        Ok(())
    }
}

/// The `KILL` command.
pub struct KillCommand {
    metadata: CallableMetadata,
    storage: Rc<RefCell<Storage>>,
}

impl KillCommand {
    /// Creates a new `KILL` command that deletes a file from `storage`.
    pub fn new(storage: Rc<RefCell<Storage>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("KILL")
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax {
                            name: Cow::Borrowed("filename"),
                            vtype: ExprType::Text,
                        },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .with_category(CATEGORY)
                .with_description(
                    "Deletes the given file.
The filename must be a string and must be a valid EndBASIC path.
See the \"File system\" help topic for information on the path syntax.",
                )
                .build(),
            storage,
        })
    }
}

#[async_trait(?Send)]
impl Callable for KillCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> Result<()> {
        debug_assert_eq!(1, scope.nargs());
        let name = scope.pop_string();

        self.storage.borrow_mut().delete(&name).await.map_err(|e| scope.io_error(e))?;

        Ok(())
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
            metadata: CallableMetadataBuilder::new("MOUNT")
                .with_syntax(&[
                    (&[], None),
                    (
                        &[
                            SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax {
                                    name: Cow::Borrowed("target"),
                                    vtype: ExprType::Text,
                                },
                                ArgSepSyntax::Exactly(ArgSep::As),
                            ),
                            SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax {
                                    name: Cow::Borrowed("drive_name"),
                                    vtype: ExprType::Text,
                                },
                                ArgSepSyntax::End,
                            ),
                        ],
                        None,
                    ),
                ])
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

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> Result<()> {
        if scope.nargs() == 0 {
            show_drives(&self.storage.borrow_mut(), &mut *self.console.borrow_mut())
                .map_err(|e| scope.io_error(e))?;
            Ok(())
        } else {
            debug_assert_eq!(2, scope.nargs());
            let target = scope.pop_string();
            let name = scope.pop_string();

            self.storage.borrow_mut().mount(&name, &target).map_err(|e| scope.io_error(e))?;
            Ok(())
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
            metadata: CallableMetadataBuilder::new("PWD")
                .with_syntax(&[(&[], None)])
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

    async fn exec(&self, scope: Scope<'_>, _machine: &mut Machine) -> Result<()> {
        debug_assert_eq!(0, scope.nargs());

        let storage = self.storage.borrow();
        let cwd = storage.cwd();
        let system_cwd = storage.system_path(&cwd).expect("cwd must return a valid path");

        let console = &mut *self.console.borrow_mut();
        console.print("").map_err(|e| scope.io_error(e))?;
        console.print(&format!("    Working directory: {}", cwd)).map_err(|e| scope.io_error(e))?;
        match system_cwd {
            Some(path) => console
                .print(&format!("    System location: {}", path.display()))
                .map_err(|e| scope.io_error(e))?,
            None => {
                console.print("    No system location available").map_err(|e| scope.io_error(e))?
            }
        }
        console.print("").map_err(|e| scope.io_error(e))?;

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
            metadata: CallableMetadataBuilder::new("UNMOUNT")
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax {
                            name: Cow::Borrowed("drive_name"),
                            vtype: ExprType::Text,
                        },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
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

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> Result<()> {
        debug_assert_eq!(1, scope.nargs());
        let drive = scope.pop_string();

        self.storage.borrow_mut().unmount(&drive).map_err(|e| scope.io_error(e))?;

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
    machine.add_callable(CdCommand::new(storage.clone()));
    machine.add_callable(CopyCommand::new(storage.clone()));
    machine.add_callable(DirCommand::new(console.clone(), storage.clone()));
    machine.add_callable(KillCommand::new(storage.clone()));
    machine.add_callable(MountCommand::new(console.clone(), storage.clone()));
    machine.add_callable(PwdCommand::new(console.clone(), storage.clone()));
    machine.add_callable(UnmountCommand::new(storage));
}

#[cfg(test)]
mod tests {
    use crate::console::{CharsXY, Key};
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
        check_stmt_err("1:1: Drive 'A' is not mounted", "CD \"A:\"");
        check_stmt_compilation_err("1:1: CD expected path$", "CD");
        check_stmt_compilation_err("1:1: CD expected path$", "CD 2, 3");
        check_stmt_compilation_err("1:4: expected STRING but found INTEGER", "CD 2");
    }

    #[test]
    fn test_copy_ok() {
        Tester::default()
            .set_program(Some("foo.bas"), "Leave me alone")
            .write_file("file1", "the content")
            .run(r#"COPY "file1", "file2""#)
            .expect_program(Some("foo.bas"), "Leave me alone")
            .expect_file("MEMORY:/file1", "the content")
            .expect_file("MEMORY:/file2", "the content")
            .check();
    }

    #[test]
    fn test_copy_deduce_target_name() {
        let t = Tester::default();
        t.get_storage().borrow_mut().mount("other", "memory://").unwrap();
        t.set_program(Some("foo.bas"), "Leave me alone")
            .write_file("file1.x", "the content")
            .run(r#"COPY "file1.x", "OTHER:/""#)
            .expect_program(Some("foo.bas"), "Leave me alone")
            .expect_file("MEMORY:/file1.x", "the content")
            .expect_file("OTHER:/file1.x", "the content")
            .check();
    }

    #[test]
    fn test_copy_errors() {
        Tester::default()
            .run(r#"COPY "foo""#)
            .expect_compilation_err("1:1: COPY expected src$, dest$")
            .check();

        Tester::default()
            .run(r#"COPY "memory:/", "foo.bar""#)
            .expect_err("1:1: Missing file name in copy source path 'memory:/'")
            .check();

        Tester::default()
            .run(r#"COPY "missing.txt", "new.txt""#)
            .expect_err("1:1: Entry not found")
            .check();

        Tester::default()
            .write_file("foo", "irrelevant")
            .run(r#"COPY "foo", "missing:/""#)
            .expect_err("1:1: Drive 'MISSING' is not mounted")
            .expect_file("MEMORY:/foo", "irrelevant")
            .check();

        //Tester::default()
        //    .run(r#"KILL "a/b.bas""#)
        //    .expect_err("1:1: Too many / separators in path 'a/b.bas'")
        //    .check();

        //Tester::default()
        //    .run(r#"KILL "drive:""#)
        //    .expect_err("1:1: Missing file name in path 'drive:'")
        //    .check();

        //Tester::default()
        //    .run("KILL")
        //    .expect_compilation_err("1:1: KILL expected filename$")
        //    .check();

        //check_stmt_err("1:1: Entry not found", r#"KILL "missing-file""#);

        //Tester::default()
        //    .write_file("no-automatic-extension.bas", "")
        //    .run(r#"KILL "no-automatic-extension""#)
        //    .expect_err("1:1: Entry not found")
        //    .expect_file("MEMORY:/no-automatic-extension.bas", "")
        //    .check();
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
        block_on(other.put("foo.bas", b"hello")).unwrap();

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
        block_on(other.put("foo.bas", b"hello")).unwrap();

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
    fn test_dir_paging() {
        let t = Tester::default();
        t.get_console().borrow_mut().set_interactive(true);
        t.get_console().borrow_mut().set_size_chars(CharsXY { x: 80, y: 7 });
        t.get_console().borrow_mut().add_input_keys(&[Key::NewLine]);
        t.write_file("0.bas", "")
            .write_file("1.bas", "")
            .write_file("2.bas", "")
            .write_file("3.bas", "")
            .run("DIR")
            .expect_prints([
                "",
                "    Directory of MEMORY:/",
                "",
                "    Modified              Size    Name",
                "    2020-05-06 09:37         0    0.bas",
                "    2020-05-06 09:37         0    1.bas",
                " << Press any key for more; ESC or Ctrl+C to stop >> ",
                "    2020-05-06 09:37         0    2.bas",
                "    2020-05-06 09:37         0    3.bas",
                "",
                "    4 file(s), 0 bytes",
                "",
            ])
            .expect_file("MEMORY:/0.bas", "")
            .expect_file("MEMORY:/1.bas", "")
            .expect_file("MEMORY:/2.bas", "")
            .expect_file("MEMORY:/3.bas", "")
            .check();
    }

    #[test]
    fn test_dir_errors() {
        check_stmt_compilation_err("1:1: DIR expected <> | <path$>", "DIR 2, 3");
        check_stmt_compilation_err("1:5: expected STRING but found INTEGER", "DIR 2");
    }

    #[test]
    fn test_kill_ok() {
        for p in &["foo", "foo.bas"] {
            Tester::default()
                .set_program(Some(p), "Leave me alone")
                .write_file("leave-me-alone.bas", "")
                .write_file(p, "line 1\n  line 2\n")
                .run(format!(r#"KILL "{}""#, p))
                .expect_program(Some(*p), "Leave me alone")
                .expect_file("MEMORY:/leave-me-alone.bas", "")
                .check();
        }
    }

    #[test]
    fn test_kill_errors() {
        Tester::default()
            .run("KILL 3")
            .expect_compilation_err("1:6: expected STRING but found INTEGER")
            .check();

        Tester::default()
            .run(r#"KILL "a/b.bas""#)
            .expect_err("1:1: Too many / separators in path 'a/b.bas'")
            .check();

        Tester::default()
            .run(r#"KILL "drive:""#)
            .expect_err("1:1: Missing file name in path 'drive:'")
            .check();

        Tester::default()
            .run("KILL")
            .expect_compilation_err("1:1: KILL expected filename$")
            .check();

        check_stmt_err("1:1: Entry not found", r#"KILL "missing-file""#);

        Tester::default()
            .write_file("no-automatic-extension.bas", "")
            .run(r#"KILL "no-automatic-extension""#)
            .expect_err("1:1: Entry not found")
            .expect_file("MEMORY:/no-automatic-extension.bas", "")
            .check();
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
        check_stmt_compilation_err("1:1: MOUNT expected <> | <target$ AS drive_name$>", "MOUNT 1");
        check_stmt_compilation_err(
            "1:1: MOUNT expected <> | <target$ AS drive_name$>",
            "MOUNT 1, 2, 3",
        );

        check_stmt_compilation_err("1:14: expected STRING but found INTEGER", r#"MOUNT "a" AS 1"#);
        check_stmt_compilation_err("1:7: expected STRING but found INTEGER", r#"MOUNT 1 AS "a""#);

        check_stmt_err("1:1: Invalid drive name 'a:'", r#"MOUNT "memory://" AS "a:""#);
        check_stmt_err(
            "1:1: Mount URI must be of the form scheme://path",
            r#"MOUNT "foo//bar" AS "a""#,
        );
        check_stmt_err("1:1: Unknown mount scheme 'foo'", r#"MOUNT "foo://bar" AS "a""#);
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
        check_stmt_compilation_err("1:1: UNMOUNT expected drive_name$", "UNMOUNT");
        check_stmt_compilation_err("1:1: UNMOUNT expected drive_name$", "UNMOUNT 2, 3");

        check_stmt_compilation_err("1:9: expected STRING but found INTEGER", "UNMOUNT 1");

        check_stmt_err("1:1: Invalid drive name 'a:'", "UNMOUNT \"a:\"");
        check_stmt_err("1:1: Drive 'a' is not mounted", "UNMOUNT \"a\"");
    }
}
