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

//! Interactive interpreter for the EndBASIC language.

// Keep these in sync with other top-level files.
#![allow(clippy::await_holding_refcell_ref)]
#![allow(clippy::collapsible_else_if)]
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(unused, unused_extern_crates, unused_import_braces, unused_qualifications)]
#![warn(unsafe_code)]

use endbasic_core::exec::{Machine, StopReason};
use endbasic_std::console::{self, refill_and_print, Console};
use endbasic_std::program::{continue_if_modified, Program};
use endbasic_std::storage::Storage;
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

pub mod demos;
pub mod editor;

/// Prints the EndBASIC welcome message to the given console.
pub fn print_welcome(console: Rc<RefCell<dyn Console>>) -> io::Result<()> {
    let mut console = console.borrow_mut();
    console.print("")?;
    console.print(&format!("    EndBASIC {}", env!("CARGO_PKG_VERSION")))?;
    console.print("    Copyright 2020-2022 Julio Merino")?;
    console.print("")?;
    console.print("    Type HELP for interactive usage information.")?;
    console.print("")?;
    Ok(())
}

/// Loads the `AUTOEXEC.BAS` file if it exists in the `drive`.
///
/// Failures to process the file are logged to the `console` but are ignored.  Other failures are
/// returned.
pub async fn try_load_autoexec(
    machine: &mut Machine,
    console: Rc<RefCell<dyn Console>>,
    storage: Rc<RefCell<Storage>>,
) -> io::Result<()> {
    let code = match storage.borrow().get("AUTOEXEC.BAS").await {
        Ok(code) => code,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(e) => {
            return console
                .borrow_mut()
                .print(&format!("AUTOEXEC.BAS exists but cannot be read: {}", e));
        }
    };

    console.borrow_mut().print("Loading AUTOEXEC.BAS...")?;
    match machine.exec(&mut code.as_bytes()).await {
        Ok(_) => Ok(()),
        Err(e) => {
            console.borrow_mut().print(&format!("AUTOEXEC.BAS failed: {}", e))?;
            Ok(())
        }
    }
}

/// Loads the program given in `username_path` pair (which is of the form `user/path`) from the
/// cloud and executes it on the `machine`.
pub async fn run_from_cloud(
    machine: &mut Machine,
    console: Rc<RefCell<dyn Console>>,
    storage: Rc<RefCell<Storage>>,
    program: Rc<RefCell<dyn Program>>,
    username_path: &str,
    will_run_repl: bool,
) -> endbasic_core::exec::Result<i32> {
    let (fs_uri, path) = match username_path.split_once('/') {
        Some((username, path)) => (format!("cloud://{}", username), format!("AUTORUN:/{}", path)),
        None => {
            let mut console = console.borrow_mut();
            console.print(&format!(
                "Invalid program to run '{}'; must be of the form 'username/path'",
                username_path
            ))?;
            return Ok(1);
        }
    };

    console.borrow_mut().print(&format!("Mounting {} as AUTORUN...", fs_uri))?;
    storage.borrow_mut().mount("AUTORUN", &fs_uri)?;
    storage.borrow_mut().cd("AUTORUN:/")?;

    console.borrow_mut().print(&format!("Loading {}...", path))?;
    let content = storage.borrow().get(&path).await?;
    program.borrow_mut().load(Some(&path), &content);

    console.borrow_mut().print("Starting...")?;
    console.borrow_mut().print("")?;

    let result = machine.exec(&mut "RUN".as_bytes()).await;

    let mut console = console.borrow_mut();

    console.print("")?;
    let code = match result {
        Ok(StopReason::Eof) => {
            console.print("**** Program exited due to EOF ****")?;
            0
        }
        Ok(StopReason::Exited(code)) => {
            console.print(&format!("**** Program exited with code {} ****", code))?;
            code as i32
        }
        Err(e) => {
            console.print(&format!("**** ERROR: {} ****", e))?;
            1
        }
    };

    if will_run_repl {
        console.print("")?;
        refill_and_print(
            &mut *console,
            [
                "You are now being dropped into the EndBASIC interpreter.",
                "The program you asked to run is still loaded in memory and you can interact with \
it now.  Use LIST to view the source code, EDIT to launch an editor on the source code, and RUN to \
execute the program again.",
                "Type HELP for interactive usage information.",
            ],
            "   ",
        )?;
        console.print("")?;
    }

    Ok(code)
}

/// Enters the interactive interpreter.
///
/// The `console` provided here is used for the REPL prompt interaction and should match the
/// console that's in use by the machine (if any).  They don't necessarily have to match though.
pub async fn run_repl_loop(
    machine: &mut Machine,
    console: Rc<RefCell<dyn Console>>,
    program: Rc<RefCell<dyn Program>>,
) -> io::Result<i32> {
    let mut stop_reason = StopReason::Eof;
    let mut history = vec![];
    while stop_reason == StopReason::Eof {
        let line = {
            let mut console = console.borrow_mut();
            if console.is_interactive() {
                console.print("Ready")?;
            }
            console::read_line(&mut *console, "", "", Some(&mut history)).await
        };

        match line {
            Ok(line) => match machine.exec(&mut line.as_bytes()).await {
                Ok(reason) => stop_reason = reason,
                Err(e) => {
                    let mut console = console.borrow_mut();
                    console.print(format!("ERROR: {}", e).as_str())?;
                }
            },
            Err(e) => {
                if e.kind() == io::ErrorKind::Interrupted {
                    let mut console = console.borrow_mut();
                    console.print("Interrupted by CTRL-C")?;
                    // TODO(jmmv): This should cause the interpreter to exit with a signal.
                    stop_reason = StopReason::Exited(1);
                } else if e.kind() == io::ErrorKind::UnexpectedEof {
                    let mut console = console.borrow_mut();
                    console.print("End of input by CTRL-D")?;
                    stop_reason = StopReason::Exited(0);
                } else {
                    stop_reason = StopReason::Exited(1);
                }
            }
        }

        #[allow(clippy::collapsible_if)]
        if stop_reason != StopReason::Eof {
            if !continue_if_modified(&*program.borrow(), &mut *console.borrow_mut()).await? {
                console.borrow_mut().print("Exit aborted; resuming REPL loop.")?;
                stop_reason = StopReason::Eof;
            }
        }
    }
    Ok(stop_reason.as_exit_code())
}

#[cfg(test)]
mod tests {
    use super::*;
    use endbasic_std::storage::{Drive, DriveFactory, InMemoryDrive};
    use endbasic_std::testutils::*;
    use futures_lite::future::block_on;

    #[test]
    fn test_autoexec_ok() {
        // The code in the autoexec test file should access, in a mutable fashion, all the resources
        // that the try_load_autoexec function uses to ensure the function's code doesn't hold onto
        // references while executing the autoexec code and causing a borrowing violation.
        let autoexec = "PRINT \"hello\": global_var = 3: CD \"MEMORY:/\"";
        let mut tester = Tester::default().write_file("AUTOEXEC.BAS", autoexec);
        let (console, storage) = (tester.get_console(), tester.get_storage());
        block_on(try_load_autoexec(tester.get_machine(), console, storage)).unwrap();
        tester
            .run("")
            .expect_var("global_var", 3)
            .expect_prints(["Loading AUTOEXEC.BAS...", "hello"])
            .expect_file("MEMORY:/AUTOEXEC.BAS", autoexec)
            .check();
    }

    #[test]
    fn test_autoexec_error_is_ignored() {
        let autoexec = "a = 1\nb = undef: c = 2";
        let mut tester = Tester::default().write_file("AUTOEXEC.BAS", autoexec);
        let (console, storage) = (tester.get_console(), tester.get_storage());
        block_on(try_load_autoexec(tester.get_machine(), console, storage)).unwrap();
        tester
            .run("after = 5")
            .expect_var("a", 1)
            .expect_var("after", 5)
            .expect_prints([
                "Loading AUTOEXEC.BAS...",
                "AUTOEXEC.BAS failed: 2:5: Undefined variable undef",
            ])
            .expect_file("MEMORY:/AUTOEXEC.BAS", autoexec)
            .check();
    }

    #[test]
    fn test_autoexec_name_is_case_sensitive() {
        let mut tester = Tester::default()
            .write_file("AUTOEXEC.BAS", "a = 1")
            .write_file("autoexec.bas", "a = 2");
        let (console, storage) = (tester.get_console(), tester.get_storage());
        block_on(try_load_autoexec(tester.get_machine(), console, storage)).unwrap();
        tester
            .run("")
            .expect_var("a", 1)
            .expect_prints(["Loading AUTOEXEC.BAS..."])
            .expect_file("MEMORY:/AUTOEXEC.BAS", "a = 1")
            .expect_file("MEMORY:/autoexec.bas", "a = 2")
            .check();
    }

    #[test]
    fn test_autoexec_missing() {
        let mut tester = Tester::default();
        let (console, storage) = (tester.get_console(), tester.get_storage());
        block_on(try_load_autoexec(tester.get_machine(), console, storage)).unwrap();
        tester.run("").check();
    }

    /// Factory for drives that mimic the behavior of a cloud drive with fixed contents.
    struct MockDriveFactory {
        exp_username: &'static str,
        exp_file: &'static str,
    }

    impl MockDriveFactory {
        /// Verbatim contents of the single file included in the mock drives.
        const SCRIPT: &'static str = r#"PRINT "Success""#;
    }

    impl DriveFactory for MockDriveFactory {
        fn create(&self, target: &str) -> io::Result<Box<dyn Drive>> {
            let mut drive = InMemoryDrive::default();
            block_on(drive.put(self.exp_file, Self::SCRIPT)).unwrap();
            assert_eq!(self.exp_username, target);
            Ok(Box::from(drive))
        }
    }

    #[test]
    fn test_run_from_cloud_no_repl() {
        let mut tester = Tester::default();
        let (console, storage, program) =
            (tester.get_console(), tester.get_storage(), tester.get_program());

        storage.borrow_mut().register_scheme(
            "cloud",
            Box::from(MockDriveFactory { exp_username: "foo", exp_file: "bar.bas" }),
        );

        block_on(run_from_cloud(
            tester.get_machine(),
            console,
            storage,
            program,
            "foo/bar.bas",
            false,
        ))
        .unwrap();
        tester
            .run("")
            .expect_prints([
                "Mounting cloud://foo as AUTORUN...",
                "Loading AUTORUN:/bar.bas...",
                "Starting...",
                "",
            ])
            .expect_clear()
            .expect_prints(["Success", "", "**** Program exited due to EOF ****"])
            .expect_program(Some("AUTORUN:/bar.bas"), MockDriveFactory::SCRIPT)
            .check();
    }

    #[test]
    fn test_run_from_cloud_repl() {
        let mut tester = Tester::default();
        let (console, storage, program) =
            (tester.get_console(), tester.get_storage(), tester.get_program());

        storage.borrow_mut().register_scheme(
            "cloud",
            Box::from(MockDriveFactory { exp_username: "abcd", exp_file: "the-path.bas" }),
        );

        block_on(run_from_cloud(
            tester.get_machine(),
            console,
            storage,
            program,
            "abcd/the-path.bas",
            true,
        ))
        .unwrap();
        let mut checker = tester.run("");
        let output = flatten_output(checker.take_captured_out());
        checker.expect_program(Some("AUTORUN:/the-path.bas"), MockDriveFactory::SCRIPT).check();

        assert!(output.contains("You are now being dropped into"));
    }
}
