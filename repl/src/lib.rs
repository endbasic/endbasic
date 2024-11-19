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

use endbasic_core::exec::{InternalStopReason, Machine, StopReason};
use endbasic_std::console::{self, is_narrow, refill_and_print, Console};
use endbasic_std::program::{continue_if_modified, Program};
use endbasic_std::storage::Storage;
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

pub mod demos;
pub mod editor;

/// Message to print on the console when receiving a break signal.
const BREAK_MSG: &str = "**** BREAK ****";

/// Prints the EndBASIC welcome message to the given console.
pub fn print_welcome(console: Rc<RefCell<dyn Console>>) -> io::Result<()> {
    let mut console = console.borrow_mut();

    if is_narrow(&*console) {
        console.print(&format!("EndBASIC {}", env!("CARGO_PKG_VERSION")))?;
    } else {
        console.print("")?;
        console.print(&format!("    EndBASIC {}", env!("CARGO_PKG_VERSION")))?;
        console.print("    Copyright 2020-2024 Julio Merino")?;
        console.print("")?;
        console.print("    Type HELP for interactive usage information.")?;
    }
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
    let mut context = match machine.compile(&mut code.as_bytes()) {
        Ok(context) => context,
        Err(e) => {
            console.borrow_mut().print(&format!("AUTOEXEC.BAS failed: {}", e))?;
            return Ok(());
        }
    };
    match machine.exec(&mut context).await {
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
) -> io::Result<i32> {
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

    let mut context =
        machine.compile(&mut "RUN".as_bytes()).expect("Compilation of hardcoded code must succeed");
    let result = machine.exec(&mut context).await;

    let mut console = console.borrow_mut();

    console.print("")?;
    let code = match result {
        Ok(r @ StopReason::Eof) => {
            console.print("**** Program exited due to EOF ****")?;
            r.as_exit_code()
        }
        Ok(r @ StopReason::Exited(_code, _is_final)) => {
            let code = r.as_exit_code();
            console.print(&format!("**** Program exited with code {} ****", code))?;
            code
        }
        Ok(r @ StopReason::Break(_is_final)) => {
            console.print("**** Program stopped due to BREAK ****")?;
            r.as_exit_code()
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

        // Any signals entered during console input should not impact upcoming execution.  Drain
        // them all.
        machine.drain_signals();

        match line {
            Ok(line) => {
                let mut context = match machine.compile(&mut line.as_bytes()) {
                    Ok(context) => context,
                    Err(e) => {
                        let mut console = console.borrow_mut();
                        console.print(format!("ERROR: {}", e).as_str())?;
                        continue;
                    }
                };

                loop {
                    match machine.resume(&mut context).await {
                        Ok(InternalStopReason::CheckStop(is_final)) => {
                            if machine.should_stop().await {
                                stop_reason = StopReason::Break(is_final);
                                break;
                            }
                        }
                        Ok(InternalStopReason::Upcall(data)) => {
                            if let Err(e) = machine.handle_upcall(&mut context, &data).await {
                                let mut console = console.borrow_mut();
                                console.print(format!("ERROR: {}", e).as_str())?;
                                break;
                            }
                        }
                        Ok(InternalStopReason::Eof) => {
                            stop_reason = StopReason::Eof;
                            break;
                        }
                        Ok(InternalStopReason::Exited(code, is_final)) => {
                            stop_reason = StopReason::Exited(code, is_final);
                            break;
                        }
                        Err(e) => {
                            let mut console = console.borrow_mut();
                            console.print(format!("ERROR: {}", e).as_str())?;
                            break;
                        }
                    }
                }
            }
            Err(e) => {
                if e.kind() == io::ErrorKind::Interrupted {
                    let mut console = console.borrow_mut();
                    console.print(BREAK_MSG)?;
                    // Do not exit the interpreter.  Other REPLs, such as Python's, do not do so,
                    // and it is actually pretty annoying to exit the REPL when one may be furiously
                    // pressing CTRL+C to stop a program inside of it.
                } else if e.kind() == io::ErrorKind::UnexpectedEof {
                    let mut console = console.borrow_mut();
                    console.print("End of input by CTRL-D")?;
                    stop_reason = StopReason::Exited(0, true);
                } else {
                    stop_reason = StopReason::Exited(1, true);
                }
            }
        }

        match stop_reason {
            StopReason::Eof => (),
            StopReason::Break(_is_final) => {
                console.borrow_mut().print("**** BREAK ****")?;
                stop_reason = StopReason::Eof;
            }
            StopReason::Exited(_, false) => {
                console
                    .borrow_mut()
                    .print(&format!("Program exited with code {}", stop_reason.as_exit_code()))?;
                stop_reason = StopReason::Eof;
            }
            StopReason::Exited(_, true) => {
                if !continue_if_modified(&*program.borrow(), &mut *console.borrow_mut()).await? {
                    console.borrow_mut().print("Exit aborted; resuming REPL loop.")?;
                    stop_reason = StopReason::Eof;
                }
            }
        }
    }
    Ok(stop_reason.as_exit_code())
}

#[cfg(test)]
mod tests {
    use super::*;
    use endbasic_core::exec::Signal;
    use endbasic_std::console::{CharsXY, Key};
    use endbasic_std::storage::{Drive, DriveFactory, InMemoryDrive};
    use endbasic_std::testutils::*;
    use futures_lite::future::block_on;
    use std::convert::TryFrom;

    /// Runs `print_welcome` against a console that is `console_width` in height and returns
    /// whether the narrow welcome message was printed or not, and the maximum width of all
    /// printed messages.
    fn check_is_narrow_welcome(console_width: u16) -> (bool, usize) {
        let console = Rc::from(RefCell::from(MockConsole::default()));
        console.borrow_mut().set_size_chars(CharsXY::new(console_width, 1));
        print_welcome(console.clone()).unwrap();

        let mut console = console.borrow_mut();
        let mut found = false;
        let mut max_length = 0;
        for output in console.take_captured_out() {
            match output {
                CapturedOut::Print(msg) => {
                    if msg.contains("Type HELP") {
                        found = true;
                        max_length = std::cmp::max(max_length, msg.len());
                    }
                }
                _ => panic!("Unexpected console operation: {:?}", output),
            }
        }
        (!found, max_length)
    }

    #[test]
    fn test_print_welcome_wide_console() {
        assert!(!check_is_narrow_welcome(50).0, "Long welcome not found");
    }

    #[test]
    fn test_print_welcome_narrow_console() {
        assert!(check_is_narrow_welcome(10).0, "Long welcome found");
    }

    #[test]
    fn test_print_welcome_and_is_narrow_agree() {
        let (narrow, max_length) = check_is_narrow_welcome(1000);
        assert!(!narrow, "Long message not found");

        for i in 0..max_length {
            assert!(check_is_narrow_welcome(u16::try_from(i).unwrap()).0, "Long message found");
        }
    }

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
    fn test_autoexec_compilation_error_is_ignored() {
        let autoexec = "a = 1\nb = undef: c = 2";
        let mut tester = Tester::default().write_file("AUTOEXEC.BAS", autoexec);
        let (console, storage) = (tester.get_console(), tester.get_storage());
        block_on(try_load_autoexec(tester.get_machine(), console, storage)).unwrap();
        tester
            .run("after = 5")
            .expect_var("after", 5)
            .expect_prints([
                "Loading AUTOEXEC.BAS...",
                "AUTOEXEC.BAS failed: 2:5: Undefined symbol UNDEF",
            ])
            .expect_file("MEMORY:/AUTOEXEC.BAS", autoexec)
            .check();
    }

    #[test]
    fn test_autoexec_execution_error_is_ignored() {
        let autoexec = "a = 1\nb = 3 >> -1: c = 2";
        let mut tester = Tester::default().write_file("AUTOEXEC.BAS", autoexec);
        let (console, storage) = (tester.get_console(), tester.get_storage());
        block_on(try_load_autoexec(tester.get_machine(), console, storage)).unwrap();
        tester
            .run("after = 5")
            .expect_var("a", 1)
            .expect_var("after", 5)
            .expect_prints([
                "Loading AUTOEXEC.BAS...",
                "AUTOEXEC.BAS failed: 2:7: Number of bits to >> (-1) must be positive",
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

    #[test]
    fn test_run_repl_loop_signal_before_exec() {
        let mut tester = Tester::default();
        let (console, program) = (tester.get_console(), tester.get_program());
        let signals_tx = tester.get_machine().get_signals_tx();

        {
            let mut console = console.borrow_mut();
            console.add_input_chars("PRINT");
            block_on(signals_tx.send(Signal::Break)).unwrap();
            console.add_input_chars(" 123");
            console.add_input_keys(&[Key::NewLine, Key::Eof]);
        }
        block_on(run_repl_loop(tester.get_machine(), console, program)).unwrap();
        tester.run("").expect_prints([" 123", "End of input by CTRL-D"]).check();
    }
}
