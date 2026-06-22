// EndBASIC
// Copyright 2020 Julio Merino
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

//! Interactive interpreter for the EndBASIC language.

use endbasic_std::console::{self, Console, PixelsXY, is_narrow, refill_and_print};
use endbasic_std::program::{BREAK_MSG, Program, continue_if_modified};
use endbasic_std::storage::Storage;
use endbasic_std::{Error as StdError, Machine};
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

pub mod demos;
pub mod editor;
mod logo;

/// Prints the EndBASIC welcome message to a wide console, with optional extra indentation to
/// leave space for the logo.
fn print_wide_welcome(console: &mut dyn Console, extra_indent: &str) -> io::Result<()> {
    console.print("")?;
    console.print(&format!("    {}EndBASIC {}", extra_indent, env!("CARGO_PKG_VERSION")))?;
    console.print(&format!("    {}Copyright 2020-2026 Julio Merino", extra_indent))?;
    console.print("")?;
    console.print("    Type HELP for interactive usage information.")
}

/// Prints the EndBASIC welcome message to a graphical console.
fn print_graphical_welcome(console: &mut dyn Console) -> io::Result<()> {
    let glyph_size = console.glyph_size()?;

    let previous_sync = console.set_sync(false)?;
    let result = (|| {
        print_wide_welcome(console, "     ")?;

        let x1 = i32::from(glyph_size.width) * 4;
        let x2 = i32::from(glyph_size.width) * 8;
        let y1 = i32::from(glyph_size.height) / 2;
        let y2 = i32::from(glyph_size.height) * 7 / 2;
        logo::draw_logo(
            console,
            PixelsXY::new(x1 as i16, y1 as i16),
            Some(PixelsXY::new(x2 as i16, y2 as i16)),
        )?;

        Ok(())
    })();
    console.set_sync(previous_sync)?;
    result
}

/// Checks if the given `console` has graphics support.
fn has_graphics(console: &dyn Console) -> bool {
    console.size_pixels().is_ok() && console.glyph_size().is_ok()
}

/// Prints the EndBASIC welcome message to the given console.
pub fn print_welcome(console: &mut dyn Console) -> io::Result<()> {
    if is_narrow(&*console) {
        console.print(&format!("EndBASIC {}", env!("CARGO_PKG_VERSION")))?;
    } else if has_graphics(&*console) {
        print_graphical_welcome(&mut *console)?;
    } else {
        print_wide_welcome(console, "")?;
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

    match machine.compile(&mut code.as_slice()) {
        Ok(()) => match machine.exec().await {
            Ok(_) => Ok(()),
            Err(e) => {
                console.borrow_mut().print(&format!("AUTOEXEC.BAS failed: {}", e))?;
                Ok(())
            }
        },
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
    let content = match String::from_utf8(content) {
        Ok(text) => text,
        Err(e) => {
            let mut console = console.borrow_mut();
            console.print(&format!("Invalid program to run '{}': {}", path, e))?;
            return Ok(1);
        }
    };
    program.borrow_mut().load(Some(&path), &content);

    console.borrow_mut().print("Starting...")?;
    console.borrow_mut().print("")?;

    if let Err(e) = machine.compile(&mut "RUN".as_bytes()) {
        let mut console = console.borrow_mut();
        console.print(&format!("**** ERROR: {} ****", e))?;
        return Ok(1);
    }

    let result = machine.exec().await;

    let mut console = console.borrow_mut();

    console.print("")?;
    let code = match result {
        Ok(None) => {
            console.print("**** Program exited due to EOF ****")?;
            0
        }
        Ok(Some(code)) => {
            console.print(&format!("**** Program exited with code {} ****", code))?;
            code
        }
        Err(StdError::Break) => {
            console.print("**** Program stopped due to BREAK ****")?;
            130
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
    let mut stop_reason = None;
    let mut history = vec![];
    while stop_reason.is_none() {
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
            Ok(line) => match machine.compile(&mut line.as_bytes()) {
                Ok(()) => match machine.exec().await {
                    Ok(None) => stop_reason = None,
                    Ok(Some(code)) => {
                        let should_continue = {
                            let program = program.borrow();
                            let mut console = console.borrow_mut();
                            continue_if_modified(&*program, &mut *console).await?
                        };
                        if should_continue {
                            stop_reason = Some(code);
                        } else {
                            let mut console = console.borrow_mut();
                            console.print("Exit aborted; resuming REPL loop.")?;
                        }
                    }
                    Err(StdError::Break) => {
                        let mut console = console.borrow_mut();
                        console.print(BREAK_MSG)?;
                    }
                    Err(e) => {
                        let mut console = console.borrow_mut();
                        console.print(format!("ERROR: {}", e).as_str())?;
                    }
                },
                Err(e) => {
                    let mut console = console.borrow_mut();
                    console.print(format!("ERROR: {}", e).as_str())?;
                }
            },
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
                    stop_reason = Some(0);
                } else {
                    stop_reason = Some(1);
                }
            }
        }
    }
    Ok(stop_reason.unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;
    use endbasic_sdl::testutils::SdlTest;
    use endbasic_std::Signal;
    use endbasic_std::console::{CharsXY, Key};
    use endbasic_std::gfx::lcd::fonts::{FONT_5X8, FONT_16X16};
    use endbasic_std::storage::{Drive, DriveFactory, InMemoryDrive};
    use endbasic_std::testutils::*;
    use futures_lite::future::block_on;

    /// Runs `print_welcome` against a console that is `console_width` in height and returns
    /// whether the narrow welcome message was printed or not, and the maximum width of all
    /// printed messages.
    fn check_is_narrow_welcome(console_width: u16) -> (bool, usize) {
        let console = Rc::from(RefCell::from(MockConsole::default()));
        console.borrow_mut().set_size_chars(CharsXY::new(console_width, 1));
        print_welcome(&mut *console.borrow_mut()).unwrap();

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
    #[ignore = "Requires a graphical environment"]
    fn test_print_welcome_draw_logo_default() {
        let mut test = SdlTest::default();
        print_welcome(test.console()).unwrap();
        test.verify("repl/src", "welcome-banner-default");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_print_welcome_draw_logo_tiny() {
        let mut test = SdlTest::new(800, 600, &FONT_5X8);
        print_welcome(test.console()).unwrap();
        test.verify("repl/src", "welcome-banner-tiny");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_print_welcome_draw_logo_big() {
        let mut test = SdlTest::new(800, 600, &FONT_16X16);
        print_welcome(test.console()).unwrap();
        test.verify("repl/src", "welcome-banner-big");
    }

    #[test]
    fn test_autoexec_ok() {
        // The code in the autoexec test file should access, in a mutable fashion, all the resources
        // that the try_load_autoexec function uses to ensure the function's code doesn't hold onto
        // references while executing the autoexec code and causing a borrowing violation.
        let autoexec = "PRINT \"hello\": global_var = 3: CD \"MEMORY:/\"";
        let tester = Tester::default().write_file("AUTOEXEC.BAS", autoexec);
        let (console, storage) = (tester.get_console(), tester.get_storage());
        let mut continuation = tester.continue_from_here();
        block_on(try_load_autoexec(continuation.get_machine(), console, storage)).unwrap();
        continuation
            .run("")
            .expect_prints(["hello"])
            .expect_file("MEMORY:/AUTOEXEC.BAS", autoexec)
            .check();
    }

    #[test]
    fn test_autoexec_compilation_error_is_ignored() {
        let autoexec = "a = 1\nb = undef: c = 2";
        let tester = Tester::default().write_file("AUTOEXEC.BAS", autoexec);
        let (console, storage) = (tester.get_console(), tester.get_storage());
        let mut continuation = tester.continue_from_here();
        block_on(try_load_autoexec(continuation.get_machine(), console, storage)).unwrap();
        continuation
            .run("after = 5")
            .expect_var("after", 5)
            .expect_prints(["AUTOEXEC.BAS failed: 2:5: Undefined symbol undef"])
            .expect_file("MEMORY:/AUTOEXEC.BAS", autoexec)
            .check();
    }

    #[test]
    fn test_autoexec_execution_error_is_ignored() {
        let autoexec = "a = 1\nb = 3 >> -1: c = 2";
        let tester = Tester::default().write_file("AUTOEXEC.BAS", autoexec);
        let (console, storage) = (tester.get_console(), tester.get_storage());
        let mut continuation = tester.continue_from_here();
        block_on(try_load_autoexec(continuation.get_machine(), console, storage)).unwrap();
        continuation
            .run("after = 5")
            .expect_prints(["AUTOEXEC.BAS failed: 2:7: Number of bits to >> (-1) must be positive"])
            .expect_file("MEMORY:/AUTOEXEC.BAS", autoexec)
            .check();
    }

    #[test]
    fn test_autoexec_name_is_case_sensitive() {
        let tester = Tester::default()
            .write_file("AUTOEXEC.BAS", "a = 1")
            .write_file("autoexec.bas", "a = 2");
        let (console, storage) = (tester.get_console(), tester.get_storage());
        let mut continuation = tester.continue_from_here();
        block_on(try_load_autoexec(continuation.get_machine(), console, storage)).unwrap();
        continuation
            .run("")
            .expect_file("MEMORY:/AUTOEXEC.BAS", "a = 1")
            .expect_file("MEMORY:/autoexec.bas", "a = 2")
            .check();
    }

    #[test]
    fn test_autoexec_missing() {
        let tester = Tester::default();
        let (console, storage) = (tester.get_console(), tester.get_storage());
        let mut continuation = tester.continue_from_here();
        block_on(try_load_autoexec(continuation.get_machine(), console, storage)).unwrap();
        continuation.run("").check();
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
            block_on(drive.put(self.exp_file, Self::SCRIPT.as_bytes())).unwrap();
            assert_eq!(self.exp_username, target);
            Ok(Box::from(drive))
        }
    }

    #[test]
    fn test_run_from_cloud_no_repl() {
        let tester = Tester::default();
        let (console, storage, program) =
            (tester.get_console(), tester.get_storage(), tester.get_program());
        let mut continuation = tester.continue_from_here();

        storage.borrow_mut().register_scheme(
            "cloud",
            Box::from(MockDriveFactory { exp_username: "foo", exp_file: "bar.bas" }),
        );

        block_on(run_from_cloud(
            continuation.get_machine(),
            console,
            storage,
            program,
            "foo/bar.bas",
            false,
        ))
        .unwrap();
        continuation
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
        let tester = Tester::default();
        let (console, storage, program) =
            (tester.get_console(), tester.get_storage(), tester.get_program());
        let mut continuation = tester.continue_from_here();

        storage.borrow_mut().register_scheme(
            "cloud",
            Box::from(MockDriveFactory { exp_username: "abcd", exp_file: "the-path.bas" }),
        );

        block_on(run_from_cloud(
            continuation.get_machine(),
            console,
            storage,
            program,
            "abcd/the-path.bas",
            true,
        ))
        .unwrap();
        let mut checker = continuation.run("");
        let output = flatten_output(checker.take_captured_out());
        checker.expect_program(Some("AUTORUN:/the-path.bas"), MockDriveFactory::SCRIPT).check();

        assert!(output.contains("You are now being dropped into"));
    }

    #[test]
    fn test_run_repl_loop_signal_before_exec() {
        let mut tester = Tester::default();
        let (console, program) = (tester.get_console(), tester.get_program());
        let (signals_tx, signals_rx) = async_channel::unbounded();
        let mut machine = endbasic_std::MachineBuilder::default()
            .with_console(console.clone())
            .with_signals_chan((signals_tx.clone(), signals_rx))
            .build();

        {
            let mut console = console.borrow_mut();
            console.add_input_chars("PRINT");
            block_on(signals_tx.send(Signal::Break)).unwrap();
            console.add_input_chars(" 123");
            console.add_input_keys(&[Key::NewLine, Key::EofOrDelete]);
        }
        block_on(run_repl_loop(&mut machine, console, program)).unwrap();
        tester.run("").expect_prints([" 123", "End of input by CTRL-D"]).check();
    }

    #[test]
    fn test_run_repl_loop_eof_during_input_does_not_exit_repl() {
        let mut tester = Tester::default();
        let (console, program) = (tester.get_console(), tester.get_program());
        let mut machine =
            endbasic_std::MachineBuilder::default().with_console(console.clone()).build();

        {
            let mut console = console.borrow_mut();
            console.add_input_chars("INPUT a\n");
            console.add_input_keys(&[Key::EofOrDelete]);
            console.add_input_chars("PRINT 3\n");
            console.add_input_keys(&[Key::EofOrDelete]);
        }
        block_on(run_repl_loop(&mut machine, console, program)).unwrap();
        tester.run("").expect_prints(["ERROR: 1:1: EOF", " 3", "End of input by CTRL-D"]).check();
    }
}
