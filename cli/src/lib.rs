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
#[cfg(feature = "sdl")]
use endbasic_sdl::SdlConsole;
use endbasic_std::console::{self, Console};
use endbasic_std::program::{continue_if_modified, Program};
use endbasic_std::storage::Storage;
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

pub mod demos;
#[cfg(feature = "sdl")]
mod sdl;

/// Prints the EndBASIC welcome message to the given console.
pub fn print_welcome(console: Rc<RefCell<dyn Console>>) -> io::Result<()> {
    let mut console = console.borrow_mut();
    console.print("")?;
    console.print(&format!("    Welcome to EndBASIC {}.", env!("CARGO_PKG_VERSION")))?;
    console.print("")?;
    console.print("    Type HELP for interactive usage information.")?;
    console.print("    For a guided tour, type: LOAD \"DEMOS:/TOUR.BAS\": RUN")?;
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

/// Creates the graphical console when SDL support is built in.
#[cfg(feature = "sdl")]
pub fn setup_graphics_console(spec: &str) -> io::Result<Rc<RefCell<dyn Console>>> {
    let spec = sdl::parse_graphics_spec(spec)?;
    let console = match spec.1 {
        None => {
            let default_font = sdl::TempFont::default_font()?;
            SdlConsole::new(spec.0, &default_font.path(), spec.2)?
            // The console has been created at this point, so it should be safe to drop
            // default_font and clean up the on-disk file backing it up.
        }
        Some(font_path) => SdlConsole::new(spec.0, font_path, spec.2)?,
    };
    Ok(Rc::from(RefCell::from(console)))
}

/// Errors out during the creation of the graphical console when SDL support is not compiled in.
#[cfg(not(feature = "sdl"))]
pub fn setup_graphics_console(_spec: &str) -> io::Result<Rc<RefCell<dyn Console>>> {
    // TODO(jmmv): Make this io::ErrorKind::Unsupported when our MSRV allows it.
    Err(io::Error::new(io::ErrorKind::InvalidInput, "SDL support not compiled in"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use endbasic_std::testutils::Tester;
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
        let autoexec = "a = 1: b = undef: c = 2";
        let mut tester = Tester::default().write_file("AUTOEXEC.BAS", autoexec);
        let (console, storage) = (tester.get_console(), tester.get_storage());
        block_on(try_load_autoexec(tester.get_machine(), console, storage)).unwrap();
        tester
            .run("after = 5")
            .expect_var("a", 1)
            .expect_var("after", 5)
            .expect_prints([
                "Loading AUTOEXEC.BAS...",
                "AUTOEXEC.BAS failed: Undefined variable undef",
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
}
