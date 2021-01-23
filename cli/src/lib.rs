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
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(unused, unused_extern_crates, unused_import_braces, unused_qualifications)]
#![warn(unsafe_code)]

use endbasic_core::exec::{Machine, StopReason};
use endbasic_std::console::{self, Console};
use endbasic_std::store::Store;
use futures_lite::future::block_on;
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

pub mod demos;

/// Prints the EndBASIC welcome message to the given console.
pub fn print_welcome(console: Rc<RefCell<dyn Console>>) -> io::Result<()> {
    let mut console = console.borrow_mut();
    console.print("")?;
    console.print(&format!("    Welcome to EndBASIC {}.", env!("CARGO_PKG_VERSION")))?;
    console.print("")?;
    console.print("    Type HELP for interactive usage information.")?;
    console.print("    Type LOAD \"DEMO:TOUR.BAS\": RUN for a guided tour.")?;
    console.print("")?;
    Ok(())
}

/// Loads the `AUTOEXEC.BAS` file if it exists in the `store`.
///
/// Failures to process the file are logged to the `console` but are ignored.  Other failures are
/// returned.
pub fn try_load_autoexec(
    machine: &mut Machine,
    console: Rc<RefCell<dyn Console>>,
    store: Rc<RefCell<dyn Store>>,
) -> io::Result<()> {
    match store.borrow().get("AUTOEXEC.BAS") {
        Ok(code) => {
            console.borrow_mut().print("Loading AUTOEXEC.BAS...")?;
            match block_on(machine.exec(&mut code.as_bytes())) {
                Ok(_) => Ok(()),
                Err(e) => {
                    console.borrow_mut().print(&format!("AUTOEXEC.BAS failed: {}", e))?;
                    Ok(())
                }
            }
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(e) => {
            console.borrow_mut().print(&format!("AUTOEXEC.BAS exists but cannot be read: {}", e))
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
) -> io::Result<i32> {
    let mut stop_reason = StopReason::Eof;
    while stop_reason == StopReason::Eof {
        let line = {
            let mut console = console.borrow_mut();
            if console.is_interactive() {
                console.print("Ready")?;
            }
            console::read_line(&mut *console, "", "").await
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
                    break;
                } else {
                    stop_reason = StopReason::Exited(1);
                }
            }
        }
    }
    Ok(stop_reason.as_exit_code())
}

#[cfg(test)]
mod tests {
    use super::*;
    use endbasic_std::testutils::Tester;

    #[test]
    fn test_autoexec_ok() {
        let autoexec = "PRINT \"hello\": global_var = 3";
        let mut tester = Tester::default().write_file("AUTOEXEC.BAS", autoexec);
        let (console, store) = (tester.get_console(), tester.get_store());
        try_load_autoexec(tester.get_machine(), console, store).unwrap();
        tester
            .run("")
            .expect_var("global_var", 3)
            .expect_prints(["Loading AUTOEXEC.BAS...", "hello"])
            .expect_file("AUTOEXEC.BAS", autoexec)
            .check();
    }

    #[test]
    fn test_autoexec_error_is_ignored() {
        let autoexec = "a = 1: b = undef: c = 2";
        let mut tester = Tester::default().write_file("AUTOEXEC.BAS", autoexec);
        let (console, store) = (tester.get_console(), tester.get_store());
        try_load_autoexec(tester.get_machine(), console, store).unwrap();
        tester
            .run("after = 5")
            .expect_var("a", 1)
            .expect_var("after", 5)
            .expect_prints([
                "Loading AUTOEXEC.BAS...",
                "AUTOEXEC.BAS failed: Undefined variable undef",
            ])
            .expect_file("AUTOEXEC.BAS", autoexec)
            .check();
    }

    #[test]
    fn test_autoexec_name_is_case_sensitive() {
        let mut tester = Tester::default()
            .write_file("AUTOEXEC.BAS", "a = 1")
            .write_file("autoexec.bas", "a = 2");
        let (console, store) = (tester.get_console(), tester.get_store());
        try_load_autoexec(tester.get_machine(), console, store).unwrap();
        tester
            .run("")
            .expect_var("a", 1)
            .expect_prints(["Loading AUTOEXEC.BAS..."])
            .expect_file("AUTOEXEC.BAS", "a = 1")
            .expect_file("autoexec.bas", "a = 2")
            .check();
    }

    #[test]
    fn test_autoexec_missing() {
        let mut tester = Tester::default();
        let (console, store) = (tester.get_console(), tester.get_store());
        try_load_autoexec(tester.get_machine(), console, store).unwrap();
        tester.run("").check();
    }
}
