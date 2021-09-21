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
use endbasic_std::console::{self, Console};
use endbasic_std::storage::Storage;
use std::cell::RefCell;
use std::io;
use std::path::Path;
use std::rc::Rc;
use std::str::FromStr;

pub mod demos;

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
                    break;
                } else {
                    stop_reason = StopReason::Exited(1);
                }
            }
        }
    }
    Ok(stop_reason.as_exit_code())
}

/// Wrapper over `str::parse` to return `io::Result` with a custom `error` message.
fn parse_str<T: FromStr>(text: &str, error: &'static str) -> io::Result<T> {
    match text.parse::<T>() {
        Ok(value) => Ok(value),
        Err(_) => Err(io::Error::new(io::ErrorKind::InvalidInput, error)),
    }
}

/// Parses a graphical `resolution` of the form `WIDTHxHEIGHT`.
fn parse_resolution(resolution: &str) -> io::Result<(u32, u32)> {
    let resolution: Vec<&str> = resolution.split('x').collect();
    match resolution.as_slice() {
        [width, height] => {
            let width = parse_str(width, "Invalid width in resolution")?;
            let height = parse_str(height, "Invalid height in resolution")?;
            Ok((width, height))
        }
        _ => Err(io::Error::new(io::ErrorKind::InvalidInput, "Invalid resolution format")),
    }
}

/// Parses a graphical console specification.
pub fn parse_graphics_spec(params: &str) -> io::Result<(u32, u32, &Path, u16)> {
    let invalid_spec =
        Err(io::Error::new(io::ErrorKind::InvalidInput, "Invalid graphics console spec"));
    let mut params = params.split(',');
    let resolution = match params.next() {
        Some(resolution) => resolution,
        None => return invalid_spec,
    };
    let font_path = match params.next() {
        Some(font_path) => font_path,
        None => return invalid_spec,
    };
    let font_size = match params.next() {
        Some(font_size) => font_size,
        None => return invalid_spec,
    };
    if params.next().is_some() {
        return invalid_spec;
    }

    let (width, height) = parse_resolution(resolution)?;
    let font_path = Path::new(font_path);
    let font_size = parse_str(font_size, "Invalid font size")?;
    Ok((width, height, font_path, font_size))
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

    #[test]
    fn test_parse_graphics_spec_ok() {
        let spec = parse_graphics_spec("800x600,/path/to/font.ttf,16").unwrap();
        assert_eq!(800, spec.0);
        assert_eq!(600, spec.1);
        assert_eq!(Path::new("/path/to/font.ttf"), spec.2);
        assert_eq!(16, spec.3);
    }

    #[test]
    fn test_parse_graphics_spec_errors() {
        fn check(exp_error: &str, s: &str) {
            assert_eq!(exp_error, format!("{}", parse_graphics_spec(s).unwrap_err()));
        }
        check("Invalid graphics console spec", "abc");
        check("Invalid graphics console spec", "800x600");
        check("Invalid graphics console spec", "800x600,font.ttf");
        check("Invalid graphics console spec", "800x600,font.ttf,16,abc");
        check("Invalid resolution format", "a,font.ttf,16");
        check("Invalid width in resolution", "ax100,font.ttf,16");
        check("Invalid height in resolution", "100xa,font.ttf,16");
        check("Invalid font size", "100x200,font.ttf,a");
    }
}
