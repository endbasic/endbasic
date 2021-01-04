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

use endbasic_core::exec::StopReason;
use endbasic_std::console::{self, Console};
use endbasic_std::store::Store;
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

pub mod demos;

/// Enters the interactive interpreter.
///
/// `dir` specifies the directory that the interpreter will use for any commands that manipulate
/// files.
pub async fn run_repl_loop(
    console: Rc<RefCell<dyn Console>>,
    store: Rc<RefCell<dyn Store>>,
) -> io::Result<i32> {
    let mut machine = endbasic_std::interactive_machine_builder(console.clone(), store).build();

    {
        let mut console = console.borrow_mut();
        console.print("")?;
        console.print(&format!("    Welcome to EndBASIC {}.", env!("CARGO_PKG_VERSION")))?;
        console.print("")?;
        console.print("    Type HELP for interactive usage information.")?;
        console.print("    Type LOAD \"DEMO:TOUR.BAS\": RUN for a guided tour.")?;
        console.print("")?;
    }

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
