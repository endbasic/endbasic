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

//! Web interface for the EndBASIC language.

// Keep these in sync with other top-level files.
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(unused, unused_extern_crates, unused_import_braces, unused_qualifications)]
#![warn(unsafe_code)]

use async_trait::async_trait;
use endbasic_core::console::Console;
use std::cell::RefCell;
use std::io;
use std::rc::Rc;
use wasm_bindgen::prelude::*;

/// Implementation of a console that talks directly to an xterm.js terminal.
struct XtermJsConsole {
    terminal: xterm_js_rs::Terminal,
}

#[async_trait(?Send)]
impl Console for XtermJsConsole {
    fn clear(&mut self) -> io::Result<()> {
        self.terminal.write("\u{001b}[2J");
        self.terminal.write("\u{001b}[0;0H");
        Ok(())
    }

    fn color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()> {
        if let Some(fg) = fg {
            self.terminal.write(&format!("\u{001b}[38;5;{}m", fg));
        }
        if let Some(bg) = bg {
            self.terminal.write(&format!("\u{001b}[48;5;{}m", bg));
        }
        self.terminal.write("\u{001b}[0K");
        Ok(())
    }

    async fn input(&mut self, _prompt: &str, _previous: &str) -> io::Result<String> {
        Err(io::Error::new(io::ErrorKind::Other, "Not yet implemented"))
    }

    fn locate(&mut self, row: usize, column: usize) -> io::Result<()> {
        self.terminal.write(&format!("\u{001b}[{};{}H", row, column));
        Ok(())
    }

    fn print(&mut self, text: &str) -> io::Result<()> {
        self.terminal.write(text);
        self.terminal.write("\n\r");
        Ok(())
    }
}

/// Backend for the web-based interactive EndBASIC interpreter.
#[wasm_bindgen]
pub struct Interpreter {
    machine: endbasic_core::exec::Machine,
}

#[wasm_bindgen]
impl Interpreter {
    /// Constructs a new interpreter attached to `terminal` for console output.
    #[wasm_bindgen(constructor)]
    pub fn new(terminal: xterm_js_rs::Terminal) -> Self {
        let console = Rc::from(RefCell::from(XtermJsConsole { terminal }));
        // TODO(jmmv): Register all commands.  Need to parameterize the program-related commands to
        // not try to do any I/O.
        let machine = endbasic_core::exec::MachineBuilder::default()
            .add_builtins(endbasic_core::console::all_commands(console.clone()))
            .add_builtin(Rc::from(endbasic_core::exec::ClearCommand::default()))
            .build();

        let mut console = console.borrow_mut();
        console.print("").unwrap();
        console.print(&format!("    Welcome to EndBASIC {}.", env!("CARGO_PKG_VERSION"))).unwrap();
        console.print("").unwrap();

        Self { machine }
    }

    /// Executes a single line of input.
    pub fn run(&mut self, code: &str) -> String {
        match self.machine.exec(&mut code.as_bytes()) {
            Ok(()) => "".to_owned(),
            Err(e) => format!("{}", e),
        }
    }
}

/// Module initialization.
pub fn main() -> Result<(), JsValue> {
    #[cfg(feature = "console_error_panic_hook")]
    console_error_panic_hook::set_once();

    Ok(())
}
