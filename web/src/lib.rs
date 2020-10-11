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

#[cfg(test)]
use wasm_bindgen_test::wasm_bindgen_test_configure;
#[cfg(test)]
wasm_bindgen_test_configure!(run_in_browser);

mod store;

use async_trait::async_trait;
use endbasic_core::console::Console;
use js_sys::{Function, Promise};
use std::cell::RefCell;
use std::io;
use std::rc::Rc;
use wasm_bindgen::prelude::*;
use wasm_bindgen_futures::JsFuture;

/// Implementation of a console that talks directly to an xterm.js terminal.
struct XtermJsConsole {
    terminal: xterm_js_rs::Terminal,
    read_line: Function,
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

    async fn input(&mut self, prompt: &str, _previous: &str) -> io::Result<String> {
        self.terminal.write(prompt);
        let this = JsValue::NULL;
        let promise = Promise::from(self.read_line.call0(&this).expect("Did not get a future"));
        let result = JsFuture::from(promise).await.expect("Failed to wait for read_line");
        Ok(result.as_string().expect("read_line expected to return a string"))
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
    last_error: String,
}

#[wasm_bindgen]
impl Interpreter {
    /// Constructs a new interpreter attached to `terminal` for console output.
    #[wasm_bindgen(constructor)]
    pub fn new(terminal: xterm_js_rs::Terminal, read_line: Function) -> Self {
        let console = Rc::from(RefCell::from(XtermJsConsole { terminal, read_line }));
        let store = Rc::from(RefCell::from(store::WebStore::from_window()));
        // TODO(jmmv): Register all commands.  Need to parameterize the program-related commands to
        // not try to do any I/O.
        let machine = endbasic_core::exec::MachineBuilder::default()
            .add_builtins(endbasic_core::console::all_commands(console.clone()))
            .add_builtin(Rc::from(endbasic_core::exec::ClearCommand::default()))
            .add_builtin(Rc::from(endbasic_core::help::HelpCommand::new(console.clone())))
            .add_builtins(endbasic_core::program::all_commands(console.clone(), store))
            .build();

        let mut console = console.borrow_mut();
        console.print("").unwrap();
        console.print("    Welcome to EndBASIC.").unwrap();
        console.print("    Type HELP for interactive usage information.").unwrap();
        console.print("").unwrap();

        Self { machine, last_error: "".to_owned() }
    }

    /// Executes a single line of input.
    ///
    /// Because this is async, it has to return itself to preserve all state while the call is
    /// ongoing.
    // TODO(jmmv): Would be nice to also return here any error information to avoid the separate
    // last_error method... but I haven't figured out how to do that.
    pub async fn run(mut self, code: String) -> Interpreter {
        match self.machine.exec(&mut code.as_bytes()).await {
            Ok(()) => {
                self.last_error = "".to_owned();
            }
            Err(e) => self.last_error = format!("{}", e),
        }
        self
    }

    /// Returns and consumes the error from the previous `run` invocation, if any.
    pub fn last_error(&mut self) -> String {
        let error = self.last_error.clone();
        self.last_error = "".to_owned();
        error
    }
}

/// Gets the build details for display on the interface.
#[wasm_bindgen]
pub fn get_build_id() -> String {
    format!("{} built on {}", env!("VERGEN_SHA_SHORT"), env!("VERGEN_BUILD_DATE"))
}

/// Module initialization.
pub fn main() -> Result<(), JsValue> {
    #[cfg(feature = "console_error_panic_hook")]
    console_error_panic_hook::set_once();

    Ok(())
}
