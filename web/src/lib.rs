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
#![allow(clippy::await_holding_refcell_ref)]
#![allow(clippy::collapsible_else_if)]
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(unused, unused_extern_crates, unused_import_braces, unused_qualifications)]
#![warn(unsafe_code)]

use endbasic_core::syms::{self, CommandResult};
use endbasic_std::console::Console;
use std::cell::RefCell;
use std::future::Future;
use std::io;
use std::pin::Pin;
use std::rc::Rc;
use std::time::Duration;
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
#[cfg(test)]
use wasm_bindgen_test::wasm_bindgen_test_configure;
use web_sys::HtmlCanvasElement;

#[cfg(test)]
wasm_bindgen_test_configure!(run_in_browser);

mod canvas;
use canvas::CanvasConsole;
mod input;
use input::{OnScreenKeyboard, WebInput};
mod store;
use store::WebDriveFactory;

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    #[allow(unsafe_code)]
    pub(crate) fn log(s: &str);
}

/// Syntactic sugar to print an error to the console and panic.  Using `unwrap` and the like alone
/// results in an unhelpful `unreachable executed` stack trace.
macro_rules! log_and_panic {
    ($($arg:tt)*) => ({
        #[allow(unused_qualifications)]
        crate::log(&format!($($arg)*));
        unreachable!();
    })
}
pub(crate) use log_and_panic;

/// Sleeps for the given period of time.
fn js_sleep(d: Duration) -> Pin<Box<dyn Future<Output = CommandResult>>> {
    let ms = d.as_millis();
    if ms > std::i32::MAX as u128 {
        // The JavaScript setTimeout function only takes i32s so ensure our value fits.  If it
        // doesn't, you can imagine chaining calls to setTimeout to achieve the desired delay...
        // but the numbers we are talking about are so big that this doesn't make sense.
        return Box::pin(async move {
            Err(syms::CallError::InternalError("Cannot sleep for that long".to_owned()))
        });
    }
    let ms = ms as i32;

    let (timeout_tx, timeout_rx) = async_channel::unbounded();
    let callback = {
        Closure::wrap(Box::new(move || timeout_tx.try_send(true).expect("Send must succeed"))
            as Box<dyn FnMut()>)
    };

    let window = match web_sys::window() {
        Some(window) => window,
        None => log_and_panic!("Failed to get window"),
    };
    if let Err(e) = window.set_timeout_with_callback_and_timeout_and_arguments(
        callback.as_ref().unchecked_ref(),
        ms,
        &js_sys::Array::new(),
    ) {
        log_and_panic!("Failed to set timeout on window: {:?}", e);
    }

    Box::pin(async move {
        let _ = callback; // Must grab ownership so that the closure remains alive until it is used.
        if let Err(e) = timeout_rx.recv().await {
            log_and_panic!("Failed to wait for timeout: {}", e);
        }
        Ok(())
    })
}

/// Sets up the common storage drives.
fn setup_storage(storage: &mut endbasic_std::storage::Storage) {
    storage.register_scheme("demos", Box::from(endbasic_repl::demos::DemoDriveFactory::default()));
    storage.mount("demos", "demos://").expect("Demos drive shouldn't fail to mount");
    storage.register_scheme("local", Box::from(WebDriveFactory::default()));
    storage.mount("local", "local://").expect("Web drive shouldn't fail to mount");
    storage.cd("local:").expect("Local drive was just registered");
}

/// Connects the EndBASIC interpreter to a web page.
#[wasm_bindgen]
pub struct WebTerminal {
    console: CanvasConsole,
    on_screen_keyboard: OnScreenKeyboard,
}

#[wasm_bindgen]
impl WebTerminal {
    /// Creates a new instance of the `WebTerminal`.
    #[wasm_bindgen(constructor)]
    pub fn new(terminal: HtmlCanvasElement) -> Self {
        let input = WebInput::default();
        let on_screen_keyboard = input.on_screen_keyboard();
        let console = match CanvasConsole::new(terminal, input) {
            Ok(console) => console,
            Err(e) => log_and_panic!("Console initialization failed: {}", e),
        };

        Self { console, on_screen_keyboard }
    }

    /// Generates a new `OnScreenKeyboard` that can inject keypresses into this terminal.
    pub fn on_screen_keyboard(&self) -> OnScreenKeyboard {
        self.on_screen_keyboard.clone()
    }

    /// Returns a textual description of the size of the console.
    pub fn size_description(&self) -> String {
        let pixels = self.console.size_pixels();
        let chars = match self.console.size() {
            Ok(size) => size,
            Err(e) => panic!("Failed to get console size in chars: {}", e),
        };
        format!("{}x{} pixels, {}x{} chars", pixels.width, pixels.height, chars.x, chars.y)
    }

    /// Safe version of `run_repl_loop` that is able to return errors.
    async fn safe_run_repl_loop(self) -> io::Result<()> {
        let console = Rc::from(RefCell::from(self.console));
        let mut builder = endbasic_std::MachineBuilder::default()
            .with_console(console.clone())
            .with_sleep_fn(Box::from(js_sleep))
            .make_interactive()
            .with_program(Rc::from(RefCell::from(endbasic_repl::editor::Editor::default())));

        let program = builder.get_program();

        let storage = builder.get_storage();
        setup_storage(&mut storage.borrow_mut());

        let mut machine = match builder.build() {
            Ok(machine) => machine,
            Err(e) => {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    format!("Machine initialization failed: {}", e),
                ))
            }
        };
        endbasic_repl::print_welcome(console.clone())?;
        endbasic_repl::try_load_autoexec(&mut machine, console.clone(), storage).await?;
        loop {
            let result =
                endbasic_repl::run_repl_loop(&mut machine, console.clone(), program.clone()).await;
            let mut console = console.borrow_mut();
            match result {
                Ok(exit_code) => {
                    console.print(&format!("Interpreter exited with code {}", exit_code))
                }
                Err(e) => console.print(&format!("FATAL ERROR: {}", e)),
            }
            .expect("Cannot handle terminal printing errors");
            console.print("Resuming execution because the web interpreter cannot be exited")?;
            console.print("")?;
        }
    }

    /// Starts the EndBASIC interpreter loop on the specified `terminal`.
    pub async fn run_repl_loop(self) {
        if let Err(e) = self.safe_run_repl_loop().await {
            log_and_panic!("REPL failed: {}", e);
        }
    }
}

/// Gets the build details for display on the interface.
#[wasm_bindgen]
pub fn get_build_id() -> String {
    format!(
        "{} built from {} on {}",
        env!("CARGO_PKG_VERSION"),
        env!("VERGEN_SHA_SHORT"),
        env!("VERGEN_BUILD_DATE")
    )
}

/// Module initialization.
pub fn main() -> Result<(), JsValue> {
    #[cfg(feature = "console_error_panic_hook")]
    console_error_panic_hook::set_once();

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use js_sys::Date;
    use wasm_bindgen_test::*;

    #[wasm_bindgen_test]
    async fn test_js_sleep_ok() {
        let before = Date::now();
        js_sleep(Duration::from_millis(10)).await.unwrap();
        let elapsed = Date::now() - before;
        assert!(10.0 <= elapsed);
    }

    #[wasm_bindgen_test]
    async fn test_js_sleep_too_big() {
        match js_sleep(Duration::from_millis(std::i32::MAX as u64 + 1)).await.unwrap_err() {
            syms::CallError::InternalError(e) => {
                assert_eq!("Cannot sleep for that long", e)
            }
            e => panic!("Unexpected error type: {:?}", e),
        }
    }
}
