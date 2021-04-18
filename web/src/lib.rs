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
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(unused, unused_extern_crates, unused_import_braces, unused_qualifications)]
#![warn(unsafe_code)]

#[cfg(test)]
use wasm_bindgen_test::wasm_bindgen_test_configure;
#[cfg(test)]
wasm_bindgen_test_configure!(run_in_browser);

mod store;

use async_trait::async_trait;
use endbasic_core::syms::{self, CommandResult};
use endbasic_std::console::{ClearType, Console, Key, Position};
use std::cell::RefCell;
use std::cmp::Ordering;
use std::future::Future;
use std::io;
use std::pin::Pin;
use std::rc::Rc;
use std::time::Duration;
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use xterm_js_rs::{OnKeyEvent, Terminal};

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

    let window = web_sys::window().unwrap();
    window
        .set_timeout_with_callback_and_timeout_and_arguments(
            callback.as_ref().unchecked_ref(),
            ms,
            &js_sys::Array::new(),
        )
        .unwrap();

    Box::pin(async move {
        let _ = callback; // Must grab ownership so that the closure remains alive until it is used.
        timeout_rx.recv().await.unwrap();
        Ok(())
    })
}

/// Converts an xterm.js key event into our own `Key` representation.
fn on_key_event_into_key(event: OnKeyEvent) -> Key {
    let dom_event = event.dom_event();
    match dom_event.key_code() as u8 {
        8 => Key::Backspace,
        10 => Key::NewLine,
        13 => Key::CarriageReturn,
        27 => Key::Escape,
        37 => Key::ArrowLeft,
        38 => Key::ArrowUp,
        39 => Key::ArrowRight,
        40 => Key::ArrowDown,
        b'C' if dom_event.ctrl_key() => Key::Interrupt,
        b'D' if dom_event.ctrl_key() => Key::Eof,
        b'J' if dom_event.ctrl_key() => Key::NewLine,
        b'M' if dom_event.ctrl_key() => Key::NewLine,
        _ => {
            let printable = !dom_event.alt_key() && !dom_event.ctrl_key() && !dom_event.meta_key();
            let chars = event.key().chars().collect::<Vec<char>>();
            if printable && chars.len() == 1 {
                Key::Char(chars[0])
            } else {
                Key::Unknown(format!("<keycode={}>", dom_event.key_code()))
            }
        }
    }
}

/// Implementation of a console that talks directly to an xterm.js terminal.
struct XtermJsConsole {
    terminal: Terminal,
    on_key_rx: async_channel::Receiver<Key>,
}

#[async_trait(?Send)]
impl Console for XtermJsConsole {
    fn clear(&mut self, how: ClearType) -> io::Result<()> {
        match how {
            ClearType::All => {
                self.terminal.write("\u{001b}[2J");
                self.terminal.write("\u{001b}[0;0H");
            }
            ClearType::CurrentLine => {
                self.terminal.write("\u{001b}[2K");
            }
            ClearType::UntilNewLine => {
                self.terminal.write("\u{001b}[K");
            }
        }
        Ok(())
    }

    fn color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()> {
        match fg {
            None => self.terminal.write("\u{001b}[39m"),
            Some(color) => self.terminal.write(&format!("\u{001b}[38;5;{}m", color)),
        };
        match bg {
            None => self.terminal.write("\u{001b}[49m"),
            Some(color) => self.terminal.write(&format!("\u{001b}[48;5;{}m", color)),
        };
        self.terminal.write("\u{001b}[0K");
        Ok(())
    }

    fn enter_alt(&mut self) -> io::Result<()> {
        self.terminal.write("\u{001b}[?1049h");
        Ok(())
    }

    fn hide_cursor(&mut self) -> io::Result<()> {
        self.terminal.write("\u{001b}[?25l");
        Ok(())
    }

    fn is_interactive(&self) -> bool {
        true
    }

    fn leave_alt(&mut self) -> io::Result<()> {
        self.terminal.write("\u{001b}[?1049l");
        Ok(())
    }

    fn locate(&mut self, pos: Position) -> io::Result<()> {
        self.terminal.write(&format!("\u{001b}[{};{}H", pos.row + 1, pos.column + 1));
        Ok(())
    }

    fn move_within_line(&mut self, off: i16) -> io::Result<()> {
        match off.cmp(&0) {
            Ordering::Less => self.terminal.write(&format!("\u{001b}[{}D", -off)),
            Ordering::Equal => (),
            Ordering::Greater => self.terminal.write(&format!("\u{001b}[{}C", off)),
        }
        Ok(())
    }

    fn print(&mut self, text: &str) -> io::Result<()> {
        self.terminal.write(text);
        self.terminal.write("\u{001b}[K\r\n");
        Ok(())
    }

    async fn read_key(&mut self) -> io::Result<Key> {
        Ok(self.on_key_rx.recv().await.unwrap())
    }

    fn show_cursor(&mut self) -> io::Result<()> {
        self.terminal.write("\u{001b}[?25h");
        Ok(())
    }

    fn size(&self) -> io::Result<Position> {
        Ok(Position {
            row: self.terminal.get_rows() as usize,
            column: self.terminal.get_cols() as usize,
        })
    }

    fn write(&mut self, bytes: &[u8]) -> io::Result<()> {
        // TODO(jmmv): Should not have to convert to UTF-8 here because it might not be and the
        // terminal should not care (?).
        self.terminal.write(&String::from_utf8_lossy(bytes));
        Ok(())
    }
}

/// Interface to implement an on-screen keyboard to provide keys that may not be available on
/// mobile keyboards.
#[wasm_bindgen]
pub struct OnScreenKeyboard {
    on_key_tx: async_channel::Sender<Key>,
}

#[wasm_bindgen]
impl OnScreenKeyboard {
    /// Generates a fake Escape key press.
    pub fn press_escape(&self) {
        self.on_key_tx.try_send(Key::Escape).expect("Send to unbounded channel must succeed")
    }

    /// Generates a fake arrow up key press.
    pub fn press_arrow_up(&self) {
        self.on_key_tx.try_send(Key::ArrowUp).expect("Send to unbounded channel must succeed")
    }

    /// Generates a fake arrow down key press.
    pub fn press_arrow_down(&self) {
        self.on_key_tx.try_send(Key::ArrowDown).expect("Send to unbounded channel must succeed")
    }

    /// Generates a fake arrow left key press.
    pub fn press_arrow_left(&self) {
        self.on_key_tx.try_send(Key::ArrowLeft).expect("Send to unbounded channel must succeed")
    }

    /// Generates a fake arrow up key press.
    pub fn press_arrow_right(&self) {
        self.on_key_tx.try_send(Key::ArrowRight).expect("Send to unbounded channel must succeed")
    }
}

/// Sets up the common storage drives.
fn setup_storage(storage: &mut endbasic_std::storage::Storage) {
    storage.register_scheme("demos", endbasic::demos::demos_drive_factory);
    storage.mount("demos", "demos://").expect("Demos drive shouldn't fail to mount");
    storage.register_scheme("local", store::web_drive_factory);
    storage.mount("local", "local://").expect("Web drive shouldn't fail to mount");
    storage.cd("local:").expect("Local drive was just registered");
}

/// Connects the EndBASIC interpreter to a web page.
#[wasm_bindgen]
pub struct WebTerminal {
    on_key_rx: async_channel::Receiver<Key>,
    on_key_tx: async_channel::Sender<Key>,
}

#[wasm_bindgen]
impl WebTerminal {
    /// Creates a new instance of the `WebTerminal`.
    #[wasm_bindgen(constructor)]
    #[allow(clippy::new_without_default)] // Cannot implement Default in wasm-bindgen.
    pub fn new() -> Self {
        let (on_key_tx, on_key_rx) = async_channel::unbounded();
        Self { on_key_rx, on_key_tx }
    }

    /// Generates a new `OnScreenKeyboard` that can inject keypresses into this terminal.
    pub fn on_screen_keyboard(&self) -> OnScreenKeyboard {
        OnScreenKeyboard { on_key_tx: self.on_key_tx.clone() }
    }

    /// Starts the EndBASIC interpreter loop on the specified `terminal`.
    pub async fn run_repl_loop(self, terminal: Terminal) {
        let (on_key_tx, on_key_rx) = (self.on_key_tx, self.on_key_rx);
        let on_key_callback = {
            Closure::wrap(Box::new(move |e| {
                on_key_tx
                    .try_send(on_key_event_into_key(e))
                    .expect("Send to unbounded channel must succeed")
            }) as Box<dyn FnMut(OnKeyEvent)>)
        };
        terminal.on_key(on_key_callback.as_ref().unchecked_ref());

        let console = Rc::from(RefCell::from(XtermJsConsole { terminal, on_key_rx }));
        let mut builder = endbasic_std::MachineBuilder::default()
            .with_console(console.clone())
            .with_sleep_fn(Box::from(js_sleep))
            .make_interactive();

        let storage = builder.get_storage();
        setup_storage(&mut storage.borrow_mut());

        let mut machine = builder.build().unwrap();
        endbasic::print_welcome(console.clone()).unwrap();
        endbasic::try_load_autoexec(&mut machine, console.clone(), storage).await.unwrap();
        loop {
            let result = endbasic::run_repl_loop(&mut machine, console.clone()).await;
            let mut console = console.borrow_mut();
            match result {
                Ok(exit_code) => {
                    console.print(&format!("Interpreter exited with code {}", exit_code))
                }
                Err(e) => console.print(&format!("FATAL ERROR: {}", e)),
            }
            .expect("Cannot handle terminal printing errors");
            console
                .print("Resuming execution because the web interpreter cannot be exited")
                .unwrap();
            console.print("").unwrap();
        }
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
