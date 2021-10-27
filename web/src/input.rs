// EndBASIC
// Copyright 2021 Julio Merino
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

//! Keyboard input tools for the web UI.

use crate::log_and_panic;
use async_channel::{self, Receiver, Sender, TryRecvError};
use endbasic_std::console::Key;
use std::io;
use wasm_bindgen::prelude::*;
use web_sys::KeyboardEvent;

/// Converts an HTML keyboard event into our own `Key` representation.
fn on_key_event_into_key(dom_event: KeyboardEvent) -> Key {
    match dom_event.key_code() as u8 {
        8 => Key::Backspace,
        9 => Key::Tab,
        10 => Key::NewLine,
        13 => Key::CarriageReturn,
        27 => Key::Escape,
        35 => Key::End,
        36 => Key::Home,
        37 => Key::ArrowLeft,
        38 => Key::ArrowUp,
        39 => Key::ArrowRight,
        40 => Key::ArrowDown,
        b'A' if dom_event.ctrl_key() => Key::Home,
        b'B' if dom_event.ctrl_key() => Key::ArrowLeft,
        b'C' if dom_event.ctrl_key() => Key::Interrupt,
        b'D' if dom_event.ctrl_key() => Key::Eof,
        b'E' if dom_event.ctrl_key() => Key::End,
        b'F' if dom_event.ctrl_key() => Key::ArrowRight,
        b'J' if dom_event.ctrl_key() => Key::NewLine,
        b'M' if dom_event.ctrl_key() => Key::NewLine,
        b'N' if dom_event.ctrl_key() => Key::ArrowDown,
        b'P' if dom_event.ctrl_key() => Key::ArrowUp,
        _ => {
            let printable = !dom_event.alt_key() && !dom_event.ctrl_key() && !dom_event.meta_key();
            let chars = dom_event.key().chars().collect::<Vec<char>>();
            if printable && chars.len() == 1 {
                Key::Char(chars[0])
            } else {
                Key::Unknown(format!("<keycode={}>", dom_event.key_code()))
            }
        }
    }
}

/// Interface to implement an on-screen keyboard to provide keys that may not be available on
/// mobile keyboards.
#[wasm_bindgen]
#[derive(Clone)]
pub struct OnScreenKeyboard {
    on_key_tx: Sender<Key>,
}

#[wasm_bindgen]
impl OnScreenKeyboard {
    /// Wrapper around `self.on_key_tx.try_send` that always expects to succeed.
    fn safe_try_send(&self, key: Key) {
        if let Err(e) = self.on_key_tx.try_send(key) {
            log_and_panic!("Send to unbounded channel must succeed: {}", e);
        }
    }

    /// Pushes a new captured `dom_event` keyboard event into the input.
    pub fn inject_keyboard_event(&self, dom_event: KeyboardEvent) {
        self.safe_try_send(on_key_event_into_key(dom_event))
    }

    /// Generates a fake Escape key press.
    pub fn press_escape(&self) {
        self.safe_try_send(Key::Escape)
    }

    /// Generates a fake arrow up key press.
    pub fn press_arrow_up(&self) {
        self.safe_try_send(Key::ArrowUp)
    }

    /// Generates a fake arrow down key press.
    pub fn press_arrow_down(&self) {
        self.safe_try_send(Key::ArrowDown)
    }

    /// Generates a fake arrow left key press.
    pub fn press_arrow_left(&self) {
        self.safe_try_send(Key::ArrowLeft)
    }

    /// Generates a fake arrow up key press.
    pub fn press_arrow_right(&self) {
        self.safe_try_send(Key::ArrowRight)
    }
}

/// Interface to interact with the browser's input, be it via a real keyboard or our custom
/// on-screen keyboard.
pub struct WebInput {
    on_key_rx: Receiver<Key>,
    on_key_tx: Sender<Key>,
}

impl Default for WebInput {
    fn default() -> Self {
        let (on_key_tx, on_key_rx) = async_channel::unbounded();
        Self { on_key_rx, on_key_tx }
    }
}

impl WebInput {
    /// Generates a new `OnScreenKeyboard` that can inject key events.
    pub(crate) fn on_screen_keyboard(&self) -> OnScreenKeyboard {
        OnScreenKeyboard { on_key_tx: self.on_key_tx.clone() }
    }

    /// Gets the next key event, if one is available.
    pub(crate) async fn try_recv(&mut self) -> io::Result<Option<Key>> {
        match self.on_key_rx.try_recv() {
            Ok(k) => Ok(Some(k)),
            Err(TryRecvError::Empty) => Ok(None),
            Err(TryRecvError::Closed) => log_and_panic!("Channel unexpectedly closed"),
        }
    }

    /// Gets the next key event, waiting until one is available.
    pub(crate) async fn recv(&mut self) -> io::Result<Key> {
        Ok(self.on_key_rx.recv().await.unwrap())
    }
}
