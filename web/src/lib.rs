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

use async_channel::{Receiver, Sender};
use endbasic_core::exec::{Error, Result, Signal, YieldNowFn};
use endbasic_core::LineCol;
use endbasic_std::console::{Console, GraphicsConsole};
use std::cell::RefCell;
use std::future::Future;
use std::io;
use std::pin::Pin;
use std::rc::Rc;
use std::time::Duration;
use time::OffsetDateTime;
use url::Url;
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
#[cfg(test)]
use wasm_bindgen_test::wasm_bindgen_test_configure;
use web_sys::HtmlCanvasElement;

#[cfg(test)]
wasm_bindgen_test_configure!(run_in_browser);

mod canvas;
use canvas::CanvasRasterOps;
mod input;
use input::{OnScreenKeyboard, WebInput, WebInputOps};
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

/// Sleeps for the given period of time in `ms`.
fn do_sleep<T: 'static>(ms: i32, ret: T) -> Pin<Box<dyn Future<Output = T>>> {
    assert!(ms >= 0, "Must have been validated by the caller");

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
        ret
    })
}

/// Implementation of a `SleepFn` using `do_sleep`.
fn js_sleep(
    d: Duration,
    pos: LineCol,
    yielder: Rc<RefCell<Yielder>>,
) -> Pin<Box<dyn Future<Output = Result<()>>>> {
    let ms = d.as_millis();
    if ms > i32::MAX as u128 {
        // The JavaScript setTimeout function only takes i32s so ensure our value fits.  If it
        // doesn't, you can imagine chaining calls to setTimeout to achieve the desired delay...
        // but the numbers we are talking about are so big that this doesn't make sense.
        return Box::pin(async move {
            Err(Error::InternalError(pos, "Cannot sleep for that long".to_owned()))
        });
    }
    let ms = ms as i32;

    yielder.borrow_mut().reset();
    do_sleep(ms, Ok(()))
}

/// Supplier of a `YieldNowFn` that relies on a zero timeout to yield execution back to the
/// JavaScript interpreter.
///
/// Yielding via a timeout in the way we do it is very expensive, so we need to avoid doing it too
/// frequently.  For this reason, this implementation tries to only yield once every
/// `MAX_INTERVAL_MILLIS`, only tries to compute this every `GRACE_ITERATIONS` instructions, and
/// only yields if nothing else (like an explicit sleep) has done it.
//
// TODO(jmmv): This is a big hack that we need to support interrupting running programs via CTRL+C
// and it doesn't work very well.   We should fix this by extracting the instruction execution loop
// from the `Machine` and issuing instructions here via a JavaScript interval.  It is unclear if
// this will fix the performance issues that we have though.
pub(crate) struct Yielder {
    counter: usize,
    last: OffsetDateTime,
}

impl Yielder {
    /// Number of iterations during which the yielder does nothing but increment a counter.  We need
    /// this to be very cheap because this is called on every executed instruction.
    const GRACE_ITERATIONS: usize = 1000000;

    /// Maximum interval between forced yields.
    const MAX_INTERVAL_MILLIS: u64 = 1000;

    /// Creates a new yielder.
    fn new() -> Self {
        Self { counter: Self::GRACE_ITERATIONS, last: OffsetDateTime::now_utc() }
    }

    /// Yields execution via a zero timeout if enough instructions have been executed and if enough
    /// time has passed.
    fn yield_now(&mut self) -> Pin<Box<dyn Future<Output = ()>>> {
        if self.counter > 0 {
            self.counter -= 1;

            Box::pin(async move {})
        } else {
            let new_last = OffsetDateTime::now_utc();
            if (new_last - self.last) >= Duration::from_millis(Self::MAX_INTERVAL_MILLIS) {
                debug_assert!(self.counter == 0);
                self.last = new_last;

                do_sleep(0, ())
            } else {
                Box::pin(async move {})
            }
        }
    }

    /// Records that a yield just happened for some other reason and needn't happen again until the
    /// next interval.
    fn reset(&mut self) {
        self.counter = Self::GRACE_ITERATIONS;
        self.last = OffsetDateTime::now_utc();
    }

    /// Schedules a forced yield on the next round.
    pub(crate) fn schedule(&mut self) {
        self.counter = 0;
        self.last -= Duration::from_millis(Self::MAX_INTERVAL_MILLIS);
    }

    /// Creates a new `YieldNowFn` that can be passed to the core executor for a given `yielder`.
    fn new_yield_now_fn(yielder: Rc<RefCell<Yielder>>) -> YieldNowFn {
        Box::from(move || {
            let yielder = yielder.clone();
            let mut yielder = yielder.borrow_mut();
            yielder.yield_now()
        })
    }
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
    yielder: Rc<RefCell<Yielder>>,
    console: GraphicsConsole<WebInputOps, CanvasRasterOps>,
    on_screen_keyboard: OnScreenKeyboard,
    service_url: String,
    signals_chan: (Sender<Signal>, Receiver<Signal>),
}

#[wasm_bindgen]
impl WebTerminal {
    /// Creates a new instance of the `WebTerminal`.
    #[wasm_bindgen(constructor)]
    pub fn new(terminal: HtmlCanvasElement, service_url: String) -> Self {
        let yielder = Rc::from(RefCell::from(Yielder::new()));
        let signals_chan = async_channel::unbounded();
        let input = WebInput::new(signals_chan.0.clone(), yielder.clone());
        let on_screen_keyboard = input.on_screen_keyboard();
        let raster_ops = match CanvasRasterOps::new(terminal, yielder.clone()) {
            Ok(raster_ops) => raster_ops,
            Err(e) => log_and_panic!("Console initialization failed: {}", e),
        };
        let input_ops = WebInputOps(input);
        let console = GraphicsConsole::new(input_ops, raster_ops, None, None).unwrap();

        Self { yielder, console, on_screen_keyboard, service_url, signals_chan }
    }

    /// Generates a new `OnScreenKeyboard` that can inject key events into this terminal.
    pub fn on_screen_keyboard(&self) -> OnScreenKeyboard {
        self.on_screen_keyboard.clone()
    }

    /// Returns a textual description of the size of the console.
    pub fn size_description(&self) -> String {
        let pixels = match self.console.size_pixels() {
            Ok(size) => size,
            Err(e) => panic!("Failed to get console size in pixels: {}", e),
        };
        let chars = match self.console.size_chars() {
            Ok(size) => size,
            Err(e) => panic!("Failed to get console size in chars: {}", e),
        };
        format!("{}x{} pixels, {}x{} chars", pixels.width, pixels.height, chars.x, chars.y)
    }

    /// Safe version of `run_repl_loop` that is able to return errors.
    async fn safe_run_repl_loop(self) -> io::Result<()> {
        let location = match web_sys::window() {
            Some(window) => match window.location().href() {
                Ok(href) => match Url::parse(&href) {
                    Ok(url) => url,
                    Err(e) => log_and_panic!("Failed to parse window's location href: {:?}", e),
                },
                Err(e) => log_and_panic!("Failed to get window's location href: {:?}", e),
            },
            None => log_and_panic!("Failed to get window"),
        };

        let yielder = self.yielder.clone();

        let console = Rc::from(RefCell::from(self.console));
        let mut builder = endbasic_std::MachineBuilder::default()
            .with_console(console.clone())
            .with_yield_now_fn(Yielder::new_yield_now_fn(self.yielder))
            .with_signals_chan(self.signals_chan)
            .with_sleep_fn(Box::from(move |d, pos| js_sleep(d, pos, yielder.clone())))
            .make_interactive()
            .with_program(Rc::from(RefCell::from(endbasic_repl::editor::Editor::default())));

        let program = builder.get_program();

        let storage = builder.get_storage();
        setup_storage(&mut storage.borrow_mut());

        let mut machine = match builder.build() {
            Ok(machine) => machine,
            Err(e) => {
                return Err(io::Error::other(format!("Machine initialization failed: {}", e)))
            }
        };

        let service =
            Rc::from(RefCell::from(endbasic_client::CloudService::new(&self.service_url)?));
        endbasic_client::add_all(
            &mut machine,
            service,
            console.clone(),
            storage.clone(),
            format!("{}/", location.origin().unicode_serialization()),
        );

        endbasic_repl::print_welcome(console.clone())?;

        let mut auto_run = None;
        for (name, value) in location.query_pairs() {
            if name == "run" {
                auto_run = Some(value);
                break;
            }
        }
        if let Some(auto_run) = auto_run {
            match endbasic_repl::run_from_cloud(
                &mut machine,
                console.clone(),
                storage.clone(),
                program.clone(),
                &auto_run,
                true,
            )
            .await
            {
                Ok(_code) => (),
                Err(e) => console
                    .borrow_mut()
                    .print(&format!("Failed to execute requested program: {}", e))?,
            }
        }

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

    /// Starts the EndBASIC interpreter loop.
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
        env!("VERGEN_GIT_SHA"),
        env!("VERGEN_BUILD_DATE")
    )
}

/// Module initialization.
pub fn main() -> std::result::Result<(), JsValue> {
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
        let yielder = Rc::from(RefCell::from(Yielder::new()));
        let before = Date::now();
        js_sleep(Duration::from_millis(10), LineCol { line: 1, col: 1 }, yielder).await.unwrap();
        let elapsed = Date::now() - before;
        assert!(10.0 <= elapsed);
    }

    #[wasm_bindgen_test]
    async fn test_js_sleep_too_big() {
        let yielder = Rc::from(RefCell::from(Yielder::new()));
        match js_sleep(
            Duration::from_millis(i32::MAX as u64 + 1),
            LineCol { line: 1, col: 2 },
            yielder,
        )
        .await
        .unwrap_err()
        {
            Error::InternalError(pos, e) => {
                assert_eq!(LineCol { line: 1, col: 2 }, pos);
                assert_eq!("Cannot sleep for that long", e);
            }
            e => panic!("Unexpected error type: {:?}", e),
        }
    }
}
