// EndBASIC
// Copyright 2020 Julio Merino
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

//! Web interface for the EndBASIC language.

use async_channel::{Receiver, Sender};
use async_trait::async_trait;
use endbasic_std::console::{Console, GraphicsConsole};
use endbasic_std::{Signal, Yielder};
use std::cell::RefCell;
use std::future::Future;
use std::io;
use std::pin::Pin;
use std::rc::Rc;
use std::time::Duration;
use time::OffsetDateTime;
use url::Url;
use wasm_bindgen::JsCast;
use wasm_bindgen::prelude::*;
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
        let _callback = callback; // Must grab ownership so that the closure remains alive until it is used.
        if let Err(e) = timeout_rx.recv().await {
            log_and_panic!("Failed to wait for timeout: {}", e);
        }
        ret
    })
}

/// Implementation of a `SleepFn` using `do_sleep`.
fn js_sleep(d: Duration, yielder: WebYielder) -> Pin<Box<dyn Future<Output = Result<(), String>>>> {
    let ms = d.as_millis();
    if ms > i32::MAX as u128 {
        // The JavaScript setTimeout function only takes i32s so ensure our value fits.  If it
        // doesn't, you can imagine chaining calls to setTimeout to achieve the desired delay...
        // but the numbers we are talking about are so big that this doesn't make sense.
        return Box::pin(async move { Err("Cannot sleep for that long".to_owned()) });
    }
    let ms = ms as i32;

    yielder.reset();
    do_sleep(ms, Ok(()))
}

/// Supplier of a `Yielder` that relies on a zero timeout to yield execution back to the
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
struct WebYielderState {
    counter: usize,
    last: OffsetDateTime,
}

#[derive(Clone)]
pub(crate) struct WebYielder(Rc<RefCell<WebYielderState>>);

impl WebYielder {
    /// Number of iterations during which the yielder does nothing but increment a counter.  We need
    /// this to be very cheap because this is called on every executed instruction.
    const GRACE_ITERATIONS: usize = 1000000;

    /// Maximum interval between forced yields.
    const MAX_INTERVAL_MILLIS: u64 = 1000;

    /// Creates a new yielder.
    fn new() -> Self {
        Self(Rc::from(RefCell::from(WebYielderState {
            counter: Self::GRACE_ITERATIONS,
            last: OffsetDateTime::now_utc(),
        })))
    }

    /// Yields execution via a zero timeout if enough instructions have been executed and if enough
    /// time has passed.
    fn yield_to_host(&self) -> Pin<Box<dyn Future<Output = ()>>> {
        let mut state = self.0.borrow_mut();
        if state.counter > 0 {
            state.counter -= 1;

            Box::pin(async move {})
        } else {
            let new_last = OffsetDateTime::now_utc();
            if (new_last - state.last) >= Duration::from_millis(Self::MAX_INTERVAL_MILLIS) {
                debug_assert!(state.counter == 0);
                state.last = new_last;

                do_sleep(0, ())
            } else {
                Box::pin(async move {})
            }
        }
    }

    /// Records that a yield just happened for some other reason and needn't happen again until the
    /// next interval.
    fn reset(&self) {
        let mut state = self.0.borrow_mut();
        state.counter = Self::GRACE_ITERATIONS;
        state.last = OffsetDateTime::now_utc();
    }

    /// Schedules a forced yield on the next round.
    pub(crate) fn schedule(&self) {
        let mut state = self.0.borrow_mut();
        state.counter = 0;
        state.last -= Duration::from_millis(Self::MAX_INTERVAL_MILLIS);
    }
}

#[async_trait(?Send)]
impl Yielder for WebYielder {
    async fn yield_now(&mut self) {
        let future = self.yield_to_host();
        future.await;
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
    yielder: WebYielder,
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
        let yielder = WebYielder::new();
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
            .with_yielder(Box::new(self.yielder.clone()))
            .with_signals_chan(self.signals_chan)
            .with_sleep_fn(Box::from(move |d| js_sleep(d, yielder.clone())));
        let program = Rc::from(RefCell::from(endbasic_repl::editor::Editor::default()));
        let storage = Rc::from(RefCell::from(endbasic_std::storage::Storage::default()));
        setup_storage(&mut storage.borrow_mut());

        let service =
            Rc::from(RefCell::from(endbasic_client::CloudService::new(&self.service_url)?));
        endbasic_client::add_all(
            &mut builder,
            service,
            console.clone(),
            storage.clone(),
            format!("{}/", location.origin().unicode_serialization()),
        );

        let mut machine = builder
            .make_interactive()
            .with_program(program.clone())
            .with_storage(storage.clone())
            .build();

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
        let yielder = WebYielder::new();
        let before = Date::now();
        js_sleep(Duration::from_millis(10), yielder).await.unwrap();
        let elapsed = Date::now() - before;
        assert!(10.0 <= elapsed);
    }

    #[wasm_bindgen_test]
    async fn test_js_sleep_too_big() {
        let yielder = WebYielder::new();
        assert_eq!(
            "Cannot sleep for that long",
            js_sleep(Duration::from_millis(i32::MAX as u64 + 1), yielder).await.unwrap_err()
        );
    }
}
