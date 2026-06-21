// EndBASIC
// Copyright 2026 Julio Merino
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

//! Date and time support for the web frontend.

use crate::{WebYielder, log_and_panic};
use async_trait::async_trait;
use std::future::Future;
use std::pin::Pin;
use std::time::Duration;
use wasm_bindgen::JsCast;
use wasm_bindgen::prelude::*;

/// Sleeps for the given period of time in `ms`.
pub(crate) fn do_sleep<T: 'static>(ms: i32, ret: T) -> Pin<Box<dyn Future<Output = T>>> {
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

/// Returns the current monotonic time in milliseconds.
pub(crate) fn current_time_millis() -> f64 {
    let window = match web_sys::window() {
        Some(window) => window,
        None => log_and_panic!("Failed to get window"),
    };
    match window.performance() {
        Some(performance) => performance.now(),
        None => js_sys::Date::now(),
    }
}

/// Browser-backed implementation of date and time facilities.
pub(crate) struct WebDateTime {
    yielder: WebYielder,
}

impl WebDateTime {
    /// Creates a new instance.
    pub(crate) fn new(yielder: WebYielder) -> Self {
        Self { yielder }
    }
}

#[async_trait(?Send)]
impl endbasic_std::datetime::DateTime for WebDateTime {
    fn monotonic(&self) -> Duration {
        Duration::from_secs_f64(current_time_millis() / 1000.0)
    }

    async fn sleep(&self, d: Duration) -> Result<(), String> {
        let ms = d.as_millis();
        if ms > i32::MAX as u128 {
            // The JavaScript setTimeout function only takes i32s so ensure our value fits.  If it
            // doesn't, you can imagine chaining calls to setTimeout to achieve the desired delay...
            // but the numbers we are talking about are so big that this doesn't make sense.
            return Err("Cannot sleep for that long".to_owned());
        }

        self.yielder.on_host_yield();
        do_sleep(ms as i32, Ok(())).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use endbasic_std::datetime::DateTime;
    use js_sys::Date;
    use wasm_bindgen_test::*;

    #[wasm_bindgen_test]
    async fn test_sleep_ok() {
        let datetime = WebDateTime::new(WebYielder::new());
        let before = Date::now();
        datetime.sleep(Duration::from_millis(10)).await.unwrap();
        let elapsed = Date::now() - before;
        assert!(10.0 <= elapsed);
    }

    #[wasm_bindgen_test]
    async fn test_sleep_too_big() {
        let datetime = WebDateTime::new(WebYielder::new());
        assert_eq!(
            "Cannot sleep for that long",
            datetime.sleep(Duration::from_millis(i32::MAX as u64 + 1)).await.unwrap_err()
        );
    }
}
