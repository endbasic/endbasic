// EndBASIC
// Copyright 2021 Julio Merino
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

//! Implementation of the EndBASIC console using SDL.

use crate::host::{Request, Response};
use async_trait::async_trait;
use endbasic_std::console::{
    CharsXY, ClearType, Console, Key, PixelsXY, SizeInPixels, remove_control_chars,
};
use std::io;
use std::sync::mpsc::{Receiver, SyncSender, TryRecvError};

/// Implementation of the EndBASIC console on top of an SDL2 window.
///
/// This is only the "client" part of the console, which implements the `Console` trait and
/// delegates all operations to a backing thread implemented by the `host` module.
pub(crate) struct SdlConsole {
    request_tx: SyncSender<Request>,
    response_rx: Receiver<Response>,
    on_key_rx: Receiver<Key>,
    fg_color: Option<u8>,
    bg_color: Option<u8>,
    alt_backup: Option<(Option<u8>, Option<u8>)>,
}

impl SdlConsole {
    /// Connects a new SDL console client to an already-configured host.
    pub(crate) fn new(
        request_tx: SyncSender<Request>,
        response_rx: Receiver<Response>,
        on_key_rx: Receiver<Key>,
    ) -> io::Result<Self> {
        // Wait for the host to be up and running.  We must do this for error propagation.
        match response_rx.recv().expect("Channel must be alive") {
            Response::Empty(Ok(())) => Ok(Self {
                request_tx,
                response_rx,
                on_key_rx,
                fg_color: None,
                bg_color: None,
                alt_backup: None,
            }),
            Response::Empty(Err(e)) => Err(e),
            r => panic!("Unexpected response {:?}", r),
        }
    }

    /// Issues a synchronous call against the console host for a request that returns nothing but
    /// an error (if any).
    fn call(&self, request: Request) -> io::Result<()> {
        self.request_tx.send(request).expect("Channel must be alive");
        match self.response_rx.recv().expect("Channel must be alive") {
            Response::Empty(Ok(v)) => Ok(v),
            Response::Empty(Err(e)) => Err(e),
            r => panic!("Unexpected response {:?}", r),
        }
    }
}

impl Drop for SdlConsole {
    fn drop(&mut self) {
        self.request_tx.send(Request::Exit).expect("Channel must be alive");
    }
}

#[async_trait(?Send)]
impl Console for SdlConsole {
    fn clear(&mut self, how: ClearType) -> io::Result<()> {
        self.call(Request::Clear(how))
    }

    fn color(&self) -> (Option<u8>, Option<u8>) {
        (self.fg_color, self.bg_color)
    }

    fn set_color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()> {
        self.call(Request::SetColor(fg, bg))?;
        self.fg_color = fg;
        self.bg_color = bg;
        Ok(())
    }

    fn enter_alt(&mut self) -> io::Result<()> {
        if self.alt_backup.is_some() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Cannot nest alternate screens",
            ));
        }

        self.alt_backup = Some((self.fg_color, self.bg_color));

        self.call(Request::EnterAlt)
    }

    fn hide_cursor(&mut self) -> io::Result<()> {
        self.call(Request::HideCursor)
    }

    fn is_interactive(&self) -> bool {
        true
    }

    fn leave_alt(&mut self) -> io::Result<()> {
        let alt_backup = match self.alt_backup.take() {
            Some(t) => t,
            None => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "Cannot leave alternate screen; not entered",
                ));
            }
        };

        self.call(Request::LeaveAlt)?;

        (self.fg_color, self.bg_color) = alt_backup;
        Ok(())
    }

    fn locate(&mut self, pos: CharsXY) -> io::Result<()> {
        self.call(Request::Locate(pos))
    }

    fn move_within_line(&mut self, off: i16) -> io::Result<()> {
        self.call(Request::MoveWithinLine(off))
    }

    fn print(&mut self, text: &str) -> io::Result<()> {
        let text = remove_control_chars(text);
        self.call(Request::Print(text))
    }

    async fn poll_key(&mut self) -> io::Result<Option<Key>> {
        match self.on_key_rx.try_recv() {
            Ok(k) => Ok(Some(k)),
            Err(TryRecvError::Empty) => Ok(None),
            Err(TryRecvError::Disconnected) => panic!("Channel must be alive"),
        }
    }

    async fn read_key(&mut self) -> io::Result<Key> {
        Ok(self.on_key_rx.recv().expect("Channel must be alive"))
    }

    fn show_cursor(&mut self) -> io::Result<()> {
        self.call(Request::ShowCursor)
    }

    fn size_chars(&self) -> io::Result<CharsXY> {
        self.request_tx.send(Request::SizeChars).expect("Channel must be alive");
        match self.response_rx.recv().expect("Channel must be alive") {
            Response::SizeChars(size) => Ok(size),
            _ => panic!("Unexpected response type"),
        }
    }

    fn size_pixels(&self) -> io::Result<SizeInPixels> {
        self.request_tx.send(Request::SizePixels).expect("Channel must be alive");
        match self.response_rx.recv().expect("Channel must be alive") {
            Response::SizePixels(size) => Ok(size),
            _ => panic!("Unexpected response type"),
        }
    }

    fn write(&mut self, text: &str) -> io::Result<()> {
        let text = remove_control_chars(text);
        self.call(Request::Write(text))
    }

    fn bucket_fill(&mut self, xy: PixelsXY) -> io::Result<()> {
        self.call(Request::BucketFill(xy))
    }

    fn draw_circle(&mut self, center: PixelsXY, radius: u16) -> io::Result<()> {
        self.call(Request::DrawCircle(center, radius))
    }

    fn draw_circle_filled(&mut self, center: PixelsXY, radius: u16) -> io::Result<()> {
        self.call(Request::DrawCircleFilled(center, radius))
    }

    fn draw_line(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        self.call(Request::DrawLine(x1y1, x2y2))
    }

    fn draw_pixel(&mut self, xy: PixelsXY) -> io::Result<()> {
        self.call(Request::DrawPixel(xy))
    }

    fn draw_poly(&mut self, points: &[PixelsXY]) -> io::Result<()> {
        self.call(Request::DrawPoly(points.to_vec()))
    }

    fn draw_poly_filled(&mut self, points: &[PixelsXY]) -> io::Result<()> {
        self.call(Request::DrawPolyFilled(points.to_vec()))
    }

    fn draw_rect(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        self.call(Request::DrawRect(x1y1, x2y2))
    }

    fn draw_rect_filled(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        self.call(Request::DrawRectFilled(x1y1, x2y2))
    }

    fn draw_tri(&mut self, x1y1: PixelsXY, x2y2: PixelsXY, x3y3: PixelsXY) -> io::Result<()> {
        self.call(Request::DrawTri(x1y1, x2y2, x3y3))
    }

    fn draw_tri_filled(
        &mut self,
        x1y1: PixelsXY,
        x2y2: PixelsXY,
        x3y3: PixelsXY,
    ) -> io::Result<()> {
        self.call(Request::DrawTriFilled(x1y1, x2y2, x3y3))
    }

    fn peek_pixel(&self, xy: PixelsXY) -> io::Result<Option<u8>> {
        self.request_tx.send(Request::PeekPixel(xy)).expect("Channel must be alive");
        match self.response_rx.recv().expect("Channel must be alive") {
            Response::PeekPixel(result) => result,
            _ => panic!("Unexpected response type"),
        }
    }

    fn sync_now(&mut self) -> io::Result<()> {
        self.call(Request::SyncNow)
    }

    fn set_sync(&mut self, enabled: bool) -> io::Result<bool> {
        self.request_tx.send(Request::SetSync(enabled)).expect("Channel must be alive");
        match self.response_rx.recv().expect("Channel must be alive") {
            Response::SetSync(result) => result,
            _ => panic!("Unexpected response type"),
        }
    }
}

#[cfg(test)]
mod testutils {
    use super::*;
    use crate::new_console_pair;
    use async_channel::{Receiver, TryRecvError};
    use endbasic_std::Signal;
    use endbasic_std::console::{ConsoleHost, Resolution};
    use endbasic_std::gfx::lcd::fonts::FONT_VGA8X16;
    use flate2::Compression;
    use flate2::read::GzDecoder;
    use flate2::write::GzEncoder;
    use futures_lite::future::block_on;
    use once_cell::sync::Lazy;
    use sdl2::event::Event;
    use sdl2::pixels::PixelFormatEnum;
    use sdl2::rwops::RWops;
    use sdl2::surface::Surface;
    use std::env;
    use std::fs::File;
    use std::io::{self, BufReader, Read};
    use std::num::NonZeroU32;
    use std::path::PathBuf;
    use std::sync::{Mutex, MutexGuard};
    use std::thread::{self, JoinHandle};

    /// Global lock to ensure we only instantiate a single `SdlConsole` at once.
    ///
    /// We could instead wrap a global `SdlConsole` with the mutex, but then the tests would
    /// sharing possibly-stale state in the presence of bugs.
    static TEST_LOCK: Lazy<Mutex<()>> = Lazy::new(|| Mutex::new(()));

    /// Computes the path to the directory where this test's binary lives.
    fn self_dir() -> PathBuf {
        let self_exe = env::current_exe().expect("Cannot get self's executable path");
        let dir = self_exe.parent().expect("Cannot get self's directory");
        assert!(dir.ends_with("target/debug/deps") || dir.ends_with("target/release/deps"));
        dir.to_owned()
    }

    /// Computes the path to the source file `name`.
    fn src_path(name: &str) -> PathBuf {
        let test_dir = self_dir();
        let debug_or_release_dir = test_dir.parent().expect("Failed to get parent directory");
        let target_dir = debug_or_release_dir.parent().expect("Failed to get parent directory");
        let dir = target_dir.parent().expect("Failed to get parent directory");

        // Sanity-check that we landed in the right location.
        assert!(dir.join("Cargo.toml").exists());

        dir.join(name)
    }

    /// Context for tests that validate the SDL console.
    #[must_use]
    pub(crate) struct SdlTest {
        /// The SDL console under test.
        console: Option<SdlConsole>,

        /// Handle to the background thread that runs the SDL host loop.
        host: Option<JoinHandle<io::Result<()>>>,

        /// Channel via which we receive signals from the console.
        signals_rx: Receiver<Signal>,

        /// Guard to ensure there is a single `SdlConsole` alive at any given time. This must come
        /// after `host` because the host must stop before releasing the lock.
        _lock: MutexGuard<'static, ()>,
    }

    impl SdlTest {
        /// Creates a new test context and ensures no other test is running at the same time.
        pub(crate) fn new() -> Self {
            let lock = TEST_LOCK.lock().unwrap();
            let signals_chan = async_channel::unbounded();
            let (host, factory) = new_console_pair(
                Resolution::Windowed((
                    NonZeroU32::new(800).unwrap(),
                    NonZeroU32::new(600).unwrap(),
                )),
                None,
                None,
                &FONT_VGA8X16,
                signals_chan.0,
            );
            let host = thread::spawn(move || Box::new(host).run());
            let console = factory.build_console().unwrap();
            Self {
                _lock: lock,
                console: Some(console),
                host: Some(host),
                signals_rx: signals_chan.1,
            }
        }

        /// Obtains access to the SDL console.
        pub(crate) fn console(&mut self) -> &mut SdlConsole {
            self.console.as_mut().expect("Console must always be present")
        }

        /// Obtains shared access to the SDL console.
        pub(crate) fn console_ref(&self) -> &SdlConsole {
            self.console.as_ref().expect("Console must always be present")
        }

        /// Synchronously waits for the reception of just one signal.
        pub(crate) fn wait_one_signal(&self) -> Signal {
            let signal = block_on(self.signals_rx.recv()).unwrap();

            match self.signals_rx.try_recv() {
                Ok(signal) => panic!("Received duplicate signal {:?}", signal),
                Err(TryRecvError::Empty) => (),
                Err(TryRecvError::Closed) => panic!("Channel must be alive"),
            }

            signal
        }

        /// Injects an SDL event into the console.
        pub(crate) fn push_event(&self, ev: Event) {
            self.console_ref().call(Request::PushEvent(ev)).unwrap()
        }

        /// Verifies that the current state of the console matches a golden imagine.  `bmp_basename`
        /// indicates the name of the BMP image to use, without an extension.
        pub(crate) fn verify(self, bmp_basename: &'static str) {
            let golden_bmp_gz = src_path("sdl/src").join(format!("{}.bmp.gz", bmp_basename));
            let dir = tempfile::tempdir().unwrap();
            let actual_bmp = dir.path().join(format!("{}.bmp", bmp_basename));

            self.console
                .as_ref()
                .expect("Console must always be present")
                .call(Request::SaveBmp(actual_bmp.clone()))
                .unwrap();

            if matches!(env::var("REGEN").as_deref(), Ok("1") | Ok("true") | Ok("yes")) {
                let mut input = BufReader::new(File::open(actual_bmp).unwrap());
                let output = File::create(golden_bmp_gz).unwrap();
                let mut encoder = GzEncoder::new(output, Compression::default());
                io::copy(&mut input, &mut encoder).unwrap();
                encoder.finish().unwrap();

                // We could delete the `actual_bmp` file here, but it's easier to keep it around
                // for manual validation of the new images.

                drop(self); // Avoid poisoning the mutex when panicking.
                panic!("Golden data regenerated; flip REGEN back to false");
            }

            let actual = {
                let mut rwops = RWops::from_file(actual_bmp, "r").unwrap();
                Surface::load_bmp_rw(&mut rwops)
                    .unwrap()
                    .into_canvas()
                    .unwrap()
                    .read_pixels(None, PixelFormatEnum::BGR888)
                    .unwrap()
            };

            let golden = {
                let input = BufReader::new(File::open(golden_bmp_gz).unwrap());
                let mut decoder = GzDecoder::new(input);
                let mut buffer = vec![];
                decoder.read_to_end(&mut buffer).unwrap();
                let mut rwops = RWops::from_bytes(buffer.as_slice()).unwrap();
                Surface::load_bmp_rw(&mut rwops)
                    .unwrap()
                    .into_canvas()
                    .unwrap()
                    .read_pixels(None, PixelFormatEnum::BGR888)
                    .unwrap()
            };

            // The test should not fail until this point, or else we poison the mutex and all
            // subsequent tests fail.  However, we must do this *after* the `Surface` manipulation
            // above, or else tests misbehave.
            drop(self);

            // Compare images for equality.  In theory, they should be pixel-perfect across
            // platforms, but in practice, I'm encountering minor color variations (e.g. FreeBSD
            // renders colors that differ by one compared to Windows) that I haven't been able to
            // explain.  Cope with those here by tolerating minor differences in the comparison.
            let mut equal = true;
            assert_eq!(golden.len(), actual.len());
            for i in 0..golden.len() {
                let pixel1 = golden[i];
                let pixel2 = actual[i];

                let pixel2min = match pixel2 {
                    0 => pixel2,
                    1 => pixel2 - 1,
                    _ => pixel2 - 2,
                };
                let pixel2max = match pixel2 {
                    255 => pixel2,
                    254 => pixel2 + 1,
                    _ => pixel2 + 2,
                };

                if pixel1 < pixel2min || pixel1 > pixel2max {
                    eprintln!("Diff at pixel {}: {} vs. {}", i, pixel1, pixel2);
                    equal = false;
                }
            }
            assert!(equal, "Images do not match; see test output");
        }
    }

    impl Drop for SdlTest {
        fn drop(&mut self) {
            drop(self.console.take().expect("Console must always be present"));
            let host = self.host.take().expect("Host must always be present");
            host.join().expect("Thread should not have panicked").expect("Host should not fail");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::testutils::*;
    use super::*;
    use endbasic_std::Signal;
    use futures_lite::future::block_on;
    use sdl2::event::Event;
    use sdl2::keyboard::{Keycode, Mod};
    use sdl2::mouse::MouseButton;
    use std::thread;
    use std::time::Duration;

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_empty() {
        let test = SdlTest::new();
        test.verify("sdl-empty");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_colors() {
        let mut test = SdlTest::new();

        test.console().print("Default colors").unwrap();
        test.console().print("").unwrap();
        test.console().set_color(Some(14), Some(4)).unwrap();
        test.console().print("Cyan on blue").unwrap();
        test.console().set_color(None, Some(1)).unwrap();
        test.console().print("Default on red").unwrap();
        test.console().set_color(Some(11), None).unwrap();
        test.console().print("Yellow on default").unwrap();
        test.console().set_color(None, None).unwrap();
        test.console().print("").unwrap();
        test.console().print("Back to default colors").unwrap();

        test.verify("sdl-colors");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_scroll_and_wrap() {
        let mut test = SdlTest::new();

        test.console().set_color(None, Some(4)).unwrap();

        let mut long_line = String::new();
        for i in 0..128 {
            long_line.push((b'a' + (i % 26)) as char);
        }

        for i in 0..15 {
            test.console().print(&format!("Line {}", i)).unwrap();
        }
        test.console().print(&long_line).unwrap();
        for i in 0..10 {
            test.console().print(&format!("Line {}", i)).unwrap();
        }
        test.console().print(&long_line).unwrap();
        test.console().print("End").unwrap();

        test.verify("sdl-scroll-and-wrap");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_clear() {
        let mut test = SdlTest::new();

        test.console().print("Before clearing the console").unwrap();
        test.console().set_color(None, Some(4)).unwrap();
        test.console().clear(ClearType::All).unwrap();
        test.console().print("After clearing the console in blue").unwrap();

        test.console().write("A line that will be erased").unwrap();
        test.console().clear(ClearType::CurrentLine).unwrap();

        test.console().write("A line with corrections1.").unwrap();
        test.console().clear(ClearType::PreviousChar).unwrap();
        test.console().clear(ClearType::PreviousChar).unwrap();
        test.console().print("!").unwrap();

        test.console().write("Remove part of this").unwrap();
        test.console().move_within_line(-8).unwrap();
        test.console().clear(ClearType::UntilNewLine).unwrap();
        test.console().write(" -- done").unwrap();

        test.console().locate(CharsXY { x: 0, y: 5 }).unwrap();
        test.console().hide_cursor().unwrap();
        test.console().write("Trailing period should be gone.").unwrap();
        test.console().clear(ClearType::PreviousChar).unwrap();
        test.console().move_within_line(-2).unwrap();
        test.console().show_cursor().unwrap();

        test.verify("sdl-clear");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_move_cursor() {
        let mut test = SdlTest::new();

        test.console().write("Move cursor over parts of this text").unwrap();
        for _ in 0..15 {
            test.console().move_within_line(-1).unwrap();
        }
        for _ in 0..5 {
            test.console().move_within_line(1).unwrap();
        }

        test.verify("sdl-move-cursor");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_hide_cursor() {
        let mut test = SdlTest::new();

        test.console().hide_cursor().unwrap();
        test.console().hide_cursor().unwrap();
        test.console().write("Cursor hidden").unwrap();

        test.verify("sdl-hide-cursor");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_enter_alt() {
        let mut test = SdlTest::new();

        test.console().print("Before entering the alternate console").unwrap();
        test.console().enter_alt().unwrap();
        test.console().print("After entering the alternate console").unwrap();

        test.verify("sdl-enter-alt");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_leave_alt() {
        let mut test = SdlTest::new();

        test.console().print("Before entering the alternate console").unwrap();
        test.console().enter_alt().unwrap();
        test.console().print("After entering the alternate console").unwrap();
        test.console().leave_alt().unwrap();

        test.verify("sdl-leave-alt");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_alt_colors() {
        let mut test = SdlTest::new();

        test.console().set_color(Some(13), Some(5)).unwrap();

        test.console().enter_alt().unwrap();
        assert_eq!((Some(13), Some(5)), test.console().color());
        test.console().print("After entering the alternate console").unwrap();

        test.console().set_color(Some(15), Some(0)).unwrap();
        assert_eq!((Some(15), Some(0)), test.console().color());

        test.console().leave_alt().unwrap();
        test.console().print("After leaving the alternate console").unwrap();
        assert_eq!((Some(13), Some(5)), test.console().color());

        test.verify("sdl-alt-colors");
    }

    /// Synthesizes an `Event::KeyDown` event for a single key press.
    fn key_down(keycode: Keycode, keymod: Mod) -> Event {
        Event::KeyDown {
            keycode: Some(keycode),
            scancode: None,
            keymod,
            timestamp: 0,
            repeat: false,
            window_id: 0,
        }
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_poll_key() {
        let mut test = SdlTest::new();

        /// Ensure the console doesn't return a key press for a brief period of time.
        ///
        /// Given that this is based on timing, the console could still report an event long after
        /// we finished polling.  This is fine: if the console works well, we shouldn't receive
        /// spurious events here, which means that under normal conditions, this is not flaky.
        /// However, if there is a bug somewhere, this is not guaranteed to catch it reliably.
        fn assert_poll_is_none(console: &mut SdlConsole) {
            let mut millis = 10;
            while millis > 0 {
                assert_eq!(None, block_on(console.poll_key()).unwrap());
                thread::sleep(Duration::from_millis(1));
                millis -= 1;
            }
        }

        /// Waits for `console.poll_key` to return `exp_key` and fails the test if it returns any
        /// other key.
        fn assert_poll_is_key(console: &mut SdlConsole, exp_key: Key) {
            loop {
                match block_on(console.poll_key()).unwrap() {
                    Some(key) if key == exp_key => break,
                    Some(key) => panic!("Unexpected key {:?}", key),
                    None => (),
                }
                thread::sleep(Duration::from_millis(1));
            }
        }

        assert_poll_is_none(test.console());

        test.push_event(Event::Quit { timestamp: 0 });
        assert_poll_is_key(test.console(), Key::Eof);
        assert_poll_is_none(test.console());

        test.push_event(key_down(Keycode::C, Mod::LCTRLMOD));
        assert_poll_is_key(test.console(), Key::Interrupt);
        assert_eq!(Signal::Break, test.wait_one_signal());
        assert_poll_is_none(test.console());

        // TODO(jmmv): We aren't testing textual input because push_event doesn't support injecting
        // Event::TextInput events.  At least check that individual key presses are ignored, because
        // those would otherwise "hide" the follow-up text input events.
        test.push_event(key_down(Keycode::A, Mod::empty()));
        assert_poll_is_none(test.console());

        // Check that non-keyboard events are ignored until a key event is received.
        test.push_event(Event::MouseButtonDown {
            timestamp: 0,
            window_id: 0,
            which: 0,
            mouse_btn: MouseButton::Left,
            clicks: 0,
            x: 0,
            y: 0,
        });
        test.push_event(Event::JoyButtonUp { timestamp: 0, which: 0, button_idx: 0 });
        test.push_event(key_down(Keycode::C, Mod::LCTRLMOD));
        assert_poll_is_key(test.console(), Key::Interrupt);
        assert_eq!(Signal::Break, test.wait_one_signal());
        assert_poll_is_none(test.console());

        test.verify("sdl-empty");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_read_key() {
        let mut test = SdlTest::new();

        test.push_event(Event::Quit { timestamp: 0 });
        assert_eq!(Key::Eof, block_on(test.console().read_key()).unwrap());

        test.push_event(key_down(Keycode::C, Mod::LCTRLMOD));
        assert_eq!(Key::Interrupt, block_on(test.console().read_key()).unwrap());
        assert_eq!(Signal::Break, test.wait_one_signal());
        test.push_event(key_down(Keycode::C, Mod::RCTRLMOD));
        assert_eq!(Key::Interrupt, block_on(test.console().read_key()).unwrap());
        assert_eq!(Signal::Break, test.wait_one_signal());

        test.push_event(key_down(Keycode::D, Mod::LCTRLMOD));
        assert_eq!(Key::Eof, block_on(test.console().read_key()).unwrap());
        test.push_event(key_down(Keycode::D, Mod::RCTRLMOD));
        assert_eq!(Key::Eof, block_on(test.console().read_key()).unwrap());

        test.push_event(key_down(Keycode::D, Mod::empty()));
        test.push_event(key_down(Keycode::Up, Mod::empty()));
        match block_on(test.console().read_key()).unwrap() {
            Key::ArrowUp => (),
            Key::Char('d') => panic!("Char key not ignored as intended"),
            key => panic!("Unexpected key {:?}", key),
        };

        // TODO(jmmv): We aren't testing textual input because push_event doesn't support injecting
        // Event::TextInput events.

        test.verify("sdl-empty");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_draw() {
        let mut test = SdlTest::new();
        let console = test.console();

        fn xy(x: i16, y: i16) -> PixelsXY {
            PixelsXY { x, y }
        }

        // ----
        // Draw some stuff that is completely visible.
        // ----

        console.set_color(Some(15), None).unwrap();
        console.draw_line(xy(10, 50), xy(110, 60)).unwrap();
        console.set_color(Some(12), Some(1)).unwrap();
        console.draw_line(xy(120, 70), xy(20, 60)).unwrap();

        console.set_color(Some(12), Some(1)).unwrap();
        // A line with start and end at the same spot should be invisible.
        console.draw_line(xy(200, 200), xy(200, 200)).unwrap();
        // But with a slight variation it should be a pixel.
        console.draw_line(xy(190, 190), xy(190, 191)).unwrap();
        console.draw_line(xy(190, 190), xy(191, 190)).unwrap();
        console.draw_line(xy(190, 191), xy(190, 190)).unwrap();
        console.draw_line(xy(191, 190), xy(190, 190)).unwrap();

        console.set_color(Some(15), None).unwrap();
        console.draw_rect_filled(xy(380, 180), xy(220, 120)).unwrap();
        console.set_color(Some(10), None).unwrap();
        console.draw_rect(xy(200, 100), xy(400, 200)).unwrap();
        console.set_color(Some(11), None).unwrap();
        console.draw_tri_filled(xy(500, 100), xy(560, 200), xy(440, 200)).unwrap();
        console.set_color(Some(13), None).unwrap();
        console.draw_tri(xy(500, 80), xy(580, 220), xy(420, 220)).unwrap();

        console.set_color(Some(10), None).unwrap();
        console
            .draw_poly_filled(&[xy(80, 140), xy(140, 110), xy(180, 150), xy(150, 210), xy(90, 200)])
            .unwrap();
        console.set_color(Some(15), None).unwrap();
        console
            .draw_poly(&[xy(70, 130), xy(145, 90), xy(195, 145), xy(155, 225), xy(80, 210)])
            .unwrap();

        console.set_color(Some(14), None).unwrap();
        console.draw_circle_filled(xy(650, 400), 50).unwrap();
        console.set_color(Some(9), None).unwrap();
        console.draw_circle(xy(650, 400), 80).unwrap();

        console.set_color(Some(12), None).unwrap();
        // A circle of radius 1 should be a single pixel.
        console.draw_circle_filled(xy(650, 210), 1).unwrap();
        console.draw_circle(xy(650, 200), 1).unwrap();
        // A circle of radius 0 should be invisible.
        console.draw_circle_filled(xy(650, 215), 0).unwrap();
        console.draw_circle(xy(650, 205), 0).unwrap();

        console.set_color(Some(14), None).unwrap();
        for i in 0..8 {
            console.draw_pixel(xy(i * 100, 300)).unwrap();
        }

        // ----
        // Draw some stuff that is completely off screen.
        // ----

        console.set_color(Some(15), None).unwrap();
        console.draw_pixel(xy(-1, 1)).unwrap();
        console.draw_pixel(xy(801, 601)).unwrap();
        console.draw_pixel(xy(-1, 0)).unwrap();
        console.draw_pixel(xy(0, 601)).unwrap();
        console.draw_line(xy(-1000, -2000), xy(-50, -30)).unwrap();
        console.draw_rect(xy(-10, -10), xy(-5, -5)).unwrap();
        console.draw_rect(xy(-10, -10), xy(810, 610)).unwrap();
        console.draw_rect(xy(810, 610), xy(815, 615)).unwrap();
        console.draw_circle(xy(-100, -100), 10).unwrap();
        console.draw_circle(xy(1000, 1000), 10).unwrap();
        console.draw_circle(xy(400, 300), 1000).unwrap();
        console.draw_circle_filled(xy(-100, -100), 10).unwrap();
        console.draw_circle_filled(xy(1000, 1000), 10).unwrap();
        console.draw_poly(&[xy(-100, -100), xy(-80, -130), xy(-40, -110), xy(-60, -80)]).unwrap();
        console
            .draw_poly_filled(&[xy(850, 650), xy(900, 620), xy(940, 700), xy(860, 740)])
            .unwrap();

        // ----
        // Draw some stuff that is partially visible.
        // ----

        console.set_color(Some(15), None).unwrap();
        console.draw_line(xy(-1000, 500), xy(100, 520)).unwrap();
        console.draw_rect(xy(-10, 400), xy(10, 450)).unwrap();
        console.draw_rect(xy(790, 410), xy(810, 440)).unwrap();
        console.draw_rect_filled(xy(500, -10), xy(510, 610)).unwrap();
        console.draw_circle(xy(800, 300), 50).unwrap();
        console.draw_circle_filled(xy(800, 300), 40).unwrap();
        console
            .draw_poly(&[xy(-20, 540), xy(20, 500), xy(60, 530), xy(30, 590), xy(-10, 580)])
            .unwrap();
        console
            .draw_poly_filled(&[
                xy(760, 500),
                xy(820, 470),
                xy(830, 540),
                xy(780, 590),
                xy(740, 550),
            ])
            .unwrap();

        console.set_color(None, None).unwrap();
        console.locate(CharsXY { x: 4, y: 22 }).unwrap();
        console.write("Done!").unwrap();

        test.verify("sdl-draw");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_draw_zero_sized_shapes() {
        let mut test = SdlTest::new();
        let console = test.console();

        fn xy(x: i16, y: i16) -> PixelsXY {
            PixelsXY { x, y }
        }

        console.set_color(Some(15), None).unwrap();
        console.draw_line(xy(10, 10), xy(10, 10)).unwrap();
        console.draw_rect(xy(20, 10), xy(20, 10)).unwrap();
        console.draw_rect_filled(xy(30, 10), xy(30, 10)).unwrap();
        console.draw_tri(xy(60, 10), xy(60, 10), xy(60, 10)).unwrap();
        console.draw_tri_filled(xy(70, 10), xy(75, 15), xy(80, 20)).unwrap();
        console.draw_circle(xy(40, 40), 0).unwrap();
        console.draw_circle_filled(xy(50, 50), 0).unwrap();
        console.draw_poly(&[xy(90, 10), xy(90, 10), xy(90, 10), xy(90, 10)]).unwrap();
        console.draw_poly_filled(&[xy(100, 10), xy(100, 10), xy(100, 10), xy(100, 10)]).unwrap();

        test.verify("sdl-empty");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_draw_one_sized_rectangles() {
        let mut test = SdlTest::new();
        let console = test.console();

        fn xy(x: i16, y: i16) -> PixelsXY {
            PixelsXY { x, y }
        }

        console.set_color(Some(15), None).unwrap();
        console.draw_rect(xy(10, 10), xy(10, 15)).unwrap();
        console.draw_rect(xy(20, 20), xy(25, 20)).unwrap();
        console.draw_rect_filled(xy(30, 30), xy(30, 35)).unwrap();
        console.draw_rect_filled(xy(40, 40), xy(45, 40)).unwrap();

        test.verify("sdl-draw-one-sized-rectangles");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_peek_pixel_exact_match() {
        let mut test = SdlTest::new();

        test.console().hide_cursor().unwrap();
        test.console().set_color(Some(15), None).unwrap();
        test.console().draw_pixel(PixelsXY::new(3, 4)).unwrap();

        assert_eq!(Some(15), test.console().peek_pixel(PixelsXY::new(3, 4)).unwrap());
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_peek_pixel_out_of_bounds() {
        let test = SdlTest::new();

        assert_eq!(None, test.console_ref().peek_pixel(PixelsXY::new(-1, 0)).unwrap());
        assert_eq!(None, test.console_ref().peek_pixel(PixelsXY::new(0, -1)).unwrap());

        let size = test.console_ref().size_pixels().unwrap();
        assert_eq!(
            None,
            test.console_ref().peek_pixel(PixelsXY::new(size.width as i16, 0)).unwrap()
        );
        assert_eq!(
            None,
            test.console_ref().peek_pixel(PixelsXY::new(0, size.height as i16)).unwrap()
        );
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_show_cursor() {
        let mut test = SdlTest::new();

        test.console().show_cursor().unwrap();
        test.console().show_cursor().unwrap();

        test.verify("sdl-empty");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_sync() {
        let mut test = SdlTest::new();

        test.console().print("Before disabling sync").unwrap();
        test.console().set_sync(false).unwrap();
        test.console().print("After disabling sync").unwrap();
        test.console().sync_now().unwrap();
        test.console().print("With sync disabled").unwrap();

        test.verify("sdl-sync");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_sdl_console_write_positions() {
        let mut test = SdlTest::new();

        let cols = test.console().size_chars().unwrap().x;
        for c in 0..cols {
            test.console().locate(CharsXY { x: c, y: 0 }).unwrap();
            test.console().write("").unwrap();
            test.console().locate(CharsXY { x: c, y: 2 }).unwrap();
            test.console().write("a").unwrap();
            test.console().locate(CharsXY { x: c, y: 4 }).unwrap();
            test.console().write("bc").unwrap();
        }

        test.verify("sdl-write-positions");
    }
}
