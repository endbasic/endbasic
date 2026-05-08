// EndBASIC
// Copyright 2022 Julio Merino
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

//! Background thread that runs the SDL main loop and acts as the host for the console.
//!
//! All communication with this thread happens via channels to ensure all SDL operations are invoked
//! from a single thread.

use crate::string_error_to_io_error;
use endbasic_std::Signal;
use endbasic_std::console::graphics::{ClampedInto, ClampedMul};
use endbasic_std::console::{CharsXY, Key, Resolution, SizeInPixels};
use endbasic_std::gfx::lcd::{LcdSize, LcdXY, to_xy_size};
use sdl2::event::Event;
use sdl2::keyboard::{Keycode, Mod};
use sdl2::pixels::PixelFormatEnum;
use sdl2::rect::Rect;
use sdl2::render::{SurfaceCanvas, TextureCreator, TextureValueError, UpdateTextureError};
use sdl2::surface::{Surface, SurfaceContext};
use sdl2::video::{Window, WindowBuildError};
use sdl2::{EventPump, Sdl};
use std::cell::RefCell;
use std::convert::TryFrom;
use std::fmt::{self, Write};
use std::io;
#[cfg(test)]
use std::path::Path;
use std::rc::Rc;
use std::sync::mpsc::{Receiver, Sender, SyncSender, TryRecvError};
use std::thread;
use std::time::Duration;

/// Number of loop iterations to poll for requests or events before sleeping.
///
/// We do this to avoid pauses that might occur if the client is sending us consecutive requests
/// but for some reason the loop is faster and fails to notice them.
const LOOP_POLL_BUDGET: u16 = 10000;

/// Delay between loop iterations when the polling budget in `LOOP_POLL_BUDGET` is exceeded.
const LOOP_DELAY_MS: u64 = 1;

/// Converts a `fmt::Error` to an `io::Error`.
fn fmt_error_to_io_error(e: fmt::Error) -> io::Error {
    io::Error::other(e)
}

/// Converts a `TextureValueError` to an `io::Error`.
fn texture_value_error_to_io_error(e: TextureValueError) -> io::Error {
    let kind = match e {
        TextureValueError::HeightOverflows(_)
        | TextureValueError::WidthOverflows(_)
        | TextureValueError::WidthMustBeMultipleOfTwoForFormat(_, _) => io::ErrorKind::InvalidInput,
        TextureValueError::SdlError(_) => io::ErrorKind::Other,
    };
    io::Error::new(kind, e)
}

/// Converts an `UpdateTextureError` to an `io::Error`.
fn update_texture_error_to_io_error(e: UpdateTextureError) -> io::Error {
    let kind = match e {
        UpdateTextureError::HeightMustBeMultipleOfTwoForFormat(_, _)
        | UpdateTextureError::PitchMustBeMultipleOfTwoForFormat(_, _)
        | UpdateTextureError::PitchOverflows(_)
        | UpdateTextureError::WidthMustBeMultipleOfTwoForFormat(_, _)
        | UpdateTextureError::XMustBeMultipleOfTwoForFormat(_, _)
        | UpdateTextureError::YMustBeMultipleOfTwoForFormat(_, _) => io::ErrorKind::InvalidInput,
        UpdateTextureError::SdlError(_) => io::ErrorKind::Other,
    };
    io::Error::new(kind, e)
}

/// Converts a `WindowBuildError` to an `io::Error`.
fn window_build_error_to_io_error(e: WindowBuildError) -> io::Error {
    let kind = match e {
        WindowBuildError::HeightOverflows(_) | WindowBuildError::WidthOverflows(_) => {
            io::ErrorKind::InvalidInput
        }
        WindowBuildError::InvalidTitle(_) => panic!("Hardcoded window title is invalid"),
        WindowBuildError::SdlError(_) => io::ErrorKind::Other,
    };
    io::Error::new(kind, e)
}

/// Constructs an SDL `Rect` from an `LcdXY` `origin` and an `LcdSize` `size`.
fn rect_origin_size(origin: LcdXY, size: LcdSize) -> Rect {
    if cfg!(debug_assertions) {
        Rect::new(
            i32::try_from(origin.x).expect("Origin X must fit in i32"),
            i32::try_from(origin.y).expect("Origin Y must fit in i32"),
            u32::try_from(size.width).expect("Width must fit in u32"),
            u32::try_from(size.height).expect("Height must fit in u32"),
        )
    } else {
        Rect::new(origin.x as i32, origin.y as i32, size.width as u32, size.height as u32)
    }
}

/// Computes the number of characters that fit within the given pixels `area`.
fn chars_in_area(glyph_size: LcdSize, area: SizeInPixels) -> CharsXY {
    CharsXY::new(
        area.width
            .checked_div(u16::try_from(glyph_size.width).expect("Glyph width must fit in u16"))
            .expect("Glyph size tested for non-zero during init"),
        area.height
            .checked_div(u16::try_from(glyph_size.height).expect("Glyph height must fit in u16"))
            .expect("Glyph size tested for non-zero during init"),
    )
}

/// Given an SDL `event`, converts it to a `Key` event if it is a key press; otherwise, returns
/// `None` for unknown events.
fn parse_event(event: Event) -> Option<Key> {
    let ctrl_mods = Mod::LCTRLMOD | Mod::RCTRLMOD;

    match event {
        Event::Quit { .. } => {
            // TODO(jmmv): This isn't really a key so we should be handling it in some other way.
            // For now, we recognize it here so that closing the window causes the interpreter to
            // exit... but that only works when the interpreter is waiting for input (which means
            // that this also confuses INKEY).
            Some(Key::Eof)
        }

        Event::KeyDown { keycode: Some(keycode), keymod, .. } => match keycode {
            Keycode::A if keymod.intersects(ctrl_mods) => Some(Key::Home),
            Keycode::B if keymod.intersects(ctrl_mods) => Some(Key::ArrowLeft),
            Keycode::C if keymod.intersects(ctrl_mods) => Some(Key::Interrupt),
            Keycode::D if keymod.intersects(ctrl_mods) => Some(Key::Eof),
            Keycode::E if keymod.intersects(ctrl_mods) => Some(Key::End),
            Keycode::F if keymod.intersects(ctrl_mods) => Some(Key::ArrowRight),
            Keycode::J if keymod.intersects(ctrl_mods) => Some(Key::NewLine),
            Keycode::M if keymod.intersects(ctrl_mods) => Some(Key::NewLine),
            Keycode::N if keymod.intersects(ctrl_mods) => Some(Key::ArrowDown),
            Keycode::P if keymod.intersects(ctrl_mods) => Some(Key::ArrowUp),

            Keycode::Backspace => Some(Key::Backspace),
            Keycode::End => Some(Key::End),
            Keycode::Escape => Some(Key::Escape),
            Keycode::Home => Some(Key::Home),
            Keycode::Return => Some(Key::NewLine),
            Keycode::Tab => Some(Key::Tab),

            Keycode::Down => Some(Key::ArrowDown),
            Keycode::Left => Some(Key::ArrowLeft),
            Keycode::Right => Some(Key::ArrowRight),
            Keycode::Up => Some(Key::ArrowUp),

            Keycode::PageDown => Some(Key::PageDown),
            Keycode::PageUp => Some(Key::PageUp),

            _ => None,
        },

        Event::TextInput { text, .. } => {
            let mut chars = text.chars();
            let first =
                chars.next().unwrap_or_else(|| panic!("Cannot handle TextInput event: {:?}", text));
            Some(Key::Char(first))
        }

        _ => None,
    }
}

/// Implementation of the EndBASIC console on top of an SDL2 window.
///
/// The current struct-based code is derived from how this used to be a direct implementation of
/// the `Console` trait and serves to keep track of all the state we need to maintain the console.
/// However, this is incomplete without the main driver loop in `run`, which waits for events and
/// manipulates the console.
struct Context {
    /// SDL2 library context.  Must remain alive for the lifetime of the console: if it is dropped
    /// early, all further SDL operations fail.
    #[cfg_attr(not(test), allow(unused))]
    sdl: Sdl,

    /// Event pump to read keyboard events from.
    event_pump: EventPump,

    /// Window that hosts the console.
    window: Window,

    /// Off-screen canvas in which to draw the console.  Use `present_canvas` to copy the contents
    /// of this surface onto the window.
    canvas: SurfaceCanvas<'static>,

    /// The pixel format used in the `canvas`; cached to avoid calls into SDL.
    pixel_format: PixelFormatEnum,

    /// The texture creator for the `canvas`; cached to avoid calls into SDL.
    texture_creator: TextureCreator<SurfaceContext<'static>>,

    /// Size of the console in pixels.
    size_pixels: SizeInPixels,
}

impl Context {
    /// Initializes a new SDL console.
    ///
    /// The console is sized to `resolution` pixels.  Uses `glyph_size` to calculate the size of the
    /// console in characters.
    ///
    /// There can only be one active `SdlConsole` at any given time given that this initializes and
    /// owns the SDL context.
    fn new(resolution: Resolution, glyph_size: LcdSize) -> io::Result<Self> {
        let sdl = sdl2::init().map_err(string_error_to_io_error)?;
        let event_pump = sdl.event_pump().map_err(string_error_to_io_error)?;
        let video = sdl.video().map_err(string_error_to_io_error)?;

        video.text_input().start();

        let mut title = format!("EndBASIC {}", env!("CARGO_PKG_VERSION"));
        let mut window = match resolution {
            Resolution::FullScreenDesktop => {
                let mut window = video.window(&title, 0, 0);
                window.fullscreen_desktop();
                window
            }
            Resolution::FullScreen(size) => {
                let mut window = video.window(&title, size.0.get(), size.1.get());
                window.fullscreen();
                window
            }
            Resolution::Windowed(size) => {
                let mut window = video.window(&title, size.0.get(), size.1.get());
                window.position_centered();
                window
            }
        }
        .opengl()
        .build()
        .map_err(window_build_error_to_io_error)?;

        let size_pixels = {
            let (width, height) = window.drawable_size();
            SizeInPixels::new(width.clamped_into(), height.clamped_into())
        };
        let size_chars = chars_in_area(glyph_size, size_pixels);

        write!(
            &mut title,
            " - {}x{} pixels, {}x{} chars",
            size_pixels.width, size_pixels.height, size_chars.x, size_chars.y
        )
        .map_err(fmt_error_to_io_error)?;
        window.set_title(&title).expect("There should have been no NULLs in the formatted title");

        let pixel_format = window.window_pixel_format();

        let surface =
            Surface::new(u32::from(size_pixels.width), u32::from(size_pixels.height), pixel_format)
                .map_err(string_error_to_io_error)?;
        let canvas = surface.into_canvas().map_err(string_error_to_io_error)?;
        let texture_creator = canvas.texture_creator();

        let mut ctx =
            Self { sdl, event_pump, window, canvas, pixel_format, texture_creator, size_pixels };
        ctx.present_canvas()?;
        Ok(ctx)
    }

    fn present_canvas(&mut self) -> io::Result<()> {
        let mut window_surface =
            self.window.surface(&self.event_pump).map_err(string_error_to_io_error)?;
        self.canvas
            .surface()
            .blit(None, &mut window_surface, None)
            .map_err(string_error_to_io_error)?;
        window_surface.finish().map_err(string_error_to_io_error)
    }

    fn get_info(&self) -> (LcdSize, usize) {
        let size = self.size_pixels;
        let pixel_size = self.pixel_format.byte_size_per_pixel();
        (LcdSize { width: usize::from(size.width), height: usize::from(size.height) }, pixel_size)
    }

    fn set_data(&mut self, x1y1: LcdXY, x2y2: LcdXY, data: &[u8]) -> io::Result<()> {
        let (xy, size) = to_xy_size(x1y1, x2y2);
        let rect = rect_origin_size(xy, size);
        let mut texture = self
            .texture_creator
            .create_texture_static(None, rect.width(), rect.height())
            .map_err(texture_value_error_to_io_error)?;
        let width = if cfg!(debug_assertions) {
            usize::try_from(rect.width()).expect("Width must fit in usize")
        } else {
            rect.width() as usize
        }
        .clamped_mul(self.pixel_format.byte_size_per_pixel());
        texture.update(None, data, width).map_err(update_texture_error_to_io_error)?;
        self.canvas.copy(&texture, None, rect).map_err(string_error_to_io_error)?;
        drop(texture);
        self.present_canvas()
    }
}

#[derive(Clone)]
struct SharedContext(Rc<RefCell<Context>>);

impl SharedContext {
    fn poll_event(&mut self) -> Option<Event> {
        (*self.0).borrow_mut().event_pump.poll_event()
    }

    fn get_info(&self) -> (LcdSize, usize) {
        (*self.0).borrow().get_info()
    }

    fn set_data(&mut self, x1y1: LcdXY, x2y2: LcdXY, data: &[u8]) -> io::Result<()> {
        (*self.0).borrow_mut().set_data(x1y1, x2y2, data)
    }

    #[cfg(test)]
    fn push_event(&mut self, ev: Event) -> io::Result<()> {
        let event_ss = (*self.0).borrow().sdl.event().map_err(string_error_to_io_error)?;
        event_ss.push_event(ev).map_err(string_error_to_io_error)
    }

    #[cfg(test)]
    fn save_bmp(&self, path: &Path) -> io::Result<()> {
        let ctx = (*self.0).borrow_mut();
        let surface = ctx.window.surface(&ctx.event_pump).map_err(string_error_to_io_error)?;
        surface.save_bmp(path).map_err(string_error_to_io_error)
    }
}

/// Representation of requests that the console host can handle.
pub(crate) enum Request {
    Exit,

    SetData(LcdXY, LcdXY, Vec<u8>),

    #[cfg(test)]
    PushEvent(Event),
    #[cfg(test)]
    SaveBmp(PathBuf),
}

/// Representation of responses that the host sends back to the client.
#[derive(Debug)]
pub(crate) enum Response {
    Empty(io::Result<()>),
    Info((LcdSize, usize)),
}

/// Runs the main graphics loop.
#[allow(clippy::too_many_arguments)]
pub(crate) fn run(
    resolution: Resolution,
    glyph_size: LcdSize,
    request_rx: Receiver<Request>,
    response_tx: SyncSender<Response>,
    on_key_tx: Sender<Key>,
    signals_tx: async_channel::Sender<Signal>,
) {
    let ctx = match Context::new(resolution, glyph_size) {
        Ok(ctx) => ctx,
        Err(e) => {
            response_tx.send(Response::Empty(Err(e))).expect("Channel must be alive");
            return;
        }
    };

    let mut ctx = SharedContext(Rc::from(RefCell::from(ctx)));

    response_tx.send(Response::Info(ctx.get_info())).expect("Channel must be alive");

    let mut budget = LOOP_POLL_BUDGET;
    loop {
        let mut did_something = false;

        match request_rx.try_recv() {
            Ok(request) => {
                let response = match request {
                    Request::Exit => break,

                    Request::SetData(x1y1, x2y2, data) => {
                        Response::Empty(ctx.set_data(x1y1, x2y2, &data))
                    }

                    #[cfg(test)]
                    Request::PushEvent(ev) => Response::Empty(ctx.push_event(ev)),

                    #[cfg(test)]
                    Request::SaveBmp(path) => Response::Empty(ctx.save_bmp(&path)),
                };

                // TODO(jmmv): This is inefficient.  Most of the operations above could probably
                // benefit from _not_ returning a response at all, being asynchronous from the
                // client perspective -- but the code is like this right now because it is adapted
                // from a previous version that was synchronous.
                response_tx.send(response).expect("Channel must be alive");

                did_something = true;
            }
            Err(TryRecvError::Empty) => (),
            Err(TryRecvError::Disconnected) => panic!("Channel must be alive"),
        }

        if let Some(event) = ctx.poll_event() {
            if let Some(key) = parse_event(event) {
                if key == Key::Interrupt {
                    // signals_tx is an async channel because that's what the execution engine
                    // needs.  This means that we cannot use a regular "send" here because we
                    // would need to await for it, which is a no-no because we are not in an
                    // async context.  Using "try_send" should be sufficient though given that
                    // the channel we use is not bounded.
                    signals_tx.try_send(Signal::Break).expect("Channel must be alive and not full")
                }

                on_key_tx.send(key).expect("Channel must be alive");
            }

            did_something = true;
        }

        if did_something {
            budget = LOOP_POLL_BUDGET;
        } else {
            if budget > 0 {
                budget -= 1;
            } else {
                thread::sleep(Duration::from_millis(LOOP_DELAY_MS));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Creates an `Event::KeyDown` struct for `keycode` with `keymod`.
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
    fn test_parse_event_ctrl_keycodes_with_extra_modifiers() {
        assert_eq!(
            Some(Key::Interrupt),
            parse_event(key_down(Keycode::C, Mod::LCTRLMOD | Mod::NUMMOD))
        );
        assert_eq!(Some(Key::Eof), parse_event(key_down(Keycode::D, Mod::RCTRLMOD | Mod::CAPSMOD)));
    }

    #[test]
    fn test_rect_origin_size() {
        assert_eq!(
            Rect::new(-31000, -32000, 63000, 64000),
            rect_origin_size(PixelsXY { x: -31000, y: -32000 }, SizeInPixels::new(63000, 64000))
        );
    }
}
