// EndBASIC
// Copyright 2022 Julio Merino
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

//! Background thread that runs the SDL main loop and acts as the host for the console.
//!
//! All communication with this thread happens via channels to ensure all SDL operations are invoked
//! from a single thread.

use crate::font::{font_error_to_io_error, MonospacedFont};
use crate::spec::Resolution;
use crate::string_error_to_io_error;
use async_trait::async_trait;
use endbasic_core::exec::Signal;
use endbasic_std::console::graphics::{ClampedInto, ClampedMul, InputOps, RasterInfo, RasterOps};
use endbasic_std::console::{
    CharsXY, ClearType, Console, GraphicsConsole, Key, PixelsXY, SizeInPixels, RGB,
};
use sdl2::event::Event;
use sdl2::keyboard::{Keycode, Mod};
use sdl2::pixels::{Color, PixelFormatEnum};
use sdl2::rect::{Point, Rect};
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
use std::path::PathBuf;
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
    io::Error::new(io::ErrorKind::Other, e)
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

/// Constructs an SDL `Point` from a `PixelsXY`.
fn point_xy(xy: PixelsXY) -> Point {
    Point::new(i32::from(xy.x), i32::from(xy.y))
}

/// Constructs an SDL `Rect` from a `PixelsXY` `origin` and a `PixelsSize` `size`.
fn rect_origin_size(origin: PixelsXY, size: SizeInPixels) -> Rect {
    Rect::new(
        i32::from(origin.x),
        i32::from(origin.y),
        u32::from(size.width),
        u32::from(size.height),
    )
}

/// Converts our own `RGB` type to an SDL `Color`.
fn rgb_to_color(rgb: RGB) -> Color {
    Color::RGB(rgb.0, rgb.1, rgb.2)
}

/// Given an SDL `event`, converts it to a `Key` event if it is a key press; otherwise, returns
/// `None` for unknown events.
fn parse_event(event: Event) -> Option<Key> {
    match event {
        Event::Quit { .. } => {
            // TODO(jmmv): This isn't really a key so we should be handling it in some other way.
            // For now, we recognize it here so that closing the window causes the interpreter to
            // exit... but that only works when the interpreter is waiting for input (which means
            // that this also confuses INKEY).
            Some(Key::Eof)
        }

        Event::KeyDown { keycode: Some(keycode), keymod, .. } => match keycode {
            Keycode::A if (keymod == Mod::LCTRLMOD || keymod == Mod::RCTRLMOD) => Some(Key::Home),
            Keycode::B if (keymod == Mod::LCTRLMOD || keymod == Mod::RCTRLMOD) => {
                Some(Key::ArrowLeft)
            }
            Keycode::C if (keymod == Mod::LCTRLMOD || keymod == Mod::RCTRLMOD) => {
                Some(Key::Interrupt)
            }
            Keycode::D if (keymod == Mod::LCTRLMOD || keymod == Mod::RCTRLMOD) => Some(Key::Eof),
            Keycode::E if (keymod == Mod::LCTRLMOD || keymod == Mod::RCTRLMOD) => Some(Key::End),
            Keycode::F if (keymod == Mod::LCTRLMOD || keymod == Mod::RCTRLMOD) => {
                Some(Key::ArrowRight)
            }
            Keycode::J if (keymod == Mod::LCTRLMOD || keymod == Mod::RCTRLMOD) => {
                Some(Key::NewLine)
            }
            Keycode::M if (keymod == Mod::LCTRLMOD || keymod == Mod::RCTRLMOD) => {
                Some(Key::NewLine)
            }
            Keycode::N if (keymod == Mod::LCTRLMOD || keymod == Mod::RCTRLMOD) => {
                Some(Key::ArrowDown)
            }
            Keycode::P if (keymod == Mod::LCTRLMOD || keymod == Mod::RCTRLMOD) => {
                Some(Key::ArrowUp)
            }

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

    /// Monospaced font to use in the console.
    font: MonospacedFont<'static>,

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

    /// Size of the console in characters.  This is derived from `size_pixels` and the `font` glyph
    /// metrics.
    size_chars: CharsXY,

    /// Current draw color.  Used only to track if we need to update the context.
    draw_color: RGB,
}

impl Context {
    /// Initializes a new SDL console.
    ///
    /// The console is sized to `resolution` pixels.  Also loads the desired font from
    /// `font_path` at `font_size` and uses it to calculate the size of the console in characters.
    ///
    /// There can only be one active `SdlConsole` at any given time given that this initializes and
    /// owns the SDL context.
    fn new(resolution: Resolution, font_path: PathBuf, font_size: u16) -> io::Result<Self> {
        let font = MonospacedFont::load(&font_path, font_size)?;

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
                let mut window = video.window(&title, size.0, size.1);
                window.fullscreen();
                window
            }
            Resolution::Windowed(size) => {
                let mut window = video.window(&title, size.0, size.1);
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
        let size_chars = font.chars_in_area(size_pixels);

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
        let mut canvas = surface.into_canvas().map_err(string_error_to_io_error)?;
        let texture_creator = canvas.texture_creator();

        let draw_color = RGB::default();
        canvas.set_draw_color(rgb_to_color(draw_color));

        Ok(Self {
            sdl,
            font,
            event_pump,
            window,
            canvas,
            pixel_format,
            texture_creator,
            size_pixels,
            size_chars,
            draw_color,
        })
    }

    /// Sets the draw color to `color` with caching.
    fn set_draw_color(&mut self, color: RGB) {
        if self.draw_color != color {
            self.canvas.set_draw_color(rgb_to_color(color));
            self.draw_color = color;
        }
    }

    /// Reads all visible pixels.  This is different from `real_pixels` in that it does not read
    /// any changes that haven't been written to the screen yet (such as the changes that happen
    /// when syncing is off).
    #[cfg(test)]
    fn read_visible_pixels(&mut self) -> io::Result<Vec<u8>> {
        let surface = self.window.surface(&self.event_pump).map_err(string_error_to_io_error)?;
        let mut copy = Surface::new(surface.width(), surface.height(), self.pixel_format)
            .map_err(string_error_to_io_error)?;
        surface.blit(None, &mut copy, None).map_err(string_error_to_io_error)?;
        copy.into_canvas()
            .map_err(string_error_to_io_error)?
            .read_pixels(None, self.pixel_format)
            .map_err(string_error_to_io_error)
    }
}

impl RasterOps for Context {
    type ID = (Vec<u8>, SizeInPixels);

    fn get_info(&self) -> RasterInfo {
        RasterInfo {
            size_chars: self.size_chars,
            size_pixels: self.size_pixels,
            glyph_size: self.font.glyph_size,
        }
    }

    fn clear(&mut self, color: RGB) -> io::Result<()> {
        self.set_draw_color(color);
        self.canvas.clear();
        Ok(())
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

    fn read_pixels(&mut self, xy: PixelsXY, size: SizeInPixels) -> io::Result<Self::ID> {
        let rect = rect_origin_size(xy, size);
        let data =
            self.canvas.read_pixels(rect, self.pixel_format).map_err(string_error_to_io_error)?;
        Ok((data, size))
    }

    fn put_pixels(&mut self, xy: PixelsXY, (data, size): &Self::ID) -> io::Result<()> {
        let rect = rect_origin_size(xy, *size);
        let mut texture = self
            .texture_creator
            .create_texture_static(None, rect.width(), rect.height())
            .map_err(texture_value_error_to_io_error)?;
        texture
            .update(
                None,
                data,
                usize::try_from(rect.width())
                    .expect("Width must fit in usize")
                    .clamped_mul(self.pixel_format.byte_size_per_pixel()),
            )
            .map_err(update_texture_error_to_io_error)?;
        self.canvas.copy(&texture, None, rect).map_err(string_error_to_io_error)
    }

    fn move_pixels(
        &mut self,
        x1y1: PixelsXY,
        x2y2: PixelsXY,
        size: SizeInPixels,
        color: RGB,
    ) -> io::Result<()> {
        let shifted = {
            let src = self.canvas.surface();
            let mut temp = Surface::new(src.width(), src.height(), self.pixel_format)
                .map_err(string_error_to_io_error)?;
            let src_rect = rect_origin_size(x1y1, size);
            let dst_rect = rect_origin_size(x2y2, size);
            temp.fill_rect(src_rect, rgb_to_color(color)).map_err(string_error_to_io_error)?;
            src.blit(src_rect, &mut temp, dst_rect).map_err(string_error_to_io_error)?;
            temp
        };
        shifted.blit(None, self.canvas.surface_mut(), None).map_err(string_error_to_io_error)?;
        Ok(())
    }

    fn write_text(
        &mut self,
        xy: PixelsXY,
        text: &str,
        fg_color: RGB,
        bg_color: RGB,
    ) -> io::Result<()> {
        debug_assert!(!text.is_empty(), "SDL does not like empty strings");

        let len = match u16::try_from(text.chars().count()) {
            Ok(v) => v,
            Err(_) => return Err(io::Error::new(io::ErrorKind::InvalidInput, "String too long")),
        };

        let surface = self
            .font
            .font
            .render(text)
            .shaded(fg_color, bg_color)
            .map_err(font_error_to_io_error)?;
        let texture = self
            .texture_creator
            .create_texture_from_surface(&surface)
            .map_err(texture_value_error_to_io_error)?;

        let rect = Rect::new(
            i32::from(xy.x),
            i32::from(xy.y),
            len.clamped_mul(self.font.glyph_size.width),
            u32::from(self.font.glyph_size.height),
        );
        self.canvas.copy(&texture, None, rect).map_err(string_error_to_io_error)
    }

    fn draw_circle(&mut self, center: PixelsXY, radius: u16, color: RGB) -> io::Result<()> {
        // This implements the [Midpoint circle
        // algorithm](https://en.wikipedia.org/wiki/Midpoint_circle_algorithm).

        fn point(canvas: &mut SurfaceCanvas<'static>, x: i16, y: i16) -> io::Result<()> {
            canvas
                .draw_point(Point::new(i32::from(x), i32::from(y)))
                .map_err(string_error_to_io_error)
        }

        let (diameter, radius): (i16, i16) = match radius.checked_mul(2) {
            Some(d) => match i16::try_from(d) {
                Ok(d) => (d, radius as i16),
                Err(_) => {
                    return Err(io::Error::new(io::ErrorKind::InvalidInput, "Radius is too big"))
                }
            },
            None => return Err(io::Error::new(io::ErrorKind::InvalidInput, "Radius is too big")),
        };

        let mut x: i16 = radius - 1;
        let mut y: i16 = 0;
        let mut tx: i16 = 1;
        let mut ty: i16 = 1;
        let mut e: i16 = tx - diameter;

        self.set_draw_color(color);
        while x >= y {
            point(&mut self.canvas, center.x + x, center.y - y)?;
            point(&mut self.canvas, center.x + x, center.y + y)?;
            point(&mut self.canvas, center.x - x, center.y - y)?;
            point(&mut self.canvas, center.x - x, center.y + y)?;
            point(&mut self.canvas, center.x + y, center.y - x)?;
            point(&mut self.canvas, center.x + y, center.y + x)?;
            point(&mut self.canvas, center.x - y, center.y - x)?;
            point(&mut self.canvas, center.x - y, center.y + x)?;

            if e <= 0 {
                y += 1;
                e += ty;
                ty += 2;
            }

            if e > 0 {
                x -= 1;
                tx += 2;
                e += tx - diameter;
            }
        }

        Ok(())
    }

    fn draw_circle_filled(&mut self, center: PixelsXY, radius: u16, color: RGB) -> io::Result<()> {
        // This implements the [Midpoint circle
        // algorithm](https://en.wikipedia.org/wiki/Midpoint_circle_algorithm).

        fn line(
            canvas: &mut SurfaceCanvas<'static>,
            x1: i16,
            y1: i16,
            x2: i16,
            y2: i16,
        ) -> io::Result<()> {
            canvas
                .draw_line(
                    Point::new(i32::from(x1), i32::from(y1)),
                    Point::new(i32::from(x2), i32::from(y2)),
                )
                .map_err(string_error_to_io_error)
        }

        if radius == 1 {
            self.set_draw_color(color);
            return self.canvas.draw_point(point_xy(center)).map_err(string_error_to_io_error);
        }

        let (diameter, radius): (i16, i16) = match radius.checked_mul(2) {
            Some(d) => match i16::try_from(d) {
                Ok(d) => (d, radius as i16),
                Err(_) => {
                    return Err(io::Error::new(io::ErrorKind::InvalidInput, "Radius is too big"))
                }
            },
            None => return Err(io::Error::new(io::ErrorKind::InvalidInput, "Radius is too big")),
        };

        let mut x: i16 = radius - 1;
        let mut y: i16 = 0;
        let mut tx: i16 = 1;
        let mut ty: i16 = 1;
        let mut e: i16 = tx - diameter;

        self.set_draw_color(color);
        while x >= y {
            line(&mut self.canvas, center.x + x, center.y - y, center.x + x, center.y + y)?;
            line(&mut self.canvas, center.x - x, center.y - y, center.x - x, center.y + y)?;
            line(&mut self.canvas, center.x + y, center.y - x, center.x + y, center.y + x)?;
            line(&mut self.canvas, center.x - y, center.y - x, center.x - y, center.y + x)?;

            if e <= 0 {
                y += 1;
                e += ty;
                ty += 2;
            }

            if e > 0 {
                x -= 1;
                tx += 2;
                e += tx - diameter;
            }
        }

        Ok(())
    }

    fn draw_line(&mut self, x1y1: PixelsXY, x2y2: PixelsXY, color: RGB) -> io::Result<()> {
        if x1y1 == x2y2 {
            // Paper over differences between platforms.  On Linux, this would paint a single dot,
            // but on Windows, it paints nothing.  For consistency with drawing a circle of radius
            // 0, and for consistency with the web interface, avoid painting anything here.
            return Ok(());
        }

        self.set_draw_color(color);
        self.canvas.draw_line(point_xy(x1y1), point_xy(x2y2)).map_err(string_error_to_io_error)
    }

    fn draw_pixel(&mut self, xy: PixelsXY, color: RGB) -> io::Result<()> {
        self.set_draw_color(color);
        self.canvas.draw_point(point_xy(xy)).map_err(string_error_to_io_error)
    }

    fn draw_rect(&mut self, xy: PixelsXY, size: SizeInPixels, color: RGB) -> io::Result<()> {
        let rect = rect_origin_size(xy, size);
        self.set_draw_color(color);
        self.canvas.draw_rect(rect).map_err(string_error_to_io_error)
    }

    fn draw_rect_filled(&mut self, xy: PixelsXY, size: SizeInPixels, color: RGB) -> io::Result<()> {
        let rect = rect_origin_size(xy, size);
        self.set_draw_color(color);
        self.canvas.fill_rect(rect).map_err(string_error_to_io_error)
    }
}

#[derive(Clone)]
struct SharedContext(Rc<RefCell<Context>>);

impl SharedContext {
    fn poll_event(&mut self) -> Option<Event> {
        (*self.0).borrow_mut().event_pump.poll_event()
    }

    #[cfg(test)]
    fn push_event(&mut self, ev: Event) -> io::Result<()> {
        let event_ss = (*self.0).borrow().sdl.event().map_err(string_error_to_io_error)?;
        event_ss.push_event(ev).map_err(string_error_to_io_error)
    }

    #[cfg(test)]
    fn raw_write(
        &mut self,
        text: &str,
        xy: PixelsXY,
        fg_color: RGB,
        bg_color: RGB,
    ) -> io::Result<()> {
        (*self.0).borrow_mut().write_text(xy, text, fg_color, bg_color)
    }

    #[cfg(test)]
    fn read_visible_pixels(&mut self) -> io::Result<(Vec<u8>, PixelFormatEnum)> {
        let mut ctx = (*self.0).borrow_mut();
        ctx.read_visible_pixels().map(|ps| (ps, ctx.pixel_format))
    }

    #[cfg(test)]
    fn save_bmp(&self, path: &Path) -> io::Result<()> {
        let ctx = (*self.0).borrow_mut();
        let surface = ctx.window.surface(&ctx.event_pump).map_err(string_error_to_io_error)?;
        surface.save_bmp(path).map_err(string_error_to_io_error)
    }
}

impl RasterOps for SharedContext {
    type ID = (Vec<u8>, SizeInPixels);

    fn get_info(&self) -> RasterInfo {
        self.0.borrow().get_info()
    }

    fn clear(&mut self, color: RGB) -> io::Result<()> {
        (*self.0).borrow_mut().clear(color)
    }

    fn present_canvas(&mut self) -> io::Result<()> {
        (*self.0).borrow_mut().present_canvas()
    }

    fn read_pixels(&mut self, xy: PixelsXY, size: SizeInPixels) -> io::Result<Self::ID> {
        (*self.0).borrow_mut().read_pixels(xy, size)
    }

    fn put_pixels(&mut self, xy: PixelsXY, data: &Self::ID) -> io::Result<()> {
        (*self.0).borrow_mut().put_pixels(xy, data)
    }

    fn move_pixels(
        &mut self,
        x1y1: PixelsXY,
        x2y2: PixelsXY,
        size: SizeInPixels,
        color: RGB,
    ) -> io::Result<()> {
        (*self.0).borrow_mut().move_pixels(x1y1, x2y2, size, color)
    }

    fn write_text(
        &mut self,
        xy: PixelsXY,
        text: &str,
        fg_color: RGB,
        bg_color: RGB,
    ) -> io::Result<()> {
        (*self.0).borrow_mut().write_text(xy, text, fg_color, bg_color)
    }

    fn draw_circle(&mut self, center: PixelsXY, radius: u16, color: RGB) -> io::Result<()> {
        (*self.0).borrow_mut().draw_circle(center, radius, color)
    }

    fn draw_circle_filled(&mut self, center: PixelsXY, radius: u16, color: RGB) -> io::Result<()> {
        (*self.0).borrow_mut().draw_circle_filled(center, radius, color)
    }

    fn draw_line(&mut self, x1y1: PixelsXY, x2y2: PixelsXY, color: RGB) -> io::Result<()> {
        (*self.0).borrow_mut().draw_line(x1y1, x2y2, color)
    }

    fn draw_pixel(&mut self, xy: PixelsXY, color: RGB) -> io::Result<()> {
        (*self.0).borrow_mut().draw_pixel(xy, color)
    }

    fn draw_rect(&mut self, xy: PixelsXY, size: SizeInPixels, color: RGB) -> io::Result<()> {
        (*self.0).borrow_mut().draw_rect(xy, size, color)
    }

    fn draw_rect_filled(&mut self, xy: PixelsXY, size: SizeInPixels, color: RGB) -> io::Result<()> {
        (*self.0).borrow_mut().draw_rect_filled(xy, size, color)
    }
}

/// Representation of requests that the console host can handle.
pub(crate) enum Request {
    Exit,

    Clear(ClearType),
    SetColor(Option<u8>, Option<u8>),
    EnterAlt,
    HideCursor,
    LeaveAlt,
    Locate(CharsXY),
    MoveWithinLine(i16),
    Print(String),
    ShowCursor,
    SizeChars,
    SizePixels,
    Write(String),
    DrawCircle(PixelsXY, u16),
    DrawCircleFilled(PixelsXY, u16),
    DrawLine(PixelsXY, PixelsXY),
    DrawPixel(PixelsXY),
    DrawRect(PixelsXY, PixelsXY),
    DrawRectFilled(PixelsXY, PixelsXY),
    SyncNow,
    SetSync(bool),

    #[cfg(test)]
    PushEvent(Event),
    #[cfg(test)]
    RawWrite(String, PixelsXY, RGB, RGB),
    #[cfg(test)]
    ReadVisiblePixels,
    #[cfg(test)]
    SaveBmp(PathBuf),
}

/// Representation of responses that the host sends back to the client.
#[derive(Debug)]
pub(crate) enum Response {
    Empty(io::Result<()>),
    SizeChars(CharsXY),
    SizePixels(SizeInPixels),
    SetSync(io::Result<bool>),

    #[cfg(test)]
    Pixels(io::Result<(Vec<u8>, PixelFormatEnum)>),
}

/// Implementation of `InputOps` that should never be used.
// TODO(jmmv): This is necessary because the host-level console implementation requires these
// methods to be present but the input operations are handled in the client-side console.  This
// might mean we need a better design.
struct NoopInputOps {}

#[async_trait(?Send)]
impl InputOps for NoopInputOps {
    async fn poll_key(&mut self) -> io::Result<Option<Key>> {
        unreachable!();
    }

    async fn read_key(&mut self) -> io::Result<Key> {
        unreachable!();
    }
}

pub(crate) fn run(
    resolution: Resolution,
    font_path: PathBuf,
    font_size: u16,
    request_rx: Receiver<Request>,
    response_tx: SyncSender<Response>,
    on_key_tx: Sender<Key>,
    signals_tx: async_channel::Sender<Signal>,
) {
    let ctx = match Context::new(resolution, font_path, font_size) {
        Ok(ctx) => ctx,
        Err(e) => {
            response_tx.send(Response::Empty(Err(e))).expect("Channel must be alive");
            return;
        }
    };

    let info = ctx.get_info();
    let mut ctx = SharedContext(Rc::from(RefCell::from(ctx)));

    let input = NoopInputOps {};
    let mut console =
        GraphicsConsole::new(input, ctx.clone()).expect("Console initialization must succeed");

    response_tx.send(Response::Empty(Ok(()))).expect("Channel must be alive");

    let mut budget = LOOP_POLL_BUDGET;
    loop {
        let mut did_something = false;

        match request_rx.try_recv() {
            Ok(request) => {
                let response = match request {
                    Request::Exit => break,

                    Request::Clear(how) => Response::Empty(console.clear(how)),
                    Request::SetColor(fg, bg) => Response::Empty(console.set_color(fg, bg)),
                    Request::EnterAlt => Response::Empty(console.enter_alt()),
                    Request::HideCursor => Response::Empty(console.hide_cursor()),
                    Request::LeaveAlt => Response::Empty(console.leave_alt()),
                    Request::Locate(pos) => Response::Empty(console.locate(pos)),
                    Request::MoveWithinLine(off) => Response::Empty(console.move_within_line(off)),
                    Request::Print(text) => Response::Empty(console.print(&text)),
                    Request::ShowCursor => Response::Empty(console.show_cursor()),
                    Request::SizeChars => Response::SizeChars(info.size_chars),
                    Request::SizePixels => Response::SizePixels(info.size_pixels),
                    Request::Write(text) => Response::Empty(console.write(&text)),
                    Request::DrawCircle(center, radius) => {
                        Response::Empty(console.draw_circle(center, radius))
                    }
                    Request::DrawCircleFilled(center, radius) => {
                        Response::Empty(console.draw_circle_filled(center, radius))
                    }
                    Request::DrawLine(x1y1, x2y2) => Response::Empty(console.draw_line(x1y1, x2y2)),
                    Request::DrawPixel(xy) => Response::Empty(console.draw_pixel(xy)),
                    Request::DrawRect(x1y1, x2y2) => Response::Empty(console.draw_rect(x1y1, x2y2)),
                    Request::DrawRectFilled(x1y1, x2y2) => {
                        Response::Empty(console.draw_rect_filled(x1y1, x2y2))
                    }
                    Request::SyncNow => Response::Empty(console.sync_now()),
                    Request::SetSync(enabled) => Response::SetSync(console.set_sync(enabled)),

                    #[cfg(test)]
                    Request::PushEvent(ev) => Response::Empty(ctx.push_event(ev)),

                    #[cfg(test)]
                    Request::RawWrite(text, start, fg_color, bg_color) => {
                        Response::Empty(ctx.raw_write(&text, start, fg_color, bg_color))
                    }

                    #[cfg(test)]
                    Request::ReadVisiblePixels => Response::Pixels(ctx.read_visible_pixels()),

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

    #[test]
    fn test_rect_origin_size() {
        assert_eq!(
            Rect::new(-31000, -32000, 63000, 64000),
            rect_origin_size(PixelsXY { x: -31000, y: -32000 }, SizeInPixels::new(63000, 64000))
        );
    }
}
