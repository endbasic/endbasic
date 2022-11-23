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
use crate::{string_error_to_io_error, SizeInPixels};
use endbasic_core::exec::Signal;
use endbasic_std::console::{ansi_color_to_rgb, CharsXY, ClearType, Key, LineBuffer, PixelsXY};
use sdl2::event::Event;
use sdl2::keyboard::{Keycode, Mod};
use sdl2::pixels::{Color, PixelFormatEnum};
use sdl2::rect::{Point, Rect};
use sdl2::render::{SurfaceCanvas, TextureCreator, TextureValueError, UpdateTextureError};
use sdl2::surface::{Surface, SurfaceContext};
use sdl2::video::{Window, WindowBuildError};
use sdl2::{EventPump, Sdl};
use std::convert::TryFrom;
use std::fmt::{self, Write};
use std::io;
#[cfg(test)]
use std::path::Path;
use std::path::PathBuf;
use std::sync::mpsc::{Receiver, Sender, SyncSender, TryRecvError};
use std::thread;
use std::time::Duration;

/// Default foreground color, used at console creation time and when requesting the default color
/// via the `COLOR` command.
const DEFAULT_FG_COLOR: Color = Color::WHITE;

/// Default background color, used at console creation time and when requesting the default color
/// via the `COLOR` command.
const DEFAULT_BG_COLOR: Color = Color::BLACK;

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

/// Conversion between types with silent value clamping.
trait ClampedInto<T> {
    /// Converts self into `T` capping values at `T`'s maximum or minimum boundaries.
    fn clamped_into(self) -> T;
}

impl ClampedInto<u16> for u32 {
    fn clamped_into(self) -> u16 {
        if self > u32::from(u16::MAX) {
            u16::MAX
        } else {
            self as u16
        }
    }
}

/// Multiplication of values into a narrower type with silent value clamping.
trait ClampedMul<T, O> {
    /// Multiplies self by `rhs` and clamps the result to fit in `O`.
    fn clamped_mul(self, rhs: T) -> O;
}

impl ClampedMul<u16, i16> for u16 {
    fn clamped_mul(self, rhs: u16) -> i16 {
        let product = u32::from(self) * u32::from(rhs);
        if product > i16::MAX as u32 {
            i16::MAX
        } else {
            product as i16
        }
    }
}

impl ClampedMul<u16, i32> for u16 {
    fn clamped_mul(self, rhs: u16) -> i32 {
        match i32::from(self).checked_mul(i32::from(rhs)) {
            Some(v) => v,
            None => i32::MAX,
        }
    }
}

impl ClampedMul<u16, u32> for u16 {
    fn clamped_mul(self, rhs: u16) -> u32 {
        u32::from(self).checked_mul(u32::from(rhs)).expect("Result must have fit")
    }
}

impl ClampedMul<usize, usize> for usize {
    fn clamped_mul(self, rhs: usize) -> usize {
        match self.checked_mul(rhs) {
            Some(v) => v,
            None => usize::MAX,
        }
    }
}

impl ClampedMul<SizeInPixels, PixelsXY> for CharsXY {
    fn clamped_mul(self, rhs: SizeInPixels) -> PixelsXY {
        PixelsXY { x: self.x.clamped_mul(rhs.width), y: self.y.clamped_mul(rhs.height) }
    }
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

/// Constructs an SDL `Rect` from two `PixelsXY` points.
fn rect_points(x1y1: PixelsXY, x2y2: PixelsXY) -> Rect {
    let (x1, x2) = if x1y1.x < x2y2.x { (x1y1.x, x2y2.x) } else { (x2y2.x, x1y1.x) };
    let (y1, y2) = if x1y1.y < x2y2.y { (x1y1.y, x2y2.y) } else { (x2y2.y, x1y1.y) };

    let width =
        u32::try_from(i32::from(x2) - i32::from(x1)).expect("Width must have been non-negative");
    let height =
        u32::try_from(i32::from(y2) - i32::from(y1)).expect("Height must have been non-negative");
    let x1 = i32::from(x1);
    let y1 = i32::from(y1);

    Rect::new(x1, y1, width, height)
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

    /// Location of the cursor.
    cursor_pos: CharsXY,

    /// Whether the cursor is visible or not.
    cursor_visible: bool,

    /// Raw pixels at the cursor position before the cursor was drawn.  Used to restore the previous
    /// contents when the cursor moves.
    cursor_backup: Vec<u8>,

    /// Current foreground color.  Used for text and graphical rendering.
    fg_color: Color,

    /// Current background color.  Used to clear text.
    bg_color: Color,

    /// State of the console right before entering the "alternate" console.
    alt_backup: Option<(Vec<u8>, CharsXY, Color, Color)>,

    /// Whether video syncing is enabled or not.
    sync_enabled: bool,
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
            SizeInPixels { width: width.clamped_into(), height: height.clamped_into() }
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
        let canvas = surface.into_canvas().map_err(string_error_to_io_error)?;
        let texture_creator = canvas.texture_creator();

        let mut console = Self {
            sdl,
            font,
            event_pump,
            window,
            canvas,
            pixel_format,
            texture_creator,
            size_pixels,
            size_chars,
            cursor_pos: CharsXY::default(),
            cursor_visible: true,
            cursor_backup: vec![],
            bg_color: DEFAULT_BG_COLOR,
            fg_color: DEFAULT_FG_COLOR,
            alt_backup: None,
            sync_enabled: true,
        };

        console.clear(ClearType::All)?;

        Ok(console)
    }

    /// Renders the current contents of `self.canvas` onto the output window irrespective of the
    /// status of the sync flag.
    fn force_present_canvas(&mut self) -> io::Result<()> {
        let mut window_surface =
            self.window.surface(&self.event_pump).map_err(string_error_to_io_error)?;
        self.canvas
            .surface()
            .blit(None, &mut window_surface, None)
            .map_err(string_error_to_io_error)?;
        window_surface.finish().map_err(string_error_to_io_error)
    }

    /// Renders the current contents of `self.canvas` onto the output window.
    fn present_canvas(&mut self) -> io::Result<()> {
        if self.sync_enabled {
            self.force_present_canvas()
        } else {
            Ok(())
        }
    }

    /// Draws the cursor at the current position and saves the previous contents of the screen so
    /// that `clear_cursor` can restore them.
    ///
    /// Does not present the canvas.
    fn draw_cursor(&mut self) -> io::Result<()> {
        if !self.cursor_visible || !self.sync_enabled {
            return Ok(());
        }

        let rect = rect_origin_size(
            self.cursor_pos.clamped_mul(self.font.glyph_size),
            self.font.glyph_size,
        );

        assert!(self.cursor_backup.is_empty());
        self.cursor_backup =
            self.canvas.read_pixels(rect, self.pixel_format).map_err(string_error_to_io_error)?;

        self.canvas.set_draw_color(self.fg_color);
        self.canvas.fill_rect(rect).map_err(string_error_to_io_error)?;
        Ok(())
    }

    /// Clears the cursor at the current position by restoring the contents of the screen saved by
    /// an earlier call to `draw_cursor`.
    ///
    /// Does not present the canvas.
    fn clear_cursor(&mut self) -> io::Result<()> {
        if !self.cursor_visible || !self.sync_enabled || self.cursor_backup.is_empty() {
            return Ok(());
        }

        let rect = rect_origin_size(
            self.cursor_pos.clamped_mul(self.font.glyph_size),
            self.font.glyph_size,
        );

        let mut texture = self
            .texture_creator
            .create_texture_static(None, rect.width(), rect.height())
            .map_err(texture_value_error_to_io_error)?;
        texture
            .update(
                None,
                &self.cursor_backup,
                usize::try_from(rect.width())
                    .expect("Width must fit in usize")
                    .clamped_mul(self.pixel_format.byte_size_per_pixel()),
            )
            .map_err(update_texture_error_to_io_error)?;
        self.canvas.copy(&texture, None, rect).map_err(string_error_to_io_error)?;
        self.cursor_backup.clear();
        Ok(())
    }

    /// Moves the cursor to beginning of the next line, scrolling the console if necessary.
    ///
    /// Does not clear nor draw the cursor, and also does not present the canvas.
    fn open_line(&mut self) -> io::Result<()> {
        if self.cursor_pos.y < self.size_chars.y - 1 {
            self.cursor_pos.x = 0;
            self.cursor_pos.y += 1;
            return Ok(());
        }

        let mut shifted = {
            let src = self.canvas.surface();
            let mut temp = Surface::new(src.width(), src.height(), self.pixel_format)
                .map_err(string_error_to_io_error)?;
            src.blit(
                Rect::new(
                    0,
                    i32::from(self.font.glyph_size.height),
                    u32::from(self.size_pixels.width),
                    u32::from(self.size_pixels.height - self.font.glyph_size.height),
                ),
                &mut temp,
                None,
            )
            .map_err(string_error_to_io_error)?;
            temp
        };
        shifted
            .fill_rect(
                Rect::new(
                    0,
                    i32::from(self.size_pixels.height - self.font.glyph_size.height),
                    u32::from(self.size_pixels.width),
                    u32::from(self.font.glyph_size.height),
                ),
                self.bg_color,
            )
            .map_err(string_error_to_io_error)?;
        shifted.blit(None, self.canvas.surface_mut(), None).map_err(string_error_to_io_error)?;

        self.cursor_pos.x = 0;
        Ok(())
    }

    /// Renders the given text at the `start` position.
    ///
    /// Does not handle overflow nor scrolling, and also does not present the canvas.
    fn raw_write(&mut self, text: &str, start: PixelsXY) -> io::Result<()> {
        debug_assert!(!text.is_empty(), "SDL does not like empty strings");

        let len = match u16::try_from(text.chars().count()) {
            Ok(v) => v,
            Err(_) => return Err(io::Error::new(io::ErrorKind::InvalidInput, "String too long")),
        };

        let surface = self
            .font
            .font
            .render(text)
            .shaded(self.fg_color, self.bg_color)
            .map_err(font_error_to_io_error)?;
        let texture = self
            .texture_creator
            .create_texture_from_surface(&surface)
            .map_err(texture_value_error_to_io_error)?;

        let rect = Rect::new(
            i32::from(start.x),
            i32::from(start.y),
            len.clamped_mul(self.font.glyph_size.width),
            u32::from(self.font.glyph_size.height),
        );
        self.canvas.copy(&texture, None, rect).map_err(string_error_to_io_error)?;

        Ok(())
    }

    /// Renders the given text at the current cursor position, with wrapping and
    /// scrolling if necessary.
    ///
    /// Does not present the canvas.
    fn raw_write_wrapped(&mut self, text: &str) -> io::Result<()> {
        debug_assert!(!text.is_empty(), "SDL does not like empty strings");

        let mut line_buffer = LineBuffer::from(text);

        loop {
            let fit_chars = self.size_chars.x - self.cursor_pos.x;

            let remaining = line_buffer.split_off(usize::from(fit_chars));
            let len = line_buffer.len();
            self.raw_write(
                &line_buffer.into_inner(),
                self.cursor_pos.clamped_mul(self.font.glyph_size),
            )?;
            self.cursor_pos.x +=
                u16::try_from(len).expect("Partial length was computed to fit on the screen");

            line_buffer = remaining;
            if line_buffer.is_empty() {
                break;
            } else {
                self.open_line()?;
            }
        }

        Ok(())
    }

    /// Handler for a `Request::Clear`.
    fn clear(&mut self, how: ClearType) -> io::Result<()> {
        self.canvas.set_draw_color(self.bg_color);
        match how {
            ClearType::All => {
                self.canvas.clear();
                self.cursor_pos.y = 0;
                self.cursor_pos.x = 0;

                // We intentionally do not draw the cursor here and wait until the first time we
                // write text to the console.  This allows the user to clear the screen and render
                // graphics if they want to without interference.
                self.cursor_backup.clear();
            }
            ClearType::CurrentLine => {
                self.clear_cursor()?;
                self.canvas
                    .fill_rect(Rect::new(
                        0,
                        self.cursor_pos.y.clamped_mul(self.font.glyph_size.height),
                        u32::from(self.size_pixels.width),
                        u32::from(self.font.glyph_size.height),
                    ))
                    .map_err(string_error_to_io_error)?;
                self.cursor_pos.x = 0;
                self.draw_cursor()?;
            }
            ClearType::PreviousChar => {
                if self.cursor_pos.x > 0 {
                    self.clear_cursor()?;
                    let previous_pos = CharsXY::new(self.cursor_pos.x - 1, self.cursor_pos.y);
                    self.canvas
                        .fill_rect(rect_origin_size(
                            previous_pos.clamped_mul(self.font.glyph_size),
                            self.font.glyph_size,
                        ))
                        .map_err(string_error_to_io_error)?;
                    self.cursor_pos = previous_pos;
                    self.draw_cursor()?;
                }
            }
            ClearType::UntilNewLine => {
                self.clear_cursor()?;
                let pos = self.cursor_pos.clamped_mul(self.font.glyph_size);
                debug_assert!(pos.x >= 0, "Inputs to pos are unsigned");
                debug_assert!(pos.y >= 0, "Inputs to pos are unsigned");
                let height = self.font.glyph_size.height;
                self.canvas
                    .fill_rect(Rect::new(
                        i32::from(pos.x),
                        i32::from(pos.y),
                        u32::try_from(i32::from(self.size_pixels.width) - i32::from(pos.x))
                            .expect("pos must have been positive"),
                        u32::from(height),
                    ))
                    .map_err(string_error_to_io_error)?;
                self.draw_cursor()?;
            }
        }

        self.present_canvas()
    }

    /// Handler for a `Request::Color`.
    fn color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()> {
        self.fg_color = match fg {
            Some(fg) => {
                let rgb = ansi_color_to_rgb(fg);
                Color::RGB(rgb.0, rgb.1, rgb.2)
            }
            None => DEFAULT_FG_COLOR,
        };

        self.bg_color = match bg {
            Some(bg) => {
                let rgb = ansi_color_to_rgb(bg);
                Color::RGB(rgb.0, rgb.1, rgb.2)
            }
            None => DEFAULT_BG_COLOR,
        };

        Ok(())
    }

    /// Handler for a `Request::EnterAlt`.
    fn enter_alt(&mut self) -> io::Result<()> {
        if self.alt_backup.is_some() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Cannot nest alternate screens",
            ));
        }

        let pixels =
            self.canvas.read_pixels(None, self.pixel_format).map_err(string_error_to_io_error)?;
        self.alt_backup = Some((pixels, self.cursor_pos, self.fg_color, self.bg_color));

        self.clear(ClearType::All)
    }

    /// Handler for a `Request::HideCursor`.
    fn hide_cursor(&mut self) -> io::Result<()> {
        self.clear_cursor()?;
        self.cursor_visible = false;
        self.present_canvas()
    }

    /// Handler for a `Request::LeaveAlt`.
    fn leave_alt(&mut self) -> io::Result<()> {
        let (pixels, cursor_pos, fg_color, bg_color) = match self.alt_backup.take() {
            Some(t) => t,
            None => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "Cannot leave alternate screen; not entered",
                ))
            }
        };

        self.clear_cursor()?;

        {
            let mut texture = self
                .texture_creator
                .create_texture_static(
                    None,
                    u32::from(self.size_pixels.width),
                    u32::from(self.size_pixels.height),
                )
                .map_err(texture_value_error_to_io_error)?;
            texture
                .update(
                    None,
                    &pixels,
                    usize::from(self.size_pixels.width)
                        .clamped_mul(self.pixel_format.byte_size_per_pixel()),
                )
                .map_err(update_texture_error_to_io_error)?;

            self.canvas.clear();
            self.canvas.copy(&texture, None, None).map_err(string_error_to_io_error)?;
        }

        self.cursor_pos = cursor_pos;
        self.fg_color = fg_color;
        self.bg_color = bg_color;
        self.draw_cursor()?;
        self.present_canvas()?;

        debug_assert!(self.alt_backup.is_none());
        Ok(())
    }

    /// Handler for a `Request::Locate`.
    fn locate(&mut self, pos: CharsXY) -> io::Result<()> {
        self.clear_cursor()?;
        self.cursor_pos = pos;
        self.draw_cursor()?;
        self.present_canvas()
    }

    /// Handler for a `Request::MoveWithinLine`.
    fn move_within_line(&mut self, off: i16) -> io::Result<()> {
        self.clear_cursor()?;
        if off < 0 {
            self.cursor_pos.x -= -off as u16;
        } else {
            self.cursor_pos.x += off as u16;
        }
        self.draw_cursor()?;
        self.present_canvas()
    }

    /// Handler for a `Request::PushEvent`.
    #[cfg(test)]
    fn push_event(&self, ev: Event) -> io::Result<()> {
        let event_ss = self.sdl.event().map_err(string_error_to_io_error)?;
        event_ss.push_event(ev).map_err(string_error_to_io_error)
    }

    /// Handler for a `Request::Print`.
    fn print(&mut self, text: &str) -> io::Result<()> {
        debug_assert!(
            !endbasic_std::console::has_control_chars(text),
            "Must have been stripped off by the client"
        );

        self.clear_cursor()?;
        if !text.is_empty() {
            self.raw_write_wrapped(text)?;
        }
        self.open_line()?;
        self.draw_cursor()?;
        self.present_canvas()
    }

    /// Handler for a `Request::ReadPixels`.
    #[cfg(test)]
    fn read_pixels(&self) -> io::Result<Vec<u8>> {
        let surface = self.window.surface(&self.event_pump).map_err(string_error_to_io_error)?;
        let mut copy = Surface::new(surface.width(), surface.height(), self.pixel_format)
            .map_err(string_error_to_io_error)?;
        surface.blit(None, &mut copy, None).map_err(string_error_to_io_error)?;
        copy.into_canvas()
            .map_err(string_error_to_io_error)?
            .read_pixels(None, self.pixel_format)
            .map_err(string_error_to_io_error)
    }

    /// Handler for a `Request::SaveBmp`.
    #[cfg(test)]
    fn save_bmp(&self, path: &Path) -> io::Result<()> {
        let surface = self.window.surface(&self.event_pump).map_err(string_error_to_io_error)?;
        surface.save_bmp(path).map_err(string_error_to_io_error)
    }

    /// Handler for a `Request::ShowCursor`.
    fn show_cursor(&mut self) -> io::Result<()> {
        if !self.cursor_visible {
            self.cursor_visible = true;
            if let Err(e) = self.draw_cursor() {
                self.cursor_visible = false;
                return Err(e);
            }
        }
        self.present_canvas()
    }

    /// Handler for a `Request::Write`.
    fn write(&mut self, text: &str) -> io::Result<()> {
        debug_assert!(
            !endbasic_std::console::has_control_chars(text),
            "Must have been stripped off by the client"
        );

        if text.is_empty() {
            return Ok(());
        }

        self.clear_cursor()?;
        self.raw_write_wrapped(text)?;
        self.draw_cursor()?;
        self.present_canvas()
    }

    /// Handler for a `Request::DrawLine`.
    fn draw_line(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        self.canvas.set_draw_color(self.fg_color);
        self.canvas.draw_line(point_xy(x1y1), point_xy(x2y2)).map_err(string_error_to_io_error)?;
        self.present_canvas()
    }

    /// Handler for a `Request::DrawPixel`.
    fn draw_pixel(&mut self, xy: PixelsXY) -> io::Result<()> {
        self.canvas.set_draw_color(self.fg_color);
        self.canvas.draw_point(point_xy(xy)).map_err(string_error_to_io_error)?;
        self.present_canvas()
    }

    /// Handler for a `Request::DrawRect`.
    fn draw_rect(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        let rect = rect_points(x1y1, x2y2);
        self.canvas.set_draw_color(self.fg_color);
        self.canvas.draw_rect(rect).map_err(string_error_to_io_error)?;
        self.present_canvas()
    }

    /// Handler for a `Request::DrawRectFilled`.
    fn draw_rect_filled(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        let rect = rect_points(x1y1, x2y2);
        self.canvas.set_draw_color(self.fg_color);
        self.canvas.fill_rect(rect).map_err(string_error_to_io_error)?;
        self.present_canvas()
    }

    /// Handler for a `Request::SyncNow`.
    fn sync_now(&mut self) -> io::Result<()> {
        if self.sync_enabled {
            Ok(())
        } else {
            self.force_present_canvas()
        }
    }

    /// Handler for a `Request::SetSync`.
    fn set_sync(&mut self, enabled: bool) -> io::Result<()> {
        if !self.sync_enabled {
            self.force_present_canvas()?;
        }
        self.sync_enabled = enabled;
        Ok(())
    }
}

/// Representation of requests that the console host can handle.
pub(crate) enum Request {
    Exit,

    Clear(ClearType),
    Color(Option<u8>, Option<u8>),
    EnterAlt,
    HideCursor,
    LeaveAlt,
    Locate(CharsXY),
    MoveWithinLine(i16),
    Print(String),
    ShowCursor,
    Size,
    Write(String),
    DrawLine(PixelsXY, PixelsXY),
    DrawPixel(PixelsXY),
    DrawRect(PixelsXY, PixelsXY),
    DrawRectFilled(PixelsXY, PixelsXY),
    SyncNow,
    SetSync(bool),

    #[cfg(test)]
    PushEvent(Event),
    #[cfg(test)]
    RawWrite(String, PixelsXY),
    #[cfg(test)]
    ReadPixels,
    #[cfg(test)]
    SaveBmp(PathBuf),
}

/// Representation of responses that the host sends back to the client.
#[derive(Debug)]
pub(crate) enum Response {
    Empty(io::Result<()>),
    Size(CharsXY),

    #[cfg(test)]
    Pixels(io::Result<(Vec<u8>, PixelFormatEnum)>),
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
    let mut ctx = match Context::new(resolution, font_path, font_size) {
        Ok(ctx) => ctx,
        Err(e) => {
            response_tx.send(Response::Empty(Err(e))).expect("Channel must be alive");
            return;
        }
    };

    response_tx.send(Response::Empty(Ok(()))).expect("Channel must be alive");

    let mut budget = LOOP_POLL_BUDGET;
    loop {
        let mut did_something = false;

        match request_rx.try_recv() {
            Ok(request) => {
                let response = match request {
                    Request::Exit => break,

                    Request::Clear(how) => Response::Empty(ctx.clear(how)),
                    Request::Color(fg, bg) => Response::Empty(ctx.color(fg, bg)),
                    Request::EnterAlt => Response::Empty(ctx.enter_alt()),
                    Request::HideCursor => Response::Empty(ctx.hide_cursor()),
                    Request::LeaveAlt => Response::Empty(ctx.leave_alt()),
                    Request::Locate(pos) => Response::Empty(ctx.locate(pos)),
                    Request::MoveWithinLine(off) => Response::Empty(ctx.move_within_line(off)),
                    Request::Print(text) => Response::Empty(ctx.print(&text)),
                    Request::ShowCursor => Response::Empty(ctx.show_cursor()),
                    Request::Size => Response::Size(ctx.size_chars),
                    Request::Write(text) => Response::Empty(ctx.write(&text)),
                    Request::DrawLine(x1y1, x2y2) => Response::Empty(ctx.draw_line(x1y1, x2y2)),
                    Request::DrawPixel(xy) => Response::Empty(ctx.draw_pixel(xy)),
                    Request::DrawRect(x1y1, x2y2) => Response::Empty(ctx.draw_rect(x1y1, x2y2)),
                    Request::DrawRectFilled(x1y1, x2y2) => {
                        Response::Empty(ctx.draw_rect_filled(x1y1, x2y2))
                    }
                    Request::SyncNow => Response::Empty(ctx.sync_now()),
                    Request::SetSync(enabled) => Response::Empty(ctx.set_sync(enabled)),

                    #[cfg(test)]
                    Request::PushEvent(ev) => Response::Empty(ctx.push_event(ev)),

                    #[cfg(test)]
                    Request::RawWrite(text, start) => Response::Empty(ctx.raw_write(&text, start)),

                    #[cfg(test)]
                    Request::ReadPixels => {
                        Response::Pixels(ctx.read_pixels().map(|ps| (ps, ctx.pixel_format)))
                    }

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

        if let Some(event) = ctx.event_pump.poll_event() {
            if let Some(key) = parse_event(event) {
                match key {
                    Key::Interrupt => {
                        // signals_tx is an async channel because that's what the execution engine
                        // needs.  This means that we cannot use a regular "send" here because we
                        // would need to await for it, which is a no-no because we are not in an
                        // async context.  Using "try_send" should be sufficient though given that
                        // the channel we use is not bounded.
                        signals_tx
                            .try_send(Signal::Break)
                            .expect("Channel must be alive and not full")
                    }
                    key => on_key_tx.send(key).expect("Channel must be alive"),
                }
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
    fn test_clamp_into_u32_u16() {
        assert_eq!(0u16, 0u32.clamped_into());
        assert_eq!(10u16, 10u32.clamped_into());
        assert_eq!(u16::MAX, u32::from(u16::MAX).clamped_into());
        assert_eq!(u16::MAX, u32::MAX.clamped_into());
    }

    #[test]
    fn test_clamped_mul_u16_u16_i16() {
        assert_eq!(0i16, ClampedMul::<u16, i16>::clamped_mul(0u16, 0u16));
        assert_eq!(55i16, ClampedMul::<u16, i16>::clamped_mul(11u16, 5u16));
        assert_eq!(i16::MAX, ClampedMul::<u16, i16>::clamped_mul(u16::MAX, u16::MAX));
    }

    #[test]
    fn test_clamped_mul_u16_u16_i32() {
        assert_eq!(0i32, ClampedMul::<u16, i32>::clamped_mul(0u16, 0u16));
        assert_eq!(55i32, ClampedMul::<u16, i32>::clamped_mul(11u16, 5u16));
        assert_eq!(i32::MAX, ClampedMul::<u16, i32>::clamped_mul(u16::MAX, u16::MAX));
    }

    #[test]
    fn test_clamped_mul_u16_u16_u32() {
        assert_eq!(0u32, ClampedMul::<u16, u32>::clamped_mul(0u16, 0u16));
        assert_eq!(55u32, ClampedMul::<u16, u32>::clamped_mul(11u16, 5u16));
        assert_eq!(4294836225u32, ClampedMul::<u16, u32>::clamped_mul(u16::MAX, u16::MAX));
    }

    #[test]
    fn test_clamped_mul_usize_usize_usize() {
        assert_eq!(0, ClampedMul::<usize, usize>::clamped_mul(0, 0));
        assert_eq!(55, ClampedMul::<usize, usize>::clamped_mul(11, 5));
        assert_eq!(usize::MAX, ClampedMul::<usize, usize>::clamped_mul(usize::MAX, usize::MAX));
    }

    #[test]
    fn test_rect_origin_size() {
        assert_eq!(
            Rect::new(-31000, -32000, 63000, 64000),
            rect_origin_size(
                PixelsXY { x: -31000, y: -32000 },
                SizeInPixels { width: 63000, height: 64000 }
            )
        );
    }

    #[test]
    fn test_rect_points() {
        assert_eq!(
            Rect::new(10, 20, 100, 200),
            rect_points(PixelsXY { x: 10, y: 20 }, PixelsXY { x: 110, y: 220 })
        );
        assert_eq!(
            Rect::new(10, 20, 100, 200),
            rect_points(PixelsXY { x: 110, y: 20 }, PixelsXY { x: 10, y: 220 })
        );
        assert_eq!(
            Rect::new(10, 20, 100, 200),
            rect_points(PixelsXY { x: 10, y: 220 }, PixelsXY { x: 110, y: 20 })
        );
        assert_eq!(
            Rect::new(10, 20, 100, 200),
            rect_points(PixelsXY { x: 110, y: 220 }, PixelsXY { x: 10, y: 20 })
        );

        assert_eq!(
            Rect::new(-31000, -32000, 31005, 32010),
            rect_points(PixelsXY { x: 5, y: -32000 }, PixelsXY { x: -31000, y: 10 })
        );
        assert_eq!(
            Rect::new(10, 5, 30990, 31995),
            rect_points(PixelsXY { x: 31000, y: 5 }, PixelsXY { x: 10, y: 32000 })
        );

        assert_eq!(
            Rect::new(-31000, -32000, 62000, 64000),
            rect_points(PixelsXY { x: -31000, y: -32000 }, PixelsXY { x: 31000, y: 32000 })
        );
        assert_eq!(
            Rect::new(-31000, -32000, 62000, 64000),
            rect_points(PixelsXY { x: 31000, y: 32000 }, PixelsXY { x: -31000, y: -32000 })
        );
    }
}
