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

//! SDL2-based graphics terminal emulator.

use crate::console::{ansi_color_to_rgb, CharsXY, ClearType, Console, Key, PixelsXY};
use async_trait::async_trait;
use once_cell::sync::Lazy;
use sdl2::event::Event;
use sdl2::keyboard::{Keycode, Mod};
use sdl2::pixels::{Color, PixelFormatEnum};
use sdl2::rect::Rect;
use sdl2::render::{SurfaceCanvas, TextureCreator, TextureValueError, UpdateTextureError};
use sdl2::surface::{Surface, SurfaceContext};
use sdl2::ttf::{Font, FontError, InitError, Sdl2TtfContext};
use sdl2::video::{Window, WindowBuildError};
use sdl2::{EventPump, Sdl};
use std::cmp;
use std::convert::TryFrom;
use std::io;
use std::path::Path;

/// Default foreground color, used at console creation time and when requesting the default color
/// via the `COLOR` command.
const DEFAULT_FG_COLOR: Color = Color::WHITE;

/// Default background color, used at console creation time and when requesting the default color
/// via the `COLOR` command.
const DEFAULT_BG_COLOR: Color = Color::BLACK;

/// Global instance of the SDL TTF font loader.  Trying to deal with the lifetime of the derived
/// fonts seems to be incredibly hard because of how we hide the `SdlConsole` implementation behind
/// the `Console` trait.  It might be possible to do this in a better way, but for now, keeping the
/// context global works well and is simple enough.
static TTF_CONTEXT: Lazy<Result<Sdl2TtfContext, InitError>> = Lazy::new(sdl2::ttf::init);

/// Converts a `FontError` to an `io::Error`.
fn font_error_to_io_error(e: FontError) -> io::Error {
    let kind = match e {
        FontError::InvalidLatin1Text(_) => io::ErrorKind::InvalidInput,
        FontError::SdlError(_) => io::ErrorKind::Other,
    };
    io::Error::new(kind, e)
}

/// Converts an `InitError` to an `io::Error`.
fn init_error_to_io_error(e: &'static InitError) -> io::Error {
    match e {
        InitError::AlreadyInitializedError => {
            panic!("Initialization from once_cell should happen only once")
        }
        InitError::InitializationError(e) => io::Error::new(e.kind(), format!("{}", e)),
    }
}

/// Converts a flat string error message to an `io::Error`.
fn string_error_to_io_error(e: String) -> io::Error {
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

/// Wrapper around a monospaced SDL font.
struct MonospacedFont<'a> {
    font: Font<'a, 'static>,
    glyph_size: PixelsXY,
}

impl<'a> MonospacedFont<'a> {
    /// Loads the font from the file `path` with `point_size`.  If the loaded font is not
    /// monospaced, returns an error.
    fn load(path: &Path, point_size: u16) -> io::Result<MonospacedFont<'a>> {
        let ttf_context = TTF_CONTEXT.as_ref().map_err(init_error_to_io_error)?;

        let font = ttf_context.load_font(path, point_size).map_err(string_error_to_io_error)?;

        if !font.face_is_fixed_width() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("Font {} is not monospaced", path.display()),
            ));
        }

        let glyph_size = {
            let metrics = match font.find_glyph_metrics('A') {
                Some(metrics) => metrics,
                None => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Font lacks a glyph for 'A'; is it valid?",
                    ))
                }
            };

            let width = match usize::try_from(metrics.advance) {
                Ok(0) => {
                    return Err(io::Error::new(io::ErrorKind::InvalidInput, "Invalid font width 0"))
                }
                Ok(width) => width,
                Err(e) => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("Invalid font width {}: {}", metrics.advance, e),
                    ))
                }
            };

            let height = match usize::try_from(font.height()) {
                Ok(0) => {
                    return Err(io::Error::new(io::ErrorKind::InvalidInput, "Invalid font height"))
                }
                Ok(height) => height,
                Err(e) => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("Invalid font height 0: {}", e),
                    ))
                }
            };

            PixelsXY::new(width, height)
        };

        Ok(MonospacedFont { font, glyph_size })
    }

    /// Computes the number of characters that fit within the given pixels `area`.
    fn chars_in_area(&self, area: PixelsXY) -> CharsXY {
        debug_assert!(area.x > 0);
        debug_assert!(area.y > 0);
        CharsXY::new(area.x / self.glyph_size.x, area.y / self.glyph_size.y)
    }
}

/// Constructs an SDL `Rect` from `usize` values, making sure they are in range.
fn rect_usize(x1: usize, y1: usize, width: usize, height: usize) -> io::Result<Rect> {
    fn usize_to_i32(value: usize, name: &'static str) -> io::Result<i32> {
        match i32::try_from(value) {
            Ok(value) => Ok(value),
            Err(e) => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("Bad {} {}: {}", name, value, e),
                ))
            }
        }
    }

    fn usize_to_u32(value: usize, name: &'static str) -> io::Result<u32> {
        match u32::try_from(value) {
            Ok(value) => Ok(value),
            Err(e) => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("Bad {} {}: {}", name, value, e),
                ))
            }
        }
    }

    let x1 = usize_to_i32(x1, "x1 coordinate")?;
    let y1 = usize_to_i32(y1, "y1 coordinate")?;
    let width = usize_to_u32(width, "width")?;
    let height = usize_to_u32(height, "height")?;

    Ok(Rect::new(x1, y1, width, height))
}

/// Configures the resolution of the graphical console.
#[derive(Debug, PartialEq)]
pub enum Resolution {
    /// Tells the console to start in full screen mode at the current desktop resolution.
    FullScreenDesktop,

    /// Tells the console to start in full screen mode at the given resolution.
    FullScreen((u32, u32)),

    /// Tells the console to start in windowed mode at the given resolution.
    Windowed((u32, u32)),
}

impl Resolution {
    /// Creates a new instance of this enum of type `FullScreenDesktop`.
    pub fn full_screen_desktop() -> Self {
        Self::FullScreenDesktop
    }

    /// Ensures that the given resolution is valid to some extent.
    fn validate_width_and_height(width: u32, height: u32) -> io::Result<()> {
        if width == 0 {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "Console width cannot be 0"));
        }
        if height == 0 {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "Console height cannot be 0"));
        }
        Ok(())
    }

    /// Creates a new instance of this enum of type `FullScreen` after validating the parameters.
    pub fn full_screen(width: u32, height: u32) -> io::Result<Self> {
        Resolution::validate_width_and_height(width, height)?;
        Ok(Self::FullScreen((width, height)))
    }

    /// Creates a new instance of this enum of type `Windowed` after validating the parameters.
    pub fn windowed(width: u32, height: u32) -> io::Result<Self> {
        Resolution::validate_width_and_height(width, height)?;
        Ok(Self::Windowed((width, height)))
    }
}

/// Implementation of the EndBASIC console on top of an SDL2 window.
pub struct SdlConsole {
    /// SDL2 library context.  Must remain alive for the lifetime of the console: if it is dropped
    /// early, all further SDL operations fail.
    _context: Sdl,

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
    size_pixels: PixelsXY,

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
}

impl SdlConsole {
    /// Initializes a new SDL console.
    ///
    /// The console is sized to `resolution` pixels.  Also loads the desired font from
    /// `font_path` at `font_size` and uses it to calculate the size of the console in characters.
    ///
    /// There can only be one active `SdlConsole` at any given time given that this initializes and
    /// owns the SDL context.
    pub fn new(resolution: Resolution, font_path: &Path, font_size: u16) -> io::Result<Self> {
        let font = MonospacedFont::load(font_path, font_size)?;

        let context = sdl2::init().map_err(string_error_to_io_error)?;
        let event_pump = context.event_pump().map_err(string_error_to_io_error)?;
        let video = context.video().map_err(string_error_to_io_error)?;

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
            PixelsXY::new(
                usize::try_from(width).expect("Width must fit in usize"),
                usize::try_from(height).expect("Height must fit in usize"),
            )
        };
        let size_chars = font.chars_in_area(size_pixels);

        title += &format!(
            " - {}x{} pixels, {}x{} chars",
            size_pixels.x, size_pixels.y, size_chars.x, size_chars.y
        );
        window.set_title(&title).expect("There should have been no NULLs in the formatted title");

        let pixel_format = window.window_pixel_format();
        let surface = Surface::new(size_pixels.x as u32, size_pixels.y as u32, pixel_format)
            .map_err(string_error_to_io_error)?;
        let canvas = surface.into_canvas().map_err(string_error_to_io_error)?;
        let texture_creator = canvas.texture_creator();

        let mut console = Self {
            _context: context,
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
        };

        console.clear(ClearType::All)?;

        Ok(console)
    }

    /// Renders the current contents of `self.canvas` onto the output window.
    fn present_canvas(&mut self) -> io::Result<()> {
        let mut window_surface =
            self.window.surface(&self.event_pump).map_err(string_error_to_io_error)?;
        self.canvas
            .surface()
            .blit(None, &mut window_surface, None)
            .map_err(string_error_to_io_error)?;
        window_surface.finish().map_err(string_error_to_io_error)?;
        Ok(())
    }

    /// Draws the cursor at the current position and saves the previous contents of the screen so
    /// that `clear_cursor` can restore them.
    ///
    /// Does not present the canvas.
    fn draw_cursor(&mut self) -> io::Result<()> {
        if !self.cursor_visible {
            return Ok(());
        }

        let pos = self.cursor_pos * self.font.glyph_size;
        let width = self.font.glyph_size.x;
        let height = self.font.glyph_size.y;
        let rect = rect_usize(pos.x, pos.y, width, height)?;

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
        if !self.cursor_visible || self.cursor_backup.is_empty() {
            return Ok(());
        }

        let pos = self.cursor_pos * self.font.glyph_size;
        let width = self.font.glyph_size.x;
        let height = self.font.glyph_size.y;
        let rect = rect_usize(pos.x, pos.y, width, height)?;

        let mut texture = self
            .texture_creator
            .create_texture_static(
                None,
                u32::try_from(width).expect("Glyph width is too large"),
                u32::try_from(height).expect("Glyph height is too large"),
            )
            .map_err(texture_value_error_to_io_error)?;
        texture
            .update(None, &self.cursor_backup, width * self.pixel_format.byte_size_per_pixel())
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
                rect_usize(
                    0,
                    self.font.glyph_size.y,
                    self.size_pixels.x,
                    self.size_pixels.y - self.font.glyph_size.y,
                )?,
                &mut temp,
                None,
            )
            .map_err(string_error_to_io_error)?;
            temp
        };
        shifted
            .fill_rect(
                rect_usize(
                    0,
                    self.size_pixels.y - self.font.glyph_size.y,
                    self.size_pixels.x,
                    self.font.glyph_size.y,
                )?,
                self.bg_color,
            )
            .map_err(string_error_to_io_error)?;
        shifted.blit(None, self.canvas.surface_mut(), None).map_err(string_error_to_io_error)?;

        self.cursor_pos.x = 0;
        Ok(())
    }

    /// Renders the given `bytes` of text at the `start` position.
    ///
    /// Does not handle overflow nor scrolling, and also does not present the canvas.
    fn raw_write(&mut self, bytes: &[u8], start: PixelsXY) -> io::Result<()> {
        debug_assert!(!bytes.is_empty(), "SDL does not like empty strings");

        let surface = self
            .font
            .font
            .render_latin1(bytes)
            .shaded(self.fg_color, self.bg_color)
            .map_err(font_error_to_io_error)?;
        let texture = self
            .texture_creator
            .create_texture_from_surface(&surface)
            .map_err(texture_value_error_to_io_error)?;

        let rect = rect_usize(
            start.x,
            start.y,
            bytes.len() * self.font.glyph_size.x,
            self.font.glyph_size.y,
        )?;
        self.canvas.copy(&texture, None, rect).map_err(string_error_to_io_error)?;

        Ok(())
    }

    /// Renders the given `bytes` of text at the current cursor position, with wrapping and
    /// scrolling if necessary.
    ///
    /// Does not present the canvas.
    fn raw_write_wrapped(&mut self, mut bytes: &[u8]) -> io::Result<()> {
        debug_assert!(!bytes.is_empty(), "SDL does not like empty strings");

        loop {
            let fit_chars = self.size_chars.x - self.cursor_pos.x;
            let partial = &bytes[0..cmp::min(bytes.len(), fit_chars)];
            self.raw_write(partial, self.cursor_pos * self.font.glyph_size)?;

            bytes = &bytes[partial.len()..];
            if bytes.is_empty() {
                break;
            } else {
                self.open_line()?;
            }
        }

        Ok(())
    }
}

#[async_trait(?Send)]
impl Console for SdlConsole {
    fn clear(&mut self, how: ClearType) -> io::Result<()> {
        self.canvas.set_draw_color(self.bg_color);
        match how {
            ClearType::All => {
                self.canvas.clear();
                self.cursor_pos.y = 0;
                self.cursor_pos.x = 0;

                // We intentionally do not draw the cursor here and wait until the first time we write text
                // to the console.  This allows the user to clear the screen and render graphics if they
                // want to without interference.
                self.cursor_backup.clear();
            }
            ClearType::CurrentLine => {
                self.clear_cursor()?;
                let height = self.font.glyph_size.y;
                let y1 = self.cursor_pos.y * height;
                self.canvas
                    .fill_rect(rect_usize(0, y1, self.size_pixels.x, height)?)
                    .map_err(string_error_to_io_error)?;
                self.cursor_pos.x = 0;
                self.draw_cursor()?;
            }
            ClearType::PreviousChar => {
                if self.cursor_pos.x > 0 {
                    let pos = self.cursor_pos * self.font.glyph_size;
                    let width = self.font.glyph_size.x;
                    let height = self.font.glyph_size.y;
                    self.canvas
                        .fill_rect(rect_usize(pos.x, pos.y, width, height)?)
                        .map_err(string_error_to_io_error)?;
                    self.cursor_pos.x -= 1;
                }
            }
            ClearType::UntilNewLine => {
                self.clear_cursor()?;
                let pos = self.cursor_pos * self.font.glyph_size;
                let height = self.font.glyph_size.y;
                self.canvas
                    .fill_rect(rect_usize(pos.x, pos.y, self.size_pixels.x - pos.x, height)?)
                    .map_err(string_error_to_io_error)?;
                self.draw_cursor()?;
            }
        }

        self.present_canvas()?;
        Ok(())
    }

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

    fn hide_cursor(&mut self) -> io::Result<()> {
        self.clear_cursor()?;
        self.cursor_visible = false;
        self.present_canvas()?;
        Ok(())
    }

    fn is_interactive(&self) -> bool {
        true
    }

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
                .create_texture_static(None, self.size_pixels.x as u32, self.size_pixels.y as u32)
                .map_err(texture_value_error_to_io_error)?;
            texture
                .update(None, &pixels, self.size_pixels.x * self.pixel_format.byte_size_per_pixel())
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

    fn locate(&mut self, pos: CharsXY) -> io::Result<()> {
        self.clear_cursor()?;
        self.cursor_pos = pos;
        self.draw_cursor()?;
        self.present_canvas()?;
        Ok(())
    }

    fn move_within_line(&mut self, off: i16) -> io::Result<()> {
        self.clear_cursor()?;
        if off < 0 {
            self.cursor_pos.x -= usize::try_from(-off).expect("offset must have fit in usize");
        } else {
            self.cursor_pos.x += usize::try_from(off).expect("offset must have fit in usize");
        }
        self.draw_cursor()?;
        self.present_canvas()?;
        Ok(())
    }

    fn print(&mut self, text: &str) -> io::Result<()> {
        debug_assert!(!crate::console::has_control_chars_str(text));

        self.clear_cursor()?;
        if !text.is_empty() {
            self.raw_write_wrapped(text.as_bytes())?;
        }
        self.open_line()?;
        self.draw_cursor()?;
        self.present_canvas()?;
        Ok(())
    }

    async fn read_key(&mut self) -> io::Result<Key> {
        loop {
            let event = self.event_pump.wait_event();
            match event {
                Event::Quit { .. } => return Ok(Key::Eof),

                Event::KeyDown { keycode: Some(keycode), keymod, .. } => {
                    let key = match keycode {
                        Keycode::C if (keymod == Mod::LCTRLMOD || keymod == Mod::RCTRLMOD) => {
                            Key::Interrupt
                        }
                        Keycode::D if (keymod == Mod::LCTRLMOD || keymod == Mod::RCTRLMOD) => {
                            Key::Eof
                        }

                        Keycode::Backspace => Key::Backspace,
                        Keycode::Escape => Key::Escape,
                        Keycode::Return => Key::NewLine,

                        Keycode::Down => Key::ArrowDown,
                        Keycode::Left => Key::ArrowLeft,
                        Keycode::Right => Key::ArrowRight,
                        Keycode::Up => Key::ArrowUp,

                        _ => Key::Unknown(format!("code={}, mod={}", keycode, keymod)),
                    };
                    return Ok(key);
                }

                Event::TextInput { text, .. } => {
                    let mut chars = text.chars();
                    let first = chars
                        .next()
                        .unwrap_or_else(|| panic!("Cannot handle TextInput event: {:?}", text));
                    return Ok(Key::Char(first));
                }

                _ => (),
            }
        }
    }

    fn show_cursor(&mut self) -> io::Result<()> {
        self.cursor_visible = true;
        if let Err(e) = self.draw_cursor() {
            self.cursor_visible = false;
            return Err(e);
        }
        self.present_canvas()?;
        Ok(())
    }

    fn size(&self) -> io::Result<CharsXY> {
        Ok(self.size_chars)
    }

    fn write(&mut self, bytes: &[u8]) -> io::Result<()> {
        debug_assert!(!crate::console::has_control_chars_u8(bytes));

        if bytes.is_empty() {
            return Ok(());
        }

        self.clear_cursor()?;
        self.raw_write_wrapped(bytes)?;
        self.cursor_pos.x += bytes.len();
        self.draw_cursor()?;
        self.present_canvas()?;
        Ok(())
    }
}

#[cfg(test)]
mod testutils {
    use super::*;
    use flate2::read::GzDecoder;
    use flate2::write::GzEncoder;
    use flate2::Compression;
    use sdl2::rwops::RWops;
    use std::env;
    use std::fs::File;
    use std::io::{self, BufReader, Read};
    use std::path::PathBuf;
    use std::sync::{Mutex, MutexGuard};

    /// Set this to true to regenerate the golden images instead of verifying them.  The
    /// checked-in value should always be false (and if it is not, all tests fail).
    const REGEN_BMPS: bool = false;

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
        console: SdlConsole,

        /// Guard to ensure there is a single `SdlConsole` alive at any given time. This must come
        /// after `console` because the Rust drop rules dictate that struct elements are dropped in
        /// the order in which they are defined.
        _lock: MutexGuard<'static, ()>,
    }

    impl SdlTest {
        /// Creates a new test context and ensures no other test is running at the same time.
        pub(crate) fn new() -> Self {
            let lock = TEST_LOCK.lock().unwrap();
            let console = SdlConsole::new(
                Resolution::windowed(800, 600).unwrap(),
                &src_path("cli/src/IBMPlexMono-Regular-6.0.0.ttf"),
                16,
            )
            .unwrap();
            Self { _lock: lock, console }
        }

        /// Obtains access to the SDL console.
        pub(crate) fn console(&mut self) -> &mut SdlConsole {
            &mut self.console
        }

        /// Verifies that the current state of the console matches a golden imagine.  `bmp_basename`
        /// indicates the name of the BMP image to use, without an extension.
        pub(crate) fn verify(self, bmp_basename: &'static str) {
            let golden_bmp_gz = src_path("std/src").join(format!("{}.bmp.gz", bmp_basename));

            let surface = self.console.window.surface(&self.console.event_pump).unwrap();

            if REGEN_BMPS {
                let golden_bmp = src_path("std/src").join(format!("{}.bmp", bmp_basename));
                surface.save_bmp(&golden_bmp).unwrap();
                let mut input = BufReader::new(File::open(golden_bmp).unwrap());
                let output = File::create(golden_bmp_gz).unwrap();
                let mut encoder = GzEncoder::new(output, Compression::default());
                io::copy(&mut input, &mut encoder).unwrap();
                encoder.finish().unwrap();

                // We could delete the `golden_bmp` file here, but it's easier to keep it around
                // for manual validation of the new images.

                drop(self); // Avoid poisoning the mutex when panicking.
                panic!("Golden data regenerated; flip REGEN_BMPS back to false");
            }

            let input = BufReader::new(File::open(golden_bmp_gz).unwrap());
            let mut decoder = GzDecoder::new(input);
            let mut buffer = vec![];
            decoder.read_to_end(&mut buffer).unwrap();
            let mut rwops = RWops::from_bytes(buffer.as_slice()).unwrap();
            let golden = Surface::load_bmp_rw(&mut rwops)
                .unwrap()
                .into_canvas()
                .unwrap()
                .read_pixels(None, self.console.pixel_format)
                .unwrap();

            let mut actual =
                Surface::new(surface.width(), surface.height(), self.console.pixel_format).unwrap();
            surface.blit(None, &mut actual, None).unwrap();
            let actual =
                actual.into_canvas().unwrap().read_pixels(None, self.console.pixel_format).unwrap();

            // Compare images for equality.  In theory, they should be pixel-perfect across
            // platforms, but in practice, I'm encountering minor color variations (e.g. FreeBSD
            // renders colors that differ by one compared to Windows) that I haven't been able to
            // explain.  Cope with those here by tolerating minor differences in the comparison.
            let mut equal = true;
            assert_eq!(golden.len(), actual.len());
            for i in 0..golden.len() {
                let pixel1 = golden[i];
                let pixel2 = actual[i];

                let pixel2min = if pixel2 == 0 { pixel2 } else { pixel2 - 1 };
                let pixel2max = if pixel2 == 255 { pixel2 } else { pixel2 + 1 };

                if pixel1 < pixel2min || pixel1 > pixel2max {
                    eprintln!("Diff at pixel {}: {} vs. {}", i, pixel1, pixel2);
                    equal = false;
                }
            }
            assert!(equal, "Images do not match; see test output");

            // assert_eq!(golden, actual);
            // assert!(golden == actual, "Image contents don't match");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::testutils::*;
    use super::*;
    use futures_lite::future::block_on;

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_empty() {
        let test = SdlTest::new();
        test.verify("sdl-empty");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_colors() {
        let mut test = SdlTest::new();

        test.console().print("Default colors").unwrap();
        test.console().print("").unwrap();
        test.console().color(Some(14), Some(4)).unwrap();
        test.console().print("Cyan on blue").unwrap();
        test.console().color(None, Some(1)).unwrap();
        test.console().print("Default on red").unwrap();
        test.console().color(Some(11), None).unwrap();
        test.console().print("Yellow on default").unwrap();
        test.console().color(None, None).unwrap();
        test.console().print("").unwrap();
        test.console().print("Back to default colors").unwrap();

        test.verify("sdl-colors");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_scroll_and_wrap() {
        let mut test = SdlTest::new();

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
    fn test_clear() {
        let mut test = SdlTest::new();

        test.console().print("Before clearing the console").unwrap();
        test.console().color(None, Some(4)).unwrap();
        test.console().clear(ClearType::All).unwrap();
        test.console().print("After clearing the console in blue").unwrap();

        test.console().write(b"A line that will be erased").unwrap();
        test.console().clear(ClearType::CurrentLine).unwrap();

        test.console().write(b"A line with corrections1.").unwrap();
        test.console().clear(ClearType::PreviousChar).unwrap();
        test.console().clear(ClearType::PreviousChar).unwrap();
        test.console().print(&"!".to_owned()).unwrap();

        test.console().write(b"Remove part of this").unwrap();
        test.console().move_within_line(-8).unwrap();
        test.console().clear(ClearType::UntilNewLine).unwrap();
        test.console().write(b" -- done").unwrap();

        test.verify("sdl-clear");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_move_cursor() {
        let mut test = SdlTest::new();

        test.console().write(b"Move cursor over parts of this text").unwrap();
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
    fn test_hide_cursor() {
        let mut test = SdlTest::new();

        test.console().hide_cursor().unwrap();
        test.console().write(b"Cursor hidden").unwrap();

        test.verify("sdl-hide-cursor");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_enter_alt() {
        let mut test = SdlTest::new();

        test.console().print("Before entering the alternate console").unwrap();
        test.console().enter_alt().unwrap();
        test.console().print("After entering the alternate console").unwrap();

        test.verify("sdl-enter-alt");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_leave_alt() {
        let mut test = SdlTest::new();

        test.console().print("Before entering the alternate console").unwrap();
        test.console().enter_alt().unwrap();
        test.console().print("After entering the alternate console").unwrap();
        test.console().leave_alt().unwrap();

        test.verify("sdl-leave-alt");
    }

    #[test]
    #[ignore = "Requires a graphical environment"]
    fn test_read_key() {
        let mut test = SdlTest::new();

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

        let ev = test.console()._context.event().unwrap();

        ev.push_event(Event::Quit { timestamp: 0 }).unwrap();
        assert_eq!(Key::Eof, block_on(test.console().read_key()).unwrap());

        ev.push_event(key_down(Keycode::C, Mod::LCTRLMOD)).unwrap();
        assert_eq!(Key::Interrupt, block_on(test.console().read_key()).unwrap());
        ev.push_event(key_down(Keycode::C, Mod::RCTRLMOD)).unwrap();
        assert_eq!(Key::Interrupt, block_on(test.console().read_key()).unwrap());

        ev.push_event(key_down(Keycode::D, Mod::LCTRLMOD)).unwrap();
        assert_eq!(Key::Eof, block_on(test.console().read_key()).unwrap());
        ev.push_event(key_down(Keycode::D, Mod::RCTRLMOD)).unwrap();
        assert_eq!(Key::Eof, block_on(test.console().read_key()).unwrap());

        ev.push_event(key_down(Keycode::D, Mod::LALTMOD)).unwrap();
        match block_on(test.console().read_key()).unwrap() {
            Key::Unknown(_) => (),
            _ => panic!("Unknown key down event not detected as such"),
        };

        // TODO(jmmv): We aren't testing textual input because push_event doesn't support injecting
        // Event::TextInput events.

        test.verify("sdl-read-key");
    }
}
