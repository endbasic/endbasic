// EndBASIC
// Copyright 2024 Julio Merino
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

//! Support to implement graphical consoles.

use super::{
    ansi_color_to_rgb, remove_control_chars, AnsiColor, CharsXY, ClearType, Console, Key,
    LineBuffer, PixelsXY, SizeInPixels, RGB,
};
use async_trait::async_trait;
use std::convert::TryFrom;
use std::io;

/// Default foreground color, used at console creation time and when requesting the default color
/// via the `COLOR` command.
const DEFAULT_FG_COLOR: u8 = AnsiColor::White as u8;

/// Default background color, used at console creation time and when requesting the default color
/// via the `COLOR` command.
const DEFAULT_BG_COLOR: u8 = AnsiColor::Black as u8;

/// Conversion between types with silent value clamping.
pub trait ClampedInto<T> {
    /// Converts self into `T` capping values at `T`'s maximum or minimum boundaries.
    fn clamped_into(self) -> T;
}

impl ClampedInto<usize> for i16 {
    fn clamped_into(self) -> usize {
        if self < 0 {
            0
        } else {
            self as usize
        }
    }
}

impl ClampedInto<i16> for u16 {
    fn clamped_into(self) -> i16 {
        if self > u16::try_from(i16::MAX).unwrap() {
            i16::MAX
        } else {
            self as i16
        }
    }
}

impl ClampedInto<i16> for i32 {
    fn clamped_into(self) -> i16 {
        if self > i32::from(i16::MAX) {
            i16::MAX
        } else if self < i32::from(i16::MIN) {
            i16::MIN
        } else {
            self as i16
        }
    }
}

impl ClampedInto<u16> for i32 {
    fn clamped_into(self) -> u16 {
        if self > i32::from(u16::MAX) {
            u16::MAX
        } else if self < 0 {
            0
        } else {
            self as u16
        }
    }
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
pub trait ClampedMul<T, O> {
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

impl ClampedMul<u16, u16> for u16 {
    fn clamped_mul(self, rhs: u16) -> u16 {
        let product = u32::from(self) * u32::from(rhs);
        if product > u16::MAX as u32 {
            u16::MAX
        } else {
            product as u16
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

/// Given two points, calculates the origin and size of the rectangle they define.
fn rect_points(x1y1: PixelsXY, x2y2: PixelsXY) -> (PixelsXY, SizeInPixels) {
    let (x1, x2) = if x1y1.x < x2y2.x { (x1y1.x, x2y2.x) } else { (x2y2.x, x1y1.x) };
    let (y1, y2) = if x1y1.y < x2y2.y { (x1y1.y, x2y2.y) } else { (x2y2.y, x1y1.y) };

    let width = u32::try_from(i32::from(x2) - i32::from(x1))
        .expect("Width must have been non-negative")
        .clamped_into();
    let height = u32::try_from(i32::from(y2) - i32::from(y1))
        .expect("Height must have been non-negative")
        .clamped_into();

    (PixelsXY::new(x1, y1), SizeInPixels::new(width, height))
}

/// Container for configuration information of the backing surface.
pub struct RasterInfo {
    /// Size of the console in pixels.
    pub size_pixels: SizeInPixels,

    /// Size of each character.
    pub glyph_size: SizeInPixels,

    /// Size of the console in characters.  This is derived from `size_pixels` and `glyph_size`.
    pub size_chars: CharsXY,
}

/// Primitive graphical console raster operations.
pub trait RasterOps {
    /// Type of the image data (raw pixels).
    type ID;

    /// Queries information about the backend.
    fn get_info(&self) -> RasterInfo;

    /// Sets the drawing color for subsequent operations.
    fn set_draw_color(&mut self, color: RGB);

    /// Clears the whole console with the given color.
    fn clear(&mut self) -> io::Result<()>;

    /// Sets whether automatic presentation of the canvas is enabled or not.
    ///
    /// Raster backends might need this when the device they talk to is very slow and they want to
    /// buffer data in main memory first.
    ///
    /// Does *NOT* present the canvas.
    fn set_sync(&mut self, _enabled: bool) {}

    /// Displays any buffered changes to the console.
    ///
    /// Should ignore any sync values that the backend might have cached via `set_sync`.
    fn present_canvas(&mut self) -> io::Result<()>;

    /// Reads the raw pixel data for the rectangular region specified by `xy` and `size`.
    fn read_pixels(&mut self, xy: PixelsXY, size: SizeInPixels) -> io::Result<Self::ID>;

    /// Restores the rectangular region stored in `data` at the `xy` coordinates.
    fn put_pixels(&mut self, xy: PixelsXY, data: &Self::ID) -> io::Result<()>;

    /// Moves the rectangular region specified by `x1y1` and `size` to `x2y2`.  The original region
    /// is erased with the current drawing color.
    fn move_pixels(&mut self, x1y1: PixelsXY, x2y2: PixelsXY, size: SizeInPixels)
        -> io::Result<()>;

    /// Writes `text` starting at `xy` with the current drawing color.
    fn write_text(&mut self, xy: PixelsXY, text: &str) -> io::Result<()>;

    /// Draws the outline of a circle at `center` with `radius` using the current drawing color.
    fn draw_circle(&mut self, center: PixelsXY, radius: u16) -> io::Result<()>;

    /// Draws a filled circle at `center` with `radius` using the current drawing color.
    fn draw_circle_filled(&mut self, center: PixelsXY, radius: u16) -> io::Result<()>;

    /// Draws a line from `x1y1` to `x2y2` using the current drawing color.
    fn draw_line(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()>;

    /// Draws a single pixel at `xy` using the current drawing color.
    fn draw_pixel(&mut self, xy: PixelsXY) -> io::Result<()>;

    /// Draws the outline of a rectangle from `x1y1` to `x2y2` using the current drawing color.
    fn draw_rect(&mut self, xy: PixelsXY, size: SizeInPixels) -> io::Result<()>;

    /// Draws a filled rectangle from `x1y1` to `x2y2` using the current drawing color.
    fn draw_rect_filled(&mut self, xy: PixelsXY, size: SizeInPixels) -> io::Result<()>;
}

/// Primitive graphical console input operations.
#[async_trait(?Send)]
pub trait InputOps {
    /// Returns the next key press if any is available.
    async fn poll_key(&mut self) -> io::Result<Option<Key>>;

    /// Waits for and returns the next key press.
    async fn read_key(&mut self) -> io::Result<Key>;
}

/// Implementation of a console that renders to a backing surface.
pub struct GraphicsConsole<IO, RO>
where
    RO: RasterOps,
{
    input_ops: IO,

    /// Operations to render to the console.
    raster_ops: RO,

    /// Size of the console in pixels.
    size_pixels: SizeInPixels,

    /// Size of each character.
    glyph_size: SizeInPixels,

    /// Size of the console in characters.  This is derived from `size_pixels` and `glyph_size`.
    size_chars: CharsXY,

    /// Location of the cursor.
    cursor_pos: CharsXY,

    /// Whether the cursor is visible or not.
    cursor_visible: bool,

    /// Raw pixels at the cursor position before the cursor was drawn.  Used to restore the previous
    /// contents when the cursor moves.
    cursor_backup: Option<RO::ID>,

    /// Current foreground color as exposed via `color` and `set_color`.
    ansi_fg_color: Option<u8>,

    /// Current background color as exposed via `color` and `set_color`.
    ansi_bg_color: Option<u8>,

    /// Current foreground color.  Used for text and graphical rendering.
    fg_color: RGB,

    /// Current background color.  Used to clear text.
    bg_color: RGB,

    /// State of the console right before entering the "alternate" console.
    alt_backup: Option<(RO::ID, CharsXY, RGB, RGB)>,

    /// Whether video syncing is enabled or not.
    sync_enabled: bool,
}

impl<IO, RO> GraphicsConsole<IO, RO>
where
    IO: InputOps,
    RO: RasterOps,
{
    /// Initializes a new graphical console.
    pub fn new(input_ops: IO, raster_ops: RO) -> io::Result<Self> {
        let info = raster_ops.get_info();

        let mut console = Self {
            input_ops,
            raster_ops,
            size_pixels: info.size_pixels,
            glyph_size: info.glyph_size,
            size_chars: info.size_chars,
            cursor_pos: CharsXY::default(),
            cursor_visible: true,
            cursor_backup: None,
            ansi_bg_color: None,
            ansi_fg_color: None,
            bg_color: ansi_color_to_rgb(DEFAULT_BG_COLOR),
            fg_color: ansi_color_to_rgb(DEFAULT_FG_COLOR),
            alt_backup: None,
            sync_enabled: true,
        };

        console.set_color(console.ansi_fg_color, console.ansi_bg_color)?;
        console.clear(ClearType::All)?;

        Ok(console)
    }

    /// Renders any buffered changes to the backing surface.
    fn present_canvas(&mut self) -> io::Result<()> {
        if self.sync_enabled {
            self.raster_ops.present_canvas()
        } else {
            Ok(())
        }
    }

    /// Draws the cursor at the current position and saves the previous contents of the screen so
    /// that `clear_cursor` can restore them.
    ///
    /// Does not present the canvas.
    fn draw_cursor(&mut self) -> io::Result<()> {
        if !self.cursor_visible {
            return Ok(());
        }

        let x1y1 = self.cursor_pos.clamped_mul(self.glyph_size);

        assert!(self.cursor_backup.is_none());
        self.cursor_backup = Some(self.raster_ops.read_pixels(x1y1, self.glyph_size)?);

        // TODO(jmmv): It would be nice to draw the cursor with alpha blending so that the letters
        // under it are visible.  This was done before in the HTML canvas but was lost when I added
        // the GraphicsConsole abstraction.  Maybe all RGB colors should switch to RGBA.  Or maybe
        // we should special-case the cursor drawing.
        self.raster_ops.set_draw_color(self.fg_color);
        self.raster_ops.draw_rect_filled(x1y1, self.glyph_size)
    }

    /// Clears the cursor at the current position by restoring the contents of the screen saved by
    /// an earlier call to `draw_cursor`.
    ///
    /// Does not present the canvas.
    fn clear_cursor(&mut self) -> io::Result<()> {
        if !self.cursor_visible || self.cursor_backup.is_none() {
            return Ok(());
        }

        let x1y1 = self.cursor_pos.clamped_mul(self.glyph_size);

        self.raster_ops.put_pixels(x1y1, self.cursor_backup.as_ref().unwrap())?;
        self.cursor_backup = None;
        Ok(())
    }

    /// Moves the cursor to beginning of the next line, scrolling the console if necessary.
    ///
    /// Does not clear nor draw the cursor.
    fn open_line(&mut self) -> io::Result<()> {
        if self.cursor_pos.y < self.size_chars.y - 1 {
            self.cursor_pos.x = 0;
            self.cursor_pos.y += 1;
            return Ok(());
        }

        let x1y1 = PixelsXY::new(0, self.glyph_size.height.clamped_into());
        let x2y2 = PixelsXY::new(0, 0);
        let size = SizeInPixels::new(
            self.size_pixels.width,
            self.size_pixels.height - self.glyph_size.height,
        );

        self.raster_ops.set_draw_color(self.bg_color);
        self.raster_ops.move_pixels(x1y1, x2y2, size)?;

        self.cursor_pos.x = 0;
        Ok(())
    }

    /// Renders the given text at the current cursor position, with wrapping and
    /// scrolling if necessary.
    fn raw_write_wrapped(&mut self, text: String) -> io::Result<()> {
        let mut line_buffer = LineBuffer::from(text);

        loop {
            let fit_chars = self.size_chars.x - self.cursor_pos.x;

            let remaining = line_buffer.split_off(usize::from(fit_chars));
            let len = match u16::try_from(line_buffer.len()) {
                Ok(len) => len,
                Err(_) => return Err(io::Error::new(io::ErrorKind::InvalidInput, "Text too long")),
            };

            if len > 0 {
                let xy = self.cursor_pos.clamped_mul(self.glyph_size);
                let size = SizeInPixels::new(
                    len.clamped_mul(self.glyph_size.width),
                    self.glyph_size.height,
                );

                self.raster_ops.set_draw_color(self.bg_color);
                self.raster_ops.draw_rect_filled(xy, size)?;

                self.raster_ops.set_draw_color(self.fg_color);
                self.raster_ops.write_text(xy, &line_buffer.into_inner())?;
                self.cursor_pos.x += len;
            }

            line_buffer = remaining;
            if line_buffer.is_empty() {
                break;
            } else {
                self.open_line()?;
            }
        }

        Ok(())
    }
}

#[async_trait(?Send)]
impl<IO, RO> Console for GraphicsConsole<IO, RO>
where
    IO: InputOps,
    RO: RasterOps,
{
    fn clear(&mut self, how: ClearType) -> io::Result<()> {
        match how {
            ClearType::All => {
                self.raster_ops.set_draw_color(self.bg_color);
                self.raster_ops.clear()?;
                self.cursor_pos.y = 0;
                self.cursor_pos.x = 0;
                self.cursor_backup = None;
            }
            ClearType::CurrentLine => {
                self.clear_cursor()?;
                let xy = PixelsXY::new(0, self.cursor_pos.y.clamped_mul(self.glyph_size.height));
                let size = SizeInPixels::new(self.size_pixels.width, self.glyph_size.height);
                self.raster_ops.set_draw_color(self.bg_color);
                self.raster_ops.draw_rect_filled(xy, size)?;
                self.cursor_pos.x = 0;
            }
            ClearType::PreviousChar => {
                if self.cursor_pos.x > 0 {
                    self.clear_cursor()?;
                    let previous_pos = CharsXY::new(self.cursor_pos.x - 1, self.cursor_pos.y);
                    let origin = previous_pos.clamped_mul(self.glyph_size);
                    self.raster_ops.set_draw_color(self.bg_color);
                    self.raster_ops.draw_rect_filled(origin, self.glyph_size)?;
                    self.cursor_pos = previous_pos;
                }
            }
            ClearType::UntilNewLine => {
                self.clear_cursor()?;
                let pos = self.cursor_pos.clamped_mul(self.glyph_size);
                debug_assert!(pos.x >= 0, "Inputs to pos are unsigned");
                debug_assert!(pos.y >= 0, "Inputs to pos are unsigned");
                let size = SizeInPixels::new(
                    (i32::from(self.size_pixels.width) - i32::from(pos.x)).clamped_into(),
                    self.glyph_size.height,
                );
                self.raster_ops.set_draw_color(self.bg_color);
                self.raster_ops.draw_rect_filled(pos, size)?;
            }
        }
        self.draw_cursor()?;
        self.present_canvas()
    }

    fn color(&self) -> (Option<u8>, Option<u8>) {
        (self.ansi_fg_color, self.ansi_bg_color)
    }

    fn set_color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()> {
        self.ansi_fg_color = fg;
        self.fg_color = ansi_color_to_rgb(fg.unwrap_or(DEFAULT_FG_COLOR));
        self.ansi_bg_color = bg;
        self.bg_color = ansi_color_to_rgb(bg.unwrap_or(DEFAULT_BG_COLOR));
        Ok(())
    }

    fn enter_alt(&mut self) -> io::Result<()> {
        if self.alt_backup.is_some() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Cannot nest alternate screens",
            ));
        }

        let pixels = self.raster_ops.read_pixels(PixelsXY::new(0, 0), self.size_pixels)?;
        self.alt_backup = Some((pixels, self.cursor_pos, self.fg_color, self.bg_color));

        self.clear(ClearType::All)
    }

    fn hide_cursor(&mut self) -> io::Result<()> {
        self.clear_cursor()?;
        self.cursor_visible = false;
        self.present_canvas()
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

        self.raster_ops.put_pixels(PixelsXY::new(0, 0), &pixels)?;

        self.cursor_pos = cursor_pos;
        self.fg_color = fg_color;
        self.bg_color = bg_color;
        self.draw_cursor()?;
        self.present_canvas()?;

        debug_assert!(self.alt_backup.is_none());
        Ok(())
    }

    fn locate(&mut self, pos: CharsXY) -> io::Result<()> {
        debug_assert!(pos.x < self.size_chars.x);
        debug_assert!(pos.y < self.size_chars.y);

        self.clear_cursor()?;
        self.cursor_pos = pos;
        self.draw_cursor()?;
        self.present_canvas()
    }

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

    fn print(&mut self, text: &str) -> io::Result<()> {
        let text = remove_control_chars(text);

        self.clear_cursor()?;
        self.raw_write_wrapped(text)?;
        self.open_line()?;
        self.draw_cursor()?;
        self.present_canvas()
    }

    async fn poll_key(&mut self) -> io::Result<Option<Key>> {
        self.input_ops.poll_key().await
    }

    async fn read_key(&mut self) -> io::Result<Key> {
        self.input_ops.read_key().await
    }

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

    fn size_chars(&self) -> io::Result<CharsXY> {
        Ok(self.size_chars)
    }

    fn size_pixels(&self) -> io::Result<SizeInPixels> {
        Ok(self.size_pixels)
    }

    fn write(&mut self, text: &str) -> io::Result<()> {
        let text = remove_control_chars(text);

        self.clear_cursor()?;
        self.raw_write_wrapped(text)?;
        self.draw_cursor()?;
        self.present_canvas()
    }

    fn draw_circle(&mut self, center: PixelsXY, radius: u16) -> io::Result<()> {
        self.raster_ops.set_draw_color(self.fg_color);
        self.raster_ops.draw_circle(center, radius)?;
        self.present_canvas()
    }

    fn draw_circle_filled(&mut self, center: PixelsXY, radius: u16) -> io::Result<()> {
        self.raster_ops.set_draw_color(self.fg_color);
        self.raster_ops.draw_circle_filled(center, radius)?;
        self.present_canvas()
    }

    fn draw_line(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        self.raster_ops.set_draw_color(self.fg_color);
        self.raster_ops.draw_line(x1y1, x2y2)?;
        self.present_canvas()
    }

    fn draw_pixel(&mut self, xy: PixelsXY) -> io::Result<()> {
        self.raster_ops.set_draw_color(self.fg_color);
        self.raster_ops.draw_pixel(xy)?;
        self.present_canvas()
    }

    fn draw_rect(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        let (xy, size) = rect_points(x1y1, x2y2);
        self.raster_ops.set_draw_color(self.fg_color);
        self.raster_ops.draw_rect(xy, size)?;
        self.present_canvas()
    }

    fn draw_rect_filled(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        let (xy, size) = rect_points(x1y1, x2y2);
        self.raster_ops.set_draw_color(self.fg_color);
        self.raster_ops.draw_rect_filled(xy, size)?;
        self.present_canvas()
    }

    fn sync_now(&mut self) -> io::Result<()> {
        if self.sync_enabled {
            Ok(())
        } else {
            self.raster_ops.present_canvas()
        }
    }

    fn set_sync(&mut self, enabled: bool) -> io::Result<bool> {
        if !self.sync_enabled && enabled {
            self.raster_ops.present_canvas()?;
        }
        let previous = self.sync_enabled;
        self.sync_enabled = enabled;
        self.raster_ops.set_sync(enabled);
        Ok(previous)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clamped_into_u16_i16() {
        assert_eq!(0i16, 0u16.clamped_into());
        assert_eq!(10i16, 10u16.clamped_into());
        assert_eq!(i16::MAX - 1, u16::try_from(i16::MAX - 1).unwrap().clamped_into());
        assert_eq!(i16::MAX, u16::try_from(i16::MAX).unwrap().clamped_into());
        assert_eq!(i16::MAX, u16::MAX.clamped_into());
    }

    #[test]
    fn test_clamped_into_u16_i32() {
        assert_eq!(0i16, 0i32.clamped_into());
        assert_eq!(10i16, 10i32.clamped_into());
        assert_eq!(i16::MIN + 1, i32::from(i16::MIN + 1).clamped_into());
        assert_eq!(i16::MIN, i32::from(i16::MIN).clamped_into());
        assert_eq!(i16::MIN, i32::MIN.clamped_into());
        assert_eq!(i16::MAX - 1, i32::from(i16::MAX - 1).clamped_into());
        assert_eq!(i16::MAX, i32::from(i16::MAX).clamped_into());
        assert_eq!(i16::MAX, i32::MAX.clamped_into());
    }

    #[test]
    fn test_clamped_into_i32_u16() {
        assert_eq!(0u16, 0i32.clamped_into());
        assert_eq!(10u16, 10i32.clamped_into());
        assert_eq!(0u16, (-10i32).clamped_into());
        assert_eq!(u16::MAX - 1, i32::from(u16::MAX - 1).clamped_into());
        assert_eq!(u16::MAX, i32::from(u16::MAX).clamped_into());
        assert_eq!(u16::MAX, i32::MAX.clamped_into());
    }

    #[test]
    fn test_clamped_into_u32_u16() {
        assert_eq!(0u16, 0u32.clamped_into());
        assert_eq!(10u16, 10u32.clamped_into());
        assert_eq!(u16::MAX - 1, u32::from(u16::MAX - 1).clamped_into());
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
    fn test_clamped_mul_u16_u16_u16() {
        assert_eq!(0u16, ClampedMul::<u16, u16>::clamped_mul(0u16, 0u16));
        assert_eq!(55u16, ClampedMul::<u16, u16>::clamped_mul(11u16, 5u16));
        assert_eq!(u16::MAX, ClampedMul::<u16, u16>::clamped_mul(u16::MAX, u16::MAX));
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
    fn test_clamped_mul_charsxy_sizeinpixels_pixelsxy() {
        assert_eq!(
            PixelsXY { x: 0, y: 0 },
            CharsXY { x: 0, y: 0 }.clamped_mul(SizeInPixels::new(1, 1))
        );
        assert_eq!(
            PixelsXY { x: 50, y: 120 },
            CharsXY { x: 10, y: 20 }.clamped_mul(SizeInPixels::new(5, 6))
        );
        assert_eq!(
            PixelsXY { x: i16::MAX, y: 120 },
            CharsXY { x: 10, y: 20 }.clamped_mul(SizeInPixels::new(50000, 6))
        );
        assert_eq!(
            PixelsXY { x: 50, y: i16::MAX },
            CharsXY { x: 10, y: 20 }.clamped_mul(SizeInPixels::new(5, 60000))
        );
        assert_eq!(
            PixelsXY { x: i16::MAX, y: i16::MAX },
            CharsXY { x: 10, y: 20 }.clamped_mul(SizeInPixels::new(50000, 60000))
        );
    }

    #[test]
    fn test_rect_points() {
        assert_eq!(
            (PixelsXY { x: 10, y: 20 }, SizeInPixels::new(100, 200)),
            rect_points(PixelsXY { x: 10, y: 20 }, PixelsXY { x: 110, y: 220 })
        );
        assert_eq!(
            (PixelsXY { x: 10, y: 20 }, SizeInPixels::new(100, 200)),
            rect_points(PixelsXY { x: 110, y: 20 }, PixelsXY { x: 10, y: 220 })
        );
        assert_eq!(
            (PixelsXY { x: 10, y: 20 }, SizeInPixels::new(100, 200)),
            rect_points(PixelsXY { x: 10, y: 220 }, PixelsXY { x: 110, y: 20 })
        );
        assert_eq!(
            (PixelsXY { x: 10, y: 20 }, SizeInPixels::new(100, 200)),
            rect_points(PixelsXY { x: 110, y: 220 }, PixelsXY { x: 10, y: 20 })
        );

        assert_eq!(
            (PixelsXY { x: -31000, y: -32000 }, SizeInPixels::new(31005, 32010)),
            rect_points(PixelsXY { x: 5, y: -32000 }, PixelsXY { x: -31000, y: 10 })
        );
        assert_eq!(
            (PixelsXY { x: 10, y: 5 }, SizeInPixels::new(30990, 31995)),
            rect_points(PixelsXY { x: 31000, y: 5 }, PixelsXY { x: 10, y: 32000 })
        );

        assert_eq!(
            (PixelsXY { x: -31000, y: -32000 }, SizeInPixels::new(62000, 64000)),
            rect_points(PixelsXY { x: -31000, y: -32000 }, PixelsXY { x: 31000, y: 32000 })
        );
        assert_eq!(
            (PixelsXY { x: -31000, y: -32000 }, SizeInPixels::new(62000, 64000)),
            rect_points(PixelsXY { x: 31000, y: 32000 }, PixelsXY { x: -31000, y: -32000 })
        );
    }
}
