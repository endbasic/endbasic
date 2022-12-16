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

//! HTML canvas-based console implementation.
//!
//! TODO(jmmv): There is a lot of duplication between this module and the SDL console
//! implementation.  While the specifics to render are different, the logic to implement a
//! framebuffer-based console is the same -- so we should make it so to minimize bugs here
//! as we cannot easily test this implementation.

use crate::input::WebInput;
use crate::log_and_panic;
use async_trait::async_trait;
use endbasic_std::console::AnsiColor;
use endbasic_std::console::{
    ansi_color_to_rgb, remove_control_chars, CharsXY, ClearType, Console, Key, LineBuffer,
    PixelsXY, SizeInPixels, RGB,
};
use js_sys::Map;
use std::convert::TryFrom;
use std::f64::consts::PI;
use std::io;
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::CanvasRenderingContext2d;
use web_sys::HtmlCanvasElement;
use web_sys::ImageData;

/// Default foreground color, used at console creation time and when requesting the default color
/// via the `COLOR` command.
const DEFAULT_FG_COLOR: u8 = AnsiColor::White as u8;

/// Default background color, used at console creation time and when requesting the default color
/// via the `COLOR` command.
const DEFAULT_BG_COLOR: u8 = AnsiColor::Black as u8;

/// Default fonts to use.  The first font in the list should match whichever font is loaded in
/// `style.css`.  The rest are only provided as fallbacks.
const DEFAULT_FONT_FACE: &str = "\"IBM Plex Mono\", SFMono-Regular, Menlo, Monaco, Consolas, \
\"Liberation Mono\", \"Courier New\", monospace";

/// Size of the default font to use in pixels.
const DEFAULT_FONT_SIZE: u16 = 16;

/// Converts a `JsValue` error to an `io::Error`.
pub(crate) fn js_value_to_io_error(e: JsValue) -> io::Error {
    if let Some(str) = e.as_string() {
        return io::Error::new(io::ErrorKind::Other, str);
    }
    io::Error::new(io::ErrorKind::Other, "Unknown error")
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

impl ClampedMul<u16, u16> for u16 {
    fn clamped_mul(self, rhs: u16) -> u16 {
        match self.checked_mul(rhs) {
            Some(v) => v,
            None => u16::MAX,
        }
    }
}

impl ClampedMul<SizeInPixels, PixelsXY> for CharsXY {
    fn clamped_mul(self, rhs: SizeInPixels) -> PixelsXY {
        PixelsXY { x: self.x.clamped_mul(rhs.width), y: self.y.clamped_mul(rhs.height) }
    }
}

/// Returns the 2D rendering context for a given `canvas` element.
fn html_canvas_to_2d_context(canvas: HtmlCanvasElement) -> io::Result<CanvasRenderingContext2d> {
    let mut options = Map::new();
    options = options.set(&JsValue::from("alpha"), &JsValue::from(false));

    let context = match canvas
        .get_context_with_context_options("2d", &options)
        .map_err(js_value_to_io_error)?
    {
        Some(context) => context,
        None => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Failed to get 2D context from canvas",
            ))
        }
    };

    let context = match context.dyn_into::<CanvasRenderingContext2d>() {
        Ok(context) => context,
        Err(_) => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Returned 2D context for canvas does not have the correct type",
            ))
        }
    };

    Ok(context)
}

/// Implementation of a console that renders on an HTML canvas.
pub(crate) struct CanvasConsole {
    /// The HTML canvas context on which to render the console.
    context: CanvasRenderingContext2d,

    /// Keyboard input handler for the web.
    input: WebInput,

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
    cursor_backup: Option<ImageData>,

    /// Current foreground color as exposed via `color` and `set_color`.
    ansi_fg_color: Option<u8>,

    /// Current background color as exposed via `color` and `set_color`.
    ansi_bg_color: Option<u8>,

    /// Current foreground color.  Used for text and graphical rendering.
    fg_color: RGB,

    /// Current background color.  Used to clear text.
    bg_color: RGB,

    /// State of the console right before entering the "alternate" console.
    alt_backup: Option<(ImageData, CharsXY, RGB, RGB)>,

    /// Whether video syncing is enabled or not.
    sync_enabled: bool,
}

impl CanvasConsole {
    /// Creates a new canvas console backed by the `canvas` HTML element and that receives input
    /// events from `input`.
    pub(crate) fn new(canvas: HtmlCanvasElement, input: WebInput) -> io::Result<Self> {
        let size_pixels = {
            let width = match u16::try_from(canvas.width()) {
                Ok(v) => v,
                Err(_) => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("Canvas is too wide at {} pixels", canvas.width()),
                    ))
                }
            };
            let height = match u16::try_from(canvas.height()) {
                Ok(v) => v,
                Err(_) => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("Canvas is too tall at {} pixels", canvas.height()),
                    ))
                }
            };
            SizeInPixels { width, height }
        };

        let context = html_canvas_to_2d_context(canvas)?;
        context.set_font(&format!("{}px {}", DEFAULT_FONT_SIZE, DEFAULT_FONT_FACE));
        context.set_text_baseline("middle");

        let glyph_size = {
            let text_metrics = context.measure_text("X").map_err(js_value_to_io_error)?;
            let width = text_metrics.width().ceil() as u16;
            let height = DEFAULT_FONT_SIZE + 2; // Pad lines a little bit.
            SizeInPixels { width, height }
        };

        let size_chars = {
            let width = match size_pixels.width.checked_div(glyph_size.width) {
                Some(v) => v,
                None => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("Invalid glyph width {}", glyph_size.width),
                    ))
                }
            };
            let height = match size_pixels.height.checked_div(glyph_size.height) {
                Some(v) => v,
                None => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("Invalid glyph height {}", glyph_size.height),
                    ))
                }
            };
            CharsXY::new(width, height)
        };

        let mut console = Self {
            context,
            input,
            size_pixels,
            glyph_size,
            size_chars,
            cursor_pos: CharsXY::new(0, 0),
            cursor_visible: true,
            cursor_backup: None,
            ansi_fg_color: None,
            ansi_bg_color: None,
            fg_color: ansi_color_to_rgb(DEFAULT_FG_COLOR),
            bg_color: ansi_color_to_rgb(DEFAULT_BG_COLOR),
            alt_backup: None,
            sync_enabled: true,
        };
        console.clear(ClearType::All)?;
        Ok(console)
    }

    /// Returns the size of the console in pixels.
    pub(crate) fn size_pixels(&self) -> SizeInPixels {
        self.size_pixels
    }

    /// Sets the fill color of the canvas to `rgb`.
    fn set_fill_style_rgb(&mut self, rgb: RGB) {
        self.context
            .set_fill_style(&JsValue::from_str(&format!("rgb({}, {}, {})", rgb.0, rgb.1, rgb.2)));
    }

    /// Sets the fill color of the canvas to `rgb` with an `alpha` value.
    fn set_fill_style_rgba(&mut self, rgb: RGB, alpha: f64) {
        self.context.set_fill_style(&JsValue::from_str(&format!(
            "rgba({}, {}, {}, {})",
            rgb.0, rgb.1, rgb.2, alpha
        )));
    }

    /// Sets the stroke color of the canvas to `rgb`.
    fn set_stroke_style_rgb(&mut self, rgb: RGB) {
        self.context
            .set_stroke_style(&JsValue::from_str(&format!("rgb({}, {}, {})", rgb.0, rgb.1, rgb.2)));
    }

    /// Draws the cursor at the current position and saves the previous contents of the screen so
    /// that `clear_cursor` can restore them.
    fn draw_cursor(&mut self) -> io::Result<()> {
        if !self.cursor_visible || !self.sync_enabled {
            return Ok(());
        }

        let origin = self.cursor_pos.clamped_mul(self.glyph_size);

        assert!(self.cursor_backup.is_none());
        self.cursor_backup = Some(
            self.context
                .get_image_data(
                    f64::from(origin.x),
                    f64::from(origin.y),
                    f64::from(self.glyph_size.width),
                    f64::from(self.glyph_size.height),
                )
                .map_err(js_value_to_io_error)?,
        );

        self.set_fill_style_rgba(self.fg_color, 0.8);
        self.context.fill_rect(
            f64::from(origin.x),
            f64::from(origin.y),
            f64::from(self.glyph_size.width),
            f64::from(self.glyph_size.height),
        );
        Ok(())
    }

    /// Clears the cursor at the current position by restoring the contents of the screen saved by
    /// an earlier call to `draw_cursor`.
    fn clear_cursor(&mut self) -> io::Result<()> {
        if !self.cursor_visible || !self.sync_enabled || self.cursor_backup.is_none() {
            return Ok(());
        }

        let origin = self.cursor_pos.clamped_mul(self.glyph_size);
        self.context
            .put_image_data(
                self.cursor_backup.as_ref().unwrap(),
                f64::from(origin.x),
                f64::from(origin.y),
            )
            .map_err(js_value_to_io_error)?;
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

        let shifted = self
            .context
            .get_image_data(
                0.0,
                f64::from(self.glyph_size.height),
                f64::from(self.size_pixels.width),
                f64::from(self.size_pixels.height - self.glyph_size.height),
            )
            .map_err(js_value_to_io_error)?;
        self.context.put_image_data(&shifted, 0.0, 0.0).map_err(js_value_to_io_error)?;

        self.set_fill_style_rgb(self.bg_color);
        self.context.fill_rect(
            0.0,
            f64::from(self.size_pixels.height - self.glyph_size.height),
            f64::from(self.size_pixels.width),
            f64::from(self.glyph_size.height),
        );

        self.cursor_pos.x = 0;
        Ok(())
    }

    /// Renders the given text at the `start` position.
    ///
    /// Does not handle overflow nor scrolling.
    fn raw_write(&mut self, text: &str, start: PixelsXY) -> io::Result<()> {
        debug_assert!(!text.is_empty(), "It doesn't make sense to render an empty string");

        let len = match u16::try_from(text.chars().count()) {
            Ok(v) => v,
            Err(_) => return Err(io::Error::new(io::ErrorKind::InvalidInput, "Text too long")),
        };

        self.set_fill_style_rgb(self.bg_color);
        self.context.fill_rect(
            f64::from(start.x),
            f64::from(start.y),
            f64::from(ClampedMul::<u16, u16>::clamped_mul(len, self.glyph_size.width)),
            f64::from(self.glyph_size.height),
        );

        self.set_fill_style_rgb(self.fg_color);
        // We must render one character at a time because the glyph width of the original font is
        // not guaranteed to be an integer pixel size.
        let mut x = start.x;
        let advance = match i16::try_from(self.glyph_size.width) {
            Ok(width) => width,
            Err(e) => log_and_panic!("Glyph size is too big: {}", e),
        };
        let y_offset = match i16::try_from(self.glyph_size.height) {
            Ok(height) => height / 2,
            Err(e) => log_and_panic!("Glyph height is too big: {}", e),
        };
        for ch in text.chars() {
            let mut buf = [0u8; 4];
            let sb = ch.encode_utf8(&mut buf);

            self.context
                .fill_text(sb, f64::from(x), f64::from(start.y + y_offset))
                .map_err(js_value_to_io_error)?;

            x += advance;
        }

        Ok(())
    }

    /// Renders the given text at the current cursor position, with wrapping and
    /// scrolling if necessary.
    fn raw_write_wrapped(&mut self, text: String) -> io::Result<()> {
        let mut line_buffer = LineBuffer::from(text);

        loop {
            let fit_chars = self.size_chars.x - self.cursor_pos.x;

            let remaining = line_buffer.split_off(usize::from(fit_chars));
            let len = line_buffer.len();
            if len > 0 {
                self.raw_write(
                    &line_buffer.into_inner(),
                    self.cursor_pos.clamped_mul(self.glyph_size),
                )?;
                self.cursor_pos.x += match u16::try_from(len) {
                    Ok(len) => len,
                    Err(e) => {
                        log_and_panic!("Partial length was computed to fit on the screen: {}", e)
                    }
                };
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
impl Console for CanvasConsole {
    fn clear(&mut self, how: ClearType) -> io::Result<()> {
        self.set_fill_style_rgb(self.bg_color);
        match how {
            ClearType::All => {
                self.context.fill_rect(
                    0.0,
                    0.0,
                    f64::from(self.size_pixels.width),
                    f64::from(self.size_pixels.height),
                );
                self.cursor_pos.y = 0;
                self.cursor_pos.x = 0;

                // We intentionally do not draw the cursor here and wait until the first time we
                // write text to the console.  This allows the user to clear the screen and render
                // graphics if they want to without interference.
                self.cursor_backup = None;
            }
            ClearType::CurrentLine => {
                self.clear_cursor()?;
                self.context.fill_rect(
                    0.0,
                    f64::from(ClampedMul::<u16, u16>::clamped_mul(
                        self.cursor_pos.y,
                        self.glyph_size.height,
                    )),
                    f64::from(self.size_pixels.width),
                    f64::from(self.glyph_size.height),
                );
                self.cursor_pos.x = 0;
                self.draw_cursor()?;
            }
            ClearType::PreviousChar => {
                if self.cursor_pos.x > 0 {
                    self.clear_cursor()?;
                    let previous_pos = CharsXY::new(self.cursor_pos.x - 1, self.cursor_pos.y);
                    let origin = previous_pos.clamped_mul(self.glyph_size);
                    self.context.fill_rect(
                        f64::from(origin.x),
                        f64::from(origin.y),
                        f64::from(self.glyph_size.width),
                        f64::from(self.glyph_size.height),
                    );
                    self.cursor_pos = previous_pos;
                    self.draw_cursor()?;
                }
            }
            ClearType::UntilNewLine => {
                self.clear_cursor()?;
                let pos = self.cursor_pos.clamped_mul(self.glyph_size);
                debug_assert!(pos.x >= 0, "Inputs to pos are unsigned");
                debug_assert!(pos.y >= 0, "Inputs to pos are unsigned");
                let height = self.glyph_size.height;
                self.context.fill_rect(
                    f64::from(pos.x),
                    f64::from(pos.y),
                    f64::from(i32::from(self.size_pixels.width) - i32::from(pos.x)),
                    f64::from(height),
                );
                self.draw_cursor()?;
            }
        }
        Ok(())
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

        let pixels = self
            .context
            .get_image_data(
                0.0,
                0.0,
                f64::from(self.size_pixels.width),
                f64::from(self.size_pixels.height),
            )
            .map_err(js_value_to_io_error)?;
        self.alt_backup = Some((pixels, self.cursor_pos, self.fg_color, self.bg_color));

        self.clear(ClearType::All)
    }

    fn hide_cursor(&mut self) -> io::Result<()> {
        self.clear_cursor()?;
        self.cursor_visible = false;
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

        self.context.put_image_data(&pixels, 0.0, 0.0).map_err(js_value_to_io_error)?;

        self.cursor_pos = cursor_pos;
        self.fg_color = fg_color;
        self.bg_color = bg_color;
        self.draw_cursor()?;

        debug_assert!(self.alt_backup.is_none());
        Ok(())
    }

    fn locate(&mut self, pos: CharsXY) -> io::Result<()> {
        debug_assert!(pos.x < self.size_chars.x);
        debug_assert!(pos.y < self.size_chars.y);

        self.clear_cursor()?;
        self.cursor_pos = pos;
        self.draw_cursor()
    }

    fn move_within_line(&mut self, off: i16) -> io::Result<()> {
        self.clear_cursor()?;
        if off < 0 {
            self.cursor_pos.x -= -off as u16;
        } else {
            self.cursor_pos.x += off as u16;
        }
        self.draw_cursor()
    }

    fn print(&mut self, text: &str) -> io::Result<()> {
        let text = remove_control_chars(text);

        self.clear_cursor()?;
        self.raw_write_wrapped(text)?;
        self.open_line()?;
        self.draw_cursor()
    }

    async fn poll_key(&mut self) -> io::Result<Option<Key>> {
        self.input.try_recv().await
    }

    async fn read_key(&mut self) -> io::Result<Key> {
        self.input.recv().await
    }

    fn show_cursor(&mut self) -> io::Result<()> {
        if !self.cursor_visible {
            self.cursor_visible = true;
            if let Err(e) = self.draw_cursor() {
                self.cursor_visible = false;
                return Err(e);
            }
        }
        Ok(())
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
        self.draw_cursor()
    }

    fn draw_circle(&mut self, center: PixelsXY, radius: u16) -> io::Result<()> {
        self.set_stroke_style_rgb(self.fg_color);
        self.context.begin_path();
        self.context
            .arc(f64::from(center.x), f64::from(center.y), f64::from(radius), 0.0, 2.0 * PI)
            .map_err(js_value_to_io_error)?;
        self.context.stroke();
        Ok(())
    }

    fn draw_circle_filled(&mut self, center: PixelsXY, radius: u16) -> io::Result<()> {
        self.set_fill_style_rgb(self.fg_color);
        self.context.begin_path();
        self.context
            .arc(f64::from(center.x), f64::from(center.y), f64::from(radius), 0.0, 2.0 * PI)
            .map_err(js_value_to_io_error)?;
        self.context.fill();
        Ok(())
    }

    fn draw_line(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        self.context.begin_path();
        self.set_stroke_style_rgb(self.fg_color);
        self.context.move_to(f64::from(x1y1.x), f64::from(x1y1.y));
        self.context.line_to(f64::from(x2y2.x), f64::from(x2y2.y));
        self.context.stroke();
        Ok(())
    }

    fn draw_pixel(&mut self, xy: PixelsXY) -> io::Result<()> {
        self.set_fill_style_rgb(self.fg_color);
        self.context.fill_rect(f64::from(xy.x), f64::from(xy.y), 1.0, 1.0);
        Ok(())
    }

    fn draw_rect(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        self.set_stroke_style_rgb(self.fg_color);
        self.context.stroke_rect(
            f64::from(x1y1.x),
            f64::from(x1y1.y),
            f64::from(x2y2.x - x1y1.x),
            f64::from(x2y2.y - x1y1.y),
        );
        Ok(())
    }

    fn draw_rect_filled(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        self.set_fill_style_rgb(self.fg_color);
        self.context.fill_rect(
            f64::from(x1y1.x),
            f64::from(x1y1.y),
            f64::from(x2y2.x - x1y1.x),
            f64::from(x2y2.y - x1y1.y),
        );
        Ok(())
    }

    fn sync_now(&mut self) -> io::Result<()> {
        Ok(())
    }

    fn set_sync(&mut self, enabled: bool) -> io::Result<()> {
        self.sync_enabled = enabled;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
}
