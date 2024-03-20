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

use crate::{log_and_panic, Yielder};
use async_trait::async_trait;
use endbasic_std::console::graphics::{RasterInfo, RasterOps};
use endbasic_std::console::{CharsXY, PixelsXY, SizeInPixels, RGB};
use std::cell::RefCell;
use std::convert::TryFrom;
use std::f64::consts::PI;
use std::io;
use std::rc::Rc;
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::HtmlCanvasElement;
use web_sys::ImageData;
use web_sys::{CanvasRenderingContext2d, ContextAttributes2d};

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
    let mut attrs = ContextAttributes2d::new();

    // We don't use transparency for anything, so disable the alpha channel for performance reasons.
    attrs.alpha(false);

    // Chrome recommends setting this to true because we read from the canvas to move the cursor
    // and to scroll the console, but these operations needn't be fast.  It seems better to keep
    // this disabled to optimize for the rendering path of graphical applications.
    attrs.will_read_frequently(false);

    let context = match canvas
        .get_context_with_context_options("2d", &attrs)
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
pub(crate) struct CanvasRasterOps {
    /// The HTML canvas context on which to render the console.
    context: CanvasRenderingContext2d,

    yielder: Rc<RefCell<Yielder>>,

    /// Size of the console in pixels.
    size_pixels: SizeInPixels,

    /// Size of each character.
    glyph_size: SizeInPixels,

    /// Size of the console in characters.  This is derived from `size_pixels` and `glyph_size`.
    size_chars: CharsXY,

    /// Current fill color.  Used only to track if we need to update the canvas.
    fill_color: RGB,

    /// Current stroke color.  Used only to track if we need to update the canvas.
    stroke_color: RGB,
}

impl CanvasRasterOps {
    /// Creates a new canvas console backed by the `canvas` HTML element and that receives input
    /// events from `input`.
    pub(crate) fn new(
        canvas: HtmlCanvasElement,
        yielder: Rc<RefCell<Yielder>>,
    ) -> io::Result<Self> {
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
            SizeInPixels::new(width, height)
        };

        let context = html_canvas_to_2d_context(canvas)?;
        context.set_font(&format!("{}px {}", DEFAULT_FONT_SIZE, DEFAULT_FONT_FACE));
        context.set_text_baseline("middle");

        let glyph_size = {
            let text_metrics = context.measure_text("X").map_err(js_value_to_io_error)?;
            let width = text_metrics.width().ceil() as u16;
            let height = DEFAULT_FONT_SIZE + 2; // Pad lines a little bit.
            SizeInPixels::new(width, height)
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

        // The actual values are irrelevant but need to be different than the initial values we use
        // below.
        let fill_color = (10, 10, 10);
        let stroke_color = (100, 100, 100);

        let mut raster_ops = Self {
            context,
            yielder,
            size_pixels,
            glyph_size,
            size_chars,
            fill_color,
            stroke_color,
        };

        raster_ops.set_fill_style_rgb((0, 0, 0));
        raster_ops.set_stroke_style_rgb((255, 255, 255));

        Ok(raster_ops)
    }

    /// Sets the fill color of the canvas to `rgb`.
    fn set_fill_style_rgb(&mut self, rgb: RGB) {
        if self.fill_color != rgb {
            self.context.set_fill_style(&JsValue::from_str(&format!(
                "rgb({}, {}, {})",
                rgb.0, rgb.1, rgb.2
            )));
            self.fill_color = rgb;
        }
    }

    /// Sets the stroke color of the canvas to `rgb`.
    fn set_stroke_style_rgb(&mut self, rgb: RGB) {
        if self.stroke_color != rgb {
            self.context.set_stroke_style(&JsValue::from_str(&format!(
                "rgb({}, {}, {})",
                rgb.0, rgb.1, rgb.2
            )));
            self.stroke_color = rgb;
        }
    }
}

#[async_trait(?Send)]
impl RasterOps for CanvasRasterOps {
    type ID = ImageData;

    fn get_info(&self) -> RasterInfo {
        RasterInfo {
            size_pixels: self.size_pixels,
            glyph_size: self.glyph_size,
            size_chars: self.size_chars,
        }
    }

    fn clear(&mut self, color: RGB) -> io::Result<()> {
        self.set_fill_style_rgb(color);
        self.context.fill_rect(
            0.0,
            0.0,
            f64::from(self.size_pixels.width),
            f64::from(self.size_pixels.height),
        );
        Ok(())
    }

    fn present_canvas(&mut self) -> io::Result<()> {
        self.yielder.borrow_mut().schedule();
        Ok(())
    }

    fn read_pixels(&mut self, xy: PixelsXY, size: SizeInPixels) -> io::Result<ImageData> {
        self.context
            .get_image_data(
                f64::from(xy.x),
                f64::from(xy.y),
                f64::from(size.width),
                f64::from(size.height),
            )
            .map_err(js_value_to_io_error)
    }

    fn put_pixels(&mut self, xy: PixelsXY, data: &ImageData) -> io::Result<()> {
        self.context
            .put_image_data(data, f64::from(xy.x), f64::from(xy.y))
            .map_err(js_value_to_io_error)
    }

    fn move_pixels(
        &mut self,
        x1y1: PixelsXY,
        x2y2: PixelsXY,
        size: SizeInPixels,
        color: RGB,
    ) -> io::Result<()> {
        let shifted = self
            .context
            .get_image_data(
                f64::from(x1y1.x),
                f64::from(x1y1.y),
                f64::from(size.width),
                f64::from(size.height),
            )
            .map_err(js_value_to_io_error)?;
        self.set_fill_style_rgb(color);
        self.context.fill_rect(
            f64::from(x1y1.x),
            f64::from(x1y1.y),
            f64::from(size.width),
            f64::from(size.height),
        );
        self.context
            .put_image_data(&shifted, f64::from(x2y2.x), f64::from(x2y2.y))
            .map_err(js_value_to_io_error)
    }

    fn write_text(
        &mut self,
        xy: PixelsXY,
        text: &str,
        fg_color: RGB,
        bg_color: RGB,
    ) -> io::Result<()> {
        debug_assert!(!text.is_empty(), "It doesn't make sense to render an empty string");

        let len = match u16::try_from(text.chars().count()) {
            Ok(v) => v,
            Err(_) => return Err(io::Error::new(io::ErrorKind::InvalidInput, "Text too long")),
        };

        self.set_fill_style_rgb(bg_color);
        self.context.fill_rect(
            f64::from(xy.x),
            f64::from(xy.y),
            f64::from(ClampedMul::<u16, u16>::clamped_mul(len, self.glyph_size.width)),
            f64::from(self.glyph_size.height),
        );

        self.set_fill_style_rgb(fg_color);
        // We must render one character at a time because the glyph width of the original font is
        // not guaranteed to be an integer pixel size.
        let mut x = xy.x;
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
                .fill_text(sb, f64::from(x), f64::from(xy.y + y_offset))
                .map_err(js_value_to_io_error)?;

            x += advance;
        }

        Ok(())
    }

    fn draw_circle(&mut self, center: PixelsXY, radius: u16, color: RGB) -> io::Result<()> {
        self.set_stroke_style_rgb(color);
        self.context.begin_path();
        self.context
            .arc(f64::from(center.x), f64::from(center.y), f64::from(radius), 0.0, 2.0 * PI)
            .map_err(js_value_to_io_error)?;
        self.context.stroke();
        Ok(())
    }

    fn draw_circle_filled(&mut self, center: PixelsXY, radius: u16, color: RGB) -> io::Result<()> {
        self.set_fill_style_rgb(color);
        self.context.begin_path();
        self.context
            .arc(f64::from(center.x), f64::from(center.y), f64::from(radius), 0.0, 2.0 * PI)
            .map_err(js_value_to_io_error)?;
        self.context.fill();
        Ok(())
    }

    fn draw_line(&mut self, x1y1: PixelsXY, x2y2: PixelsXY, color: RGB) -> io::Result<()> {
        self.context.begin_path();
        self.set_stroke_style_rgb(color);
        self.context.move_to(f64::from(x1y1.x), f64::from(x1y1.y));
        self.context.line_to(f64::from(x2y2.x), f64::from(x2y2.y));
        self.context.stroke();
        Ok(())
    }

    fn draw_pixel(&mut self, xy: PixelsXY, color: RGB) -> io::Result<()> {
        self.set_fill_style_rgb(color);
        self.context.fill_rect(f64::from(xy.x), f64::from(xy.y), 1.0, 1.0);
        Ok(())
    }

    fn draw_rect(&mut self, xy: PixelsXY, size: SizeInPixels, color: RGB) -> io::Result<()> {
        self.set_stroke_style_rgb(color);
        self.context.stroke_rect(
            f64::from(xy.x),
            f64::from(xy.y),
            f64::from(size.width),
            f64::from(size.height),
        );
        Ok(())
    }

    fn draw_rect_filled(&mut self, xy: PixelsXY, size: SizeInPixels, color: RGB) -> io::Result<()> {
        self.set_fill_style_rgb(color);
        self.context.fill_rect(
            f64::from(xy.x),
            f64::from(xy.y),
            f64::from(size.width),
            f64::from(size.height),
        );
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
