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

use crate::WebYielder;
use async_trait::async_trait;
use endbasic_std::console::drawing::draw_text;
use endbasic_std::console::graphics::{RasterInfo, RasterOps};
use endbasic_std::console::{PixelsXY, RGB, SizeInPixels, rgb_to_ansi_color};
use endbasic_std::gfx::lcd::fonts::Font;
use std::convert::TryFrom;
use std::f64::consts::PI;
use std::io;
use wasm_bindgen::JsCast;
use wasm_bindgen::prelude::*;
use web_sys::HtmlCanvasElement;
use web_sys::ImageData;
use web_sys::{CanvasRenderingContext2d, ContextAttributes2d};

/// Converts a `JsValue` error to an `io::Error`.
pub(crate) fn js_value_to_io_error(e: JsValue) -> io::Error {
    if let Some(str) = e.as_string() {
        return io::Error::other(str);
    }
    io::Error::other("Unknown error")
}

/// Returns the 2D rendering context for a given `canvas` element.
fn html_canvas_to_2d_context(canvas: HtmlCanvasElement) -> io::Result<CanvasRenderingContext2d> {
    let attrs = ContextAttributes2d::new();

    // We don't use transparency for anything, so disable the alpha channel for performance reasons.
    attrs.set_alpha(false);

    // Chrome recommends setting this to true because we read from the canvas to move the cursor
    // and to scroll the console, but these operations needn't be fast.  It seems better to keep
    // this disabled to optimize for the rendering path of graphical applications.
    attrs.set_will_read_frequently(false);

    let context = match canvas
        .get_context_with_context_options("2d", &attrs)
        .map_err(js_value_to_io_error)?
    {
        Some(context) => context,
        None => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Failed to get 2D context from canvas",
            ));
        }
    };

    let context = match context.dyn_into::<CanvasRenderingContext2d>() {
        Ok(context) => context,
        Err(_) => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Returned 2D context for canvas does not have the correct type",
            ));
        }
    };

    Ok(context)
}

/// Implementation of a console that renders on an HTML canvas.
pub(crate) struct CanvasRasterOps {
    /// The HTML canvas context on which to render the console.
    context: CanvasRenderingContext2d,

    /// The font to use.
    font: &'static Font,

    /// The yielder with which to return control to the JavaScript runtime.
    yielder: WebYielder,

    /// Size of the console in pixels.
    size_pixels: SizeInPixels,

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
        font: &'static Font,
        yielder: WebYielder,
    ) -> io::Result<Self> {
        let size_pixels = {
            let width = match u16::try_from(canvas.width()) {
                Ok(v) => v,
                Err(_) => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("Canvas is too wide at {} pixels", canvas.width()),
                    ));
                }
            };
            let height = match u16::try_from(canvas.height()) {
                Ok(v) => v,
                Err(_) => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("Canvas is too tall at {} pixels", canvas.height()),
                    ));
                }
            };
            SizeInPixels::new(width, height)
        };

        let context = html_canvas_to_2d_context(canvas)?;
        context.set_image_smoothing_enabled(false);
        context.set_text_baseline("middle");

        // The actual values are irrelevant but need to be different than the initial values we use
        // below.
        let fill_color = (10, 10, 10);
        let stroke_color = (100, 100, 100);

        let mut raster_ops = Self { context, font, yielder, size_pixels, fill_color, stroke_color };

        raster_ops.set_fill_style_rgb((0, 0, 0));
        raster_ops.set_stroke_style_rgb((255, 255, 255));

        Ok(raster_ops)
    }

    /// Returns true if the point falls within the canvas bounds.
    fn contains_pixel(&self, xy: PixelsXY) -> bool {
        xy.x >= 0
            && xy.y >= 0
            && u16::try_from(xy.x).unwrap_or(u16::MAX) < self.size_pixels.width
            && u16::try_from(xy.y).unwrap_or(u16::MAX) < self.size_pixels.height
    }

    /// Sets the fill color of the canvas to `rgb`.
    fn set_fill_style_rgb(&mut self, rgb: RGB) {
        if self.fill_color != rgb {
            self.context.set_fill_style_str(&format!("rgb({}, {}, {})", rgb.0, rgb.1, rgb.2));
            self.fill_color = rgb;
        }
    }

    /// Sets the stroke color of the canvas to `rgb`.
    fn set_stroke_style_rgb(&mut self, rgb: RGB) {
        if self.stroke_color != rgb {
            self.context.set_stroke_style_str(&format!("rgb({}, {}, {})", rgb.0, rgb.1, rgb.2));
            self.stroke_color = rgb;
        }
    }

    /// Defines a canvas path for a polygon.
    fn poly_path(&self, points: &[PixelsXY]) {
        debug_assert!(points.len() > 2);
        self.context.begin_path();
        self.context.move_to(f64::from(points[0].x), f64::from(points[0].y));
        for point in &points[1..] {
            self.context.line_to(f64::from(point.x), f64::from(point.y));
        }
        self.context.close_path();
    }
}

#[async_trait(?Send)]
impl RasterOps for CanvasRasterOps {
    type ID = ImageData;

    fn get_info(&self) -> RasterInfo {
        RasterInfo {
            size_pixels: self.size_pixels,
            size_chars: self.font.chars_in_area(self.size_pixels),
            glyph_size: self.font.glyph_size.into(),
        }
    }

    fn set_draw_color(&mut self, color: RGB) {
        self.set_fill_style_rgb(color);
        self.set_stroke_style_rgb(color);
    }

    fn clear(&mut self) -> io::Result<()> {
        self.context.fill_rect(
            0.0,
            0.0,
            f64::from(self.size_pixels.width),
            f64::from(self.size_pixels.height),
        );
        Ok(())
    }

    fn present_canvas(&mut self) -> io::Result<()> {
        self.yielder.request_paint();
        Ok(())
    }

    fn peek_pixel(&self, xy: PixelsXY) -> io::Result<Option<u8>> {
        if !self.contains_pixel(xy) {
            return Ok(None);
        }

        let data = self
            .context
            .get_image_data(f64::from(xy.x), f64::from(xy.y), 1.0, 1.0)
            .map_err(js_value_to_io_error)?;
        let pixels = data.data();
        Ok(rgb_to_ansi_color((pixels[0], pixels[1], pixels[2])))
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
    ) -> io::Result<()> {
        // TODO(jmmv): This is much faster to do than reading and putting pixels... but means we
        // cannot use the "_size" parameter to move just a portion of the image.  This is fine
        // for now because this is only used for console scrolling... but highlights that this
        // generic interface may need tweaking.
        //
        // https://stackoverflow.com/questions/8376534/shift-canvas-contents-to-the-left
        debug_assert_eq!(
            SizeInPixels::new(
                self.size_pixels.width,
                self.size_pixels.height - u16::try_from(self.font.glyph_size.height).unwrap(),
            ),
            size
        );

        let saved = self.context.global_composite_operation().map_err(js_value_to_io_error)?;
        self.context.set_global_composite_operation("copy").map_err(js_value_to_io_error)?;

        self.context
            .draw_image_with_html_canvas_element(
                self.context.canvas().as_ref().expect("Canvas must be present in context"),
                f64::from(x2y2.x - x1y1.x),
                f64::from(x2y2.y - x1y1.y),
            )
            .map_err(js_value_to_io_error)?;

        self.context.set_global_composite_operation(&saved).map_err(js_value_to_io_error)
    }

    fn write_text(&mut self, xy: PixelsXY, text: &str) -> io::Result<()> {
        draw_text(self, self.font, xy, text)
    }

    fn draw_circle(&mut self, center: PixelsXY, radius: u16) -> io::Result<()> {
        self.context.begin_path();
        self.context
            .arc(f64::from(center.x), f64::from(center.y), f64::from(radius), 0.0, 2.0 * PI)
            .map_err(js_value_to_io_error)?;
        self.context.stroke();
        Ok(())
    }

    fn draw_circle_filled(&mut self, center: PixelsXY, radius: u16) -> io::Result<()> {
        self.context.begin_path();
        self.context
            .arc(f64::from(center.x), f64::from(center.y), f64::from(radius), 0.0, 2.0 * PI)
            .map_err(js_value_to_io_error)?;
        self.context.fill();
        Ok(())
    }

    fn draw_line(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        self.context.begin_path();
        self.context.move_to(f64::from(x1y1.x), f64::from(x1y1.y));
        self.context.line_to(f64::from(x2y2.x), f64::from(x2y2.y));
        self.context.stroke();
        Ok(())
    }

    fn draw_pixel(&mut self, xy: PixelsXY) -> io::Result<()> {
        self.context.fill_rect(f64::from(xy.x), f64::from(xy.y), 1.0, 1.0);
        Ok(())
    }

    fn draw_poly(&mut self, points: &[PixelsXY]) -> io::Result<()> {
        self.poly_path(points);
        self.context.stroke();
        Ok(())
    }

    fn draw_poly_filled(&mut self, points: &[PixelsXY]) -> io::Result<()> {
        self.poly_path(points);
        self.context.fill();
        self.context.stroke();
        Ok(())
    }

    fn draw_rect(&mut self, xy: PixelsXY, size: SizeInPixels) -> io::Result<()> {
        self.context.stroke_rect(
            f64::from(xy.x),
            f64::from(xy.y),
            f64::from(size.width),
            f64::from(size.height),
        );
        Ok(())
    }

    fn draw_rect_filled(&mut self, xy: PixelsXY, size: SizeInPixels) -> io::Result<()> {
        self.context.fill_rect(
            f64::from(xy.x),
            f64::from(xy.y),
            f64::from(size.width),
            f64::from(size.height),
        );
        Ok(())
    }

    fn draw_tri(&mut self, x1y1: PixelsXY, x2y2: PixelsXY, x3y3: PixelsXY) -> io::Result<()> {
        self.context.begin_path();
        self.context.move_to(f64::from(x1y1.x), f64::from(x1y1.y));
        self.context.line_to(f64::from(x2y2.x), f64::from(x2y2.y));
        self.context.line_to(f64::from(x3y3.x), f64::from(x3y3.y));
        self.context.close_path();
        self.context.stroke();
        Ok(())
    }

    fn draw_tri_filled(
        &mut self,
        x1y1: PixelsXY,
        x2y2: PixelsXY,
        x3y3: PixelsXY,
    ) -> io::Result<()> {
        self.context.begin_path();
        self.context.move_to(f64::from(x1y1.x), f64::from(x1y1.y));
        self.context.line_to(f64::from(x2y2.x), f64::from(x2y2.y));
        self.context.line_to(f64::from(x3y3.x), f64::from(x3y3.y));
        self.context.close_path();
        self.context.fill();
        Ok(())
    }
}
