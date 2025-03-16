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

//! Generic types to represent and manipulate LCDs.

use crate::console::{SizeInPixels, RGB};
use std::convert::TryFrom;
use std::io;

mod buffered;
mod font8;

pub use buffered::BufferedLcd;
pub use font8::FONT_5X8;

/// Trait to convert a pixel to a sequence of bytes.
pub trait AsByteSlice {
    /// Returns the byte representation of a pixel.
    fn as_slice(&self) -> &[u8];
}

/// Data for one pixel encoded as RGB565.
#[derive(Clone, Copy)]
pub struct RGB565Pixel(pub [u8; 2]);

impl AsByteSlice for RGB565Pixel {
    fn as_slice(&self) -> &[u8] {
        &self.0
    }
}

/// Representation of a font.
pub struct Font {
    /// The size of a single glyph, in pixels.
    pub glyph_size: LcdSize,

    /// The bitmap data for the font.
    pub data: &'static [u8],
}

impl Font {
    /// Returns the raw font data for `ch`.
    ///
    /// Each entry in the array corresponds to a row of pixels and is a bitmask indicating which
    /// pixels to turn on.
    fn glyph(&self, mut ch: char) -> &'static [u8] {
        if !(' '..='~').contains(&ch) {
            // TODO(jmmv): Would be nicer to draw an empty box, much like how unknown Unicode
            // characters are typically displayed.
            ch = '?';
        }
        let height = self.glyph_size.height;
        let offset = ((ch as usize) - (' ' as usize)) * height;
        debug_assert!(offset < (self.data.len() + height));
        &self.data[offset..offset + height]
    }
}

/// Primitives that an LCD must define.
pub trait Lcd {
    /// The primitive type of the pixel data.
    type Pixel: AsByteSlice + Copy;

    /// Returns the dimensions of the LCD and size of the `Pixel` (stride).
    fn info(&self) -> (LcdSize, usize);

    /// Encodes an `rgb` color into the `Pixel` expected by the LCD.
    fn encode(&self, rgb: RGB) -> Self::Pixel;

    /// Fills the area expressed by `x1y1` to `x2y2` by the pixel `data`.  The length of `data`
    /// should be the size of the window in pixels multiplied by the `Pixel` size.
    fn set_data(&mut self, x1y1: LcdXY, x2y2: LcdXY, data: &[u8]) -> io::Result<()>;
}

/// Represents valid coordinates within the LCD space.
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct LcdXY {
    /// The X coordinate.
    pub x: usize,

    /// The Y coordinate.
    pub y: usize,
}

/// Represents a size that fits in the LCD space.
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct LcdSize {
    /// The width.
    pub width: usize,

    /// The height.
    pub height: usize,
}

impl LcdSize {
    /// Calculates the size of the window represented by `x1y1` and `x2y2`.
    fn between(x1y1: LcdXY, x2y2: LcdXY) -> Self {
        debug_assert!(x2y2.x >= x1y1.x);
        debug_assert!(x2y2.y >= x1y1.y);
        Self { width: x2y2.x - x1y1.x + 1, height: x2y2.y - x1y1.y + 1 }
    }

    /// Creates a new buffer with enough capacity to hold the content of this LCD size for the given
    /// `stride``.  The returned buffer is of zero size.
    fn new_buffer(&self, stride: usize) -> Vec<u8> {
        Vec::with_capacity(self.width * self.height * stride)
    }
}

impl From<LcdSize> for SizeInPixels {
    fn from(value: LcdSize) -> Self {
        Self::new(
            u16::try_from(value.width).expect("Must fit"),
            u16::try_from(value.height).expect("Must fit"),
        )
    }
}

/// Converts a pair of coordinates to a top-left origin coordinate plus a size.
pub fn to_xy_size(x1y1: LcdXY, x2y2: LcdXY) -> (LcdXY, LcdSize) {
    let x1 = std::cmp::min(x1y1.x, x2y2.x);
    let y1 = std::cmp::min(x1y1.y, x2y2.y);

    let x2 = std::cmp::max(x1y1.x, x2y2.x);
    let y2 = std::cmp::max(x1y1.y, x2y2.y);

    (LcdXY { x: x1, y: y1 }, LcdSize { width: x2 + 1 - x1, height: y2 + 1 - y1 })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Syntactic sugar to instantiate a coordinate in the LCD space.
    fn xy(x: usize, y: usize) -> LcdXY {
        LcdXY { x, y }
    }

    /// Syntactic sugar to instantiate a size in the LCD space.
    fn size(width: usize, height: usize) -> LcdSize {
        LcdSize { width, height }
    }

    #[test]
    fn test_lcdsize_between_one_pixel() {
        assert_eq!(size(1, 1), LcdSize::between(xy(15, 16), xy(15, 16)));
    }

    #[test]
    fn test_lcdsize_between_rect() {
        assert_eq!(size(4, 5), LcdSize::between(xy(10, 25), xy(13, 29)));
    }

    #[test]
    fn test_lcdsize_new_buffer() {
        let buffer = size(10, 20).new_buffer(3);
        assert_eq!(10 * 20 * 3, buffer.capacity());
    }

    #[test]
    fn test_to_xy_size_one_pixel() {
        assert_eq!(
            (LcdXY { x: 10, y: 20 }, LcdSize { width: 1, height: 1 }),
            to_xy_size(xy(10, 20), xy(10, 20))
        );
    }

    #[test]
    fn test_to_xy_size_rect() {
        assert_eq!(
            (LcdXY { x: 10, y: 20 }, LcdSize { width: 5, height: 7 }),
            to_xy_size(xy(10, 20), xy(14, 26))
        );
    }

    #[test]
    fn test_font_glyph_printable() {
        let font = &FONT_5X8;

        let offset = (usize::from(b'a') - usize::from(b' ')) * 8;
        let expected = &font.data[offset..offset + 8];

        let data = font.glyph('a');
        assert_eq!(expected, data);
    }

    #[test]
    fn test_font_glyph_non_printable() {
        let font = &FONT_5X8;

        let offset = (usize::from(b'?') - usize::from(b' ')) * 8;
        let expected = &font.data[offset..offset + 8];

        let data = font.glyph(char::from(30));
        assert_eq!(expected, data);
    }
}
