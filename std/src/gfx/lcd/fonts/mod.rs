// EndBASIC
// Copyright 2025 Julio Merino
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

//! Support for bitmap fonts directly rendered onto an LCD.

use crate::console::{CharsXY, SizeInPixels};
use crate::gfx::lcd::LcdSize;
use std::collections::HashMap;
use std::io;

mod font_5x8;
pub use font_5x8::FONT_5X8;

mod font_16x16;
pub use font_16x16::FONT_16X16;

mod font_vga8x16;
pub use font_vga8x16::FONT_VGA8X16;

/// Representation of a font.
pub struct Font {
    /// The name of the font.
    pub name: &'static str,

    /// The size of a single glyph, in pixels.
    pub glyph_size: LcdSize,

    /// The number of bytes in every glyph row.
    pub stride: usize,

    /// The bitmap data for the font.
    pub data: &'static [u8],
}

impl Font {
    /// Returns the raw font data for `ch`.
    ///
    /// Each entry in the array corresponds to a row of pixels and is a bitmask indicating which
    /// pixels to turn on.
    pub(crate) fn glyph(&self, mut ch: char) -> &'static [u8] {
        if !(' '..='~').contains(&ch) {
            // TODO(jmmv): Would be nicer to draw an empty box, much like how unknown Unicode
            // characters are typically displayed.
            ch = '?';
        }
        let height = self.glyph_size.height * self.stride;
        let offset = ((ch as usize) - (' ' as usize)) * height;
        debug_assert!(offset < (self.data.len() + height));
        &self.data[offset..offset + height]
    }

    /// Computes the number of characters that fit within the given pixels `area`.
    pub fn chars_in_area(&self, area: SizeInPixels) -> CharsXY {
        CharsXY::new(
            area.width
                .checked_div(u16::try_from(self.glyph_size.width).expect("Must fit"))
                .expect("Glyph size tested for non-zero during init"),
            area.height
                .checked_div(u16::try_from(self.glyph_size.height).expect("Must fit"))
                .expect("Glyph size tested for non-zero during init"),
        )
    }
}

/// Registry of all available fonts.
pub struct Fonts(HashMap<&'static str, &'static Font>);

impl Fonts {
    /// Obtains a mapping of all available fonts.
    pub fn all() -> Self {
        let mut fonts = HashMap::default();
        fonts.insert(FONT_5X8.name, &FONT_5X8);
        fonts.insert(FONT_16X16.name, &FONT_16X16);
        fonts.insert(FONT_VGA8X16.name, &FONT_VGA8X16);
        Self(fonts)
    }

    /// Gets a font by `name`, ensuring that it's present.
    pub fn get(&self, name: &str) -> io::Result<&'static Font> {
        match self.0.get(name) {
            Some(font) => Ok(*font),
            None => {
                let mut valid = self.0.keys().copied().collect::<Vec<&'static str>>();
                valid.sort();
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("Unknown font: {}; valid names are: {}", name, valid.join(", ")),
                ))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
