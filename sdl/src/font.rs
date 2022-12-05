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

//! SDL font manipulation helpers.

use crate::string_error_to_io_error;
use endbasic_std::console::{CharsXY, SizeInPixels};
use once_cell::sync::Lazy;
use sdl2::ttf::{Font, FontError, InitError, Sdl2TtfContext};
use std::convert::TryFrom;
use std::io;
use std::path::Path;

/// Global instance of the SDL TTF font loader.  Trying to deal with the lifetime of the derived
/// fonts seems to be incredibly hard because of how we hide the `SdlConsole` implementation behind
/// the `Console` trait.  It might be possible to do this in a better way, but for now, keeping the
/// context global works well and is simple enough.
static TTF_CONTEXT: Lazy<Result<Sdl2TtfContext, InitError>> = Lazy::new(sdl2::ttf::init);

/// Converts an `InitError` to an `io::Error`.
fn init_error_to_io_error(e: &'static InitError) -> io::Error {
    match e {
        InitError::AlreadyInitializedError => {
            panic!("Initialization from once_cell should happen only once")
        }
        InitError::InitializationError(e) => io::Error::new(e.kind(), format!("{}", e)),
    }
}

/// Converts a `FontError` to an `io::Error`.
pub(crate) fn font_error_to_io_error(e: FontError) -> io::Error {
    let kind = match e {
        FontError::InvalidLatin1Text(_) => io::ErrorKind::InvalidInput,
        FontError::SdlError(_) => io::ErrorKind::Other,
    };
    io::Error::new(kind, e)
}

/// Wrapper around a monospaced SDL font.
pub(crate) struct MonospacedFont<'a> {
    pub(crate) font: Font<'a, 'static>,
    pub(crate) glyph_size: SizeInPixels,
}

impl<'a> MonospacedFont<'a> {
    /// Loads the font from the file `path` with `point_size`.  If the loaded font is not
    /// monospaced, returns an error.
    pub(crate) fn load(path: &Path, point_size: u16) -> io::Result<MonospacedFont<'a>> {
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

            let width = match u16::try_from(metrics.advance) {
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

            let height = match u16::try_from(font.height()) {
                Ok(0) => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "Invalid font height 0",
                    ))
                }
                Ok(height) => height,
                Err(e) => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("Invalid font height {}: {}", font.height(), e),
                    ))
                }
            };

            SizeInPixels { width, height }
        };

        Ok(MonospacedFont { font, glyph_size })
    }

    /// Computes the number of characters that fit within the given pixels `area`.
    pub(crate) fn chars_in_area(&self, area: SizeInPixels) -> CharsXY {
        debug_assert!(area.width > 0);
        debug_assert!(area.height > 0);
        CharsXY::new(
            area.width
                .checked_div(self.glyph_size.width)
                .expect("Glyph size tested for non-zero during init"),
            area.height
                .checked_div(self.glyph_size.height)
                .expect("Glyph size tested for non-zero during init"),
        )
    }
}
