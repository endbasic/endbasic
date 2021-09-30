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

//! Configuration support for the graphical console.

use std::fs::File;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::str::FromStr;
use tempfile::TempDir;

/// Default resolution to use when none is provided.
const DEFAULT_RESOLUTION_PIXELS: (u32, u32) = (800, 600);

/// Default font to use when none is provided.
const DEFAULT_FONT_BYTES: &[u8] = include_bytes!("IBMPlexMono-Regular-6.0.0.ttf");

/// Default font size.
const DEFAULT_FONT_SIZE: u16 = 16;

/// Wrapper over `str::parse` to return `io::Result` with a custom `error` message.
fn parse_str<T: FromStr>(text: &str, error: &'static str) -> io::Result<T> {
    match text.parse::<T>() {
        Ok(value) => Ok(value),
        Err(_) => Err(io::Error::new(io::ErrorKind::InvalidInput, error)),
    }
}

/// Parses a graphical `resolution` of the form `WIDTHxHEIGHT`.
fn parse_resolution(resolution: &str) -> io::Result<(u32, u32)> {
    let resolution: Vec<&str> = resolution.split('x').collect();
    match resolution.as_slice() {
        [width, height] => {
            let width = parse_str(width, "Invalid width in resolution")?;
            let height = parse_str(height, "Invalid height in resolution")?;
            Ok((width, height))
        }
        _ => Err(io::Error::new(io::ErrorKind::InvalidInput, "Invalid resolution format")),
    }
}

/// Parses a graphical console specification.
pub fn parse_graphics_spec(params: &str) -> io::Result<(u32, u32, Option<&Path>, u16)> {
    let invalid_spec =
        Err(io::Error::new(io::ErrorKind::InvalidInput, "Invalid graphics console spec"));

    let mut params = params.split(',');
    let (width, height) = match params.next() {
        Some("") => DEFAULT_RESOLUTION_PIXELS,
        Some(resolution) => parse_resolution(resolution)?,
        None => return invalid_spec,
    };
    let font_path = match params.next() {
        Some("") => None,
        Some(font_path) => Some(Path::new(font_path)),
        None => None,
    };
    let font_size = match params.next() {
        Some("") => DEFAULT_FONT_SIZE,
        Some(font_size) => parse_str(font_size, "Invalid font size")?,
        None => DEFAULT_FONT_SIZE,
    };
    if params.next().is_some() {
        return invalid_spec;
    }

    Ok((width, height, font_path, font_size))
}

/// Context to maintain a font on disk temporarily.
pub struct TempFont {
    dir: TempDir,
}

impl TempFont {
    /// Gets an instance of the default font.
    pub fn default_font() -> io::Result<Self> {
        let dir = tempfile::tempdir()?;
        let mut file = File::create(dir.path().join("font.ttf"))?;
        file.write_all(DEFAULT_FONT_BYTES)?;
        Ok(Self { dir })
    }

    /// Gets the path to the temporary font.
    pub fn path(&self) -> PathBuf {
        self.dir.path().join("font.ttf")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_graphics_spec_empty() {
        for spec in ["", ",", ",,"] {
            let spec = parse_graphics_spec(spec).unwrap();
            assert_eq!(DEFAULT_RESOLUTION_PIXELS.0, spec.0);
            assert_eq!(DEFAULT_RESOLUTION_PIXELS.1, spec.1);
            assert_eq!(None, spec.2);
            assert_eq!(DEFAULT_FONT_SIZE, spec.3);
        }
    }

    #[test]
    fn test_parse_graphics_spec_only_resolution() {
        for spec in ["1024x768", "1024x768,", "1024x768,,"] {
            let spec = parse_graphics_spec(spec).unwrap();
            assert_eq!(1024, spec.0);
            assert_eq!(768, spec.1);
            assert_eq!(None, spec.2);
            assert_eq!(DEFAULT_FONT_SIZE, spec.3);
        }
    }

    #[test]
    fn test_parse_graphics_spec_only_font_path() {
        for spec in [",foo.ttf", ",foo.ttf,"] {
            let spec = parse_graphics_spec(spec).unwrap();
            assert_eq!(DEFAULT_RESOLUTION_PIXELS.0, spec.0);
            assert_eq!(DEFAULT_RESOLUTION_PIXELS.1, spec.1);
            assert_eq!(Some(Path::new("foo.ttf")), spec.2);
            assert_eq!(DEFAULT_FONT_SIZE, spec.3);
        }
    }

    #[test]
    fn test_parse_graphics_spec_only_font_size() {
        let spec = parse_graphics_spec(",,32").unwrap();
        assert_eq!(DEFAULT_RESOLUTION_PIXELS.0, spec.0);
        assert_eq!(DEFAULT_RESOLUTION_PIXELS.1, spec.1);
        assert_eq!(None, spec.2);
        assert_eq!(32, spec.3);
    }

    #[test]
    fn test_parse_graphics_spec_full() {
        let spec = parse_graphics_spec("1x2,/path/to/font.ttf,24").unwrap();
        assert_eq!(1, spec.0);
        assert_eq!(2, spec.1);
        assert_eq!(Some(Path::new("/path/to/font.ttf")), spec.2);
        assert_eq!(24, spec.3);
    }

    #[test]
    fn test_parse_graphics_spec_errors() {
        fn check(exp_error: &str, s: &str) {
            assert_eq!(exp_error, format!("{}", parse_graphics_spec(s).unwrap_err()));
        }
        check("Invalid graphics console spec", ",,,,");
        check("Invalid graphics console spec", "800x600,font.ttf,16,abc");
        check("Invalid resolution format", "a,font.ttf,16");
        check("Invalid width in resolution", "ax100,font.ttf,16");
        check("Invalid height in resolution", "100xa,font.ttf,16");
        check("Invalid font size", "100x200,font.ttf,a");
    }
}
