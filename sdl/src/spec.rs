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

use crate::console::Resolution;
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

/// Returns the default resolution for the console.
fn default_resolution() -> Resolution {
    Resolution::windowed(DEFAULT_RESOLUTION_PIXELS.0, DEFAULT_RESOLUTION_PIXELS.1)
        .expect("Hardcoded default resolution must have been valid")
}

/// Wrapper over `str::parse` to return `io::Result` with a custom `error` message.
fn parse_str<T: FromStr>(text: &str, error: &'static str) -> io::Result<T> {
    match text.parse::<T>() {
        Ok(value) => Ok(value),
        Err(_) => Err(io::Error::new(io::ErrorKind::InvalidInput, error)),
    }
}

/// Parses a graphical `resolution` of the form `WIDTHxHEIGHT[fs]` or `fs`.
fn parse_resolution(mut resolution: &str) -> io::Result<Resolution> {
    if resolution == "fs" {
        return Ok(Resolution::FullScreenDesktop);
    }

    let fullscreen;
    if resolution.ends_with("fs") {
        resolution = resolution.strip_suffix("fs").expect("Suffix presence checked right above");
        fullscreen = true;
    } else {
        fullscreen = false;
    }

    let resolution: Vec<&str> = resolution.split('x').collect();
    match resolution.as_slice() {
        [width, height] => {
            let width = parse_str(width, "Invalid width in resolution")?;
            let height = parse_str(height, "Invalid height in resolution")?;
            if fullscreen {
                Ok(Resolution::full_screen(width, height)?)
            } else {
                Ok(Resolution::windowed(width, height)?)
            }
        }
        _ => Err(io::Error::new(io::ErrorKind::InvalidInput, "Invalid resolution format")),
    }
}

/// Parses a graphical console specification.
pub(crate) fn parse_graphics_spec(params: &str) -> io::Result<(Resolution, Option<&Path>, u16)> {
    let invalid_spec =
        Err(io::Error::new(io::ErrorKind::InvalidInput, "Invalid graphics console spec"));

    let mut params = params.split(',');
    let resolution = match params.next() {
        Some("") => default_resolution(),
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

    Ok((resolution, font_path, font_size))
}

/// Context to maintain a font on disk temporarily.
pub(crate) struct TempFont {
    dir: TempDir,
}

impl TempFont {
    /// Gets an instance of the default font.
    pub(crate) fn default_font() -> io::Result<Self> {
        let dir = tempfile::tempdir()?;
        let mut file = File::create(dir.path().join("font.ttf"))?;
        file.write_all(DEFAULT_FONT_BYTES)?;
        Ok(Self { dir })
    }

    /// Gets the path to the temporary font.
    pub(crate) fn path(&self) -> PathBuf {
        self.dir.path().join("font.ttf")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_resolution_full_screen_desktop() {
        assert_eq!(Resolution::FullScreenDesktop, parse_resolution("fs").unwrap());
    }

    #[test]
    fn test_parse_resolution_full_screen() {
        assert_eq!(
            Resolution::full_screen(123, 45).unwrap(),
            parse_resolution("123x45fs").unwrap()
        );
    }

    #[test]
    fn test_parse_resolution_windowed() {
        assert_eq!(Resolution::windowed(123, 45).unwrap(), parse_resolution("123x45").unwrap());
    }

    #[test]
    fn test_parse_resolution_errors() {
        fn check(exp_error: &str, s: &str) {
            assert_eq!(exp_error, format!("{}", parse_resolution(s).unwrap_err()));
        }
        check("Invalid resolution format", "a");
        check("Invalid width in resolution", "1fsx2");
        check("Invalid height in resolution", "1x2f");
        check("Invalid width in resolution", "ax100");
        check("Invalid height in resolution", "100xa");
        check("Console width cannot be 0", "0x100");
        check("Console height cannot be 0", "100x0");
    }

    #[test]
    fn test_parse_graphics_spec_empty() {
        for spec in ["", ",", ",,"] {
            let spec = parse_graphics_spec(spec).unwrap();
            assert_eq!(default_resolution(), spec.0);
            assert_eq!(None, spec.1);
            assert_eq!(DEFAULT_FONT_SIZE, spec.2);
        }
    }

    #[test]
    fn test_parse_graphics_spec_only_resolution() {
        for spec in ["1024x768", "1024x768,", "1024x768,,"] {
            let spec = parse_graphics_spec(spec).unwrap();
            assert_eq!(Resolution::windowed(1024, 768).unwrap(), spec.0);
            assert_eq!(None, spec.1);
            assert_eq!(DEFAULT_FONT_SIZE, spec.2);
        }
    }

    #[test]
    fn test_parse_graphics_spec_only_font_path() {
        for spec in [",foo.ttf", ",foo.ttf,"] {
            let spec = parse_graphics_spec(spec).unwrap();
            assert_eq!(default_resolution(), spec.0);
            assert_eq!(Some(Path::new("foo.ttf")), spec.1);
            assert_eq!(DEFAULT_FONT_SIZE, spec.2);
        }
    }

    #[test]
    fn test_parse_graphics_spec_only_font_size() {
        let spec = parse_graphics_spec(",,32").unwrap();
        assert_eq!(default_resolution(), spec.0);
        assert_eq!(None, spec.1);
        assert_eq!(32, spec.2);
    }

    #[test]
    fn test_parse_graphics_spec_full() {
        let spec = parse_graphics_spec("1x2,/path/to/font.ttf,24").unwrap();
        assert_eq!(Resolution::windowed(1, 2).unwrap(), spec.0);
        assert_eq!(Some(Path::new("/path/to/font.ttf")), spec.1);
        assert_eq!(24, spec.2);
    }

    #[test]
    fn test_parse_graphics_spec_errors() {
        fn check(exp_error: &str, s: &str) {
            assert_eq!(exp_error, format!("{}", parse_graphics_spec(s).unwrap_err()));
        }
        check("Invalid graphics console spec", ",,,,");
        check("Invalid graphics console spec", "800x600,font.ttf,16,abc");
        check("Invalid resolution format", "a,font.ttf,16");
        check("Invalid font size", "100x200,font.ttf,a");
    }
}
