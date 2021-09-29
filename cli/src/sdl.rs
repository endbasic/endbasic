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

use std::io;
use std::path::Path;
use std::str::FromStr;

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
pub fn parse_graphics_spec(params: &str) -> io::Result<(u32, u32, &Path, u16)> {
    let invalid_spec =
        Err(io::Error::new(io::ErrorKind::InvalidInput, "Invalid graphics console spec"));
    let mut params = params.split(',');
    let resolution = match params.next() {
        Some(resolution) => resolution,
        None => return invalid_spec,
    };
    let font_path = match params.next() {
        Some(font_path) => font_path,
        None => return invalid_spec,
    };
    let font_size = match params.next() {
        Some(font_size) => font_size,
        None => return invalid_spec,
    };
    if params.next().is_some() {
        return invalid_spec;
    }

    let (width, height) = parse_resolution(resolution)?;
    let font_path = Path::new(font_path);
    let font_size = parse_str(font_size, "Invalid font size")?;
    Ok((width, height, font_path, font_size))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_graphics_spec_ok() {
        let spec = parse_graphics_spec("800x600,/path/to/font.ttf,16").unwrap();
        assert_eq!(800, spec.0);
        assert_eq!(600, spec.1);
        assert_eq!(Path::new("/path/to/font.ttf"), spec.2);
        assert_eq!(16, spec.3);
    }

    #[test]
    fn test_parse_graphics_spec_errors() {
        fn check(exp_error: &str, s: &str) {
            assert_eq!(exp_error, format!("{}", parse_graphics_spec(s).unwrap_err()));
        }
        check("Invalid graphics console spec", "abc");
        check("Invalid graphics console spec", "800x600");
        check("Invalid graphics console spec", "800x600,font.ttf");
        check("Invalid graphics console spec", "800x600,font.ttf,16,abc");
        check("Invalid resolution format", "a,font.ttf,16");
        check("Invalid width in resolution", "ax100,font.ttf,16");
        check("Invalid height in resolution", "100xa,font.ttf,16");
        check("Invalid font size", "100x200,font.ttf,a");
    }
}
