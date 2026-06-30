// EndBASIC
// Copyright 2026 Julio Merino
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

//! Parser for the optional script property line.

use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::path::Path;

/// Properties encoded in the second line of a script.
#[derive(Debug, Default, Eq, PartialEq)]
pub struct PropLine {
    /// Optional console specification to use as the default for the script.
    pub console_spec: Option<String>,
}

/// Strips the newline terminator from `s` if present.
fn strip_newline(s: &mut String) {
    if s.ends_with('\n') {
        s.pop();
        if s.ends_with('\r') {
            s.pop();
        }
    }
}

/// Parses a propline from `line`.
///
/// Returns an error if `line` looks like a propline but its contents are invalid.
fn parse_propline(line: &str) -> io::Result<PropLine> {
    let without_comment = match line.strip_prefix("' ") {
        Some(line) => Some(line),
        None => {
            if line.len() <= 4 {
                None
            } else {
                let token = line[0..4].to_ascii_lowercase();
                if token == "rem " { Some(&line[4..]) } else { None }
            }
        }
    };
    let Some(payload) = without_comment else {
        return Ok(PropLine::default());
    };

    let Some(payload) = payload.strip_prefix("endbasic cli: ") else {
        return Ok(PropLine::default());
    };

    let Some(console_spec) = payload.strip_prefix("console=") else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("Invalid EndBASIC propline: {}", line),
        ));
    };

    if console_spec.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "Invalid EndBASIC propline: missing console specification",
        ));
    }

    Ok(PropLine { console_spec: Some(console_spec.to_owned()) })
}

/// Extracts the property line from `path` if present.
pub fn extract_propline<P: AsRef<Path>>(path: P) -> io::Result<PropLine> {
    let input = File::open(path)?;
    let mut input = BufReader::new(input);

    let mut line1 = String::new();
    if input.read_line(&mut line1)? == 0 {
        return Ok(PropLine::default());
    }
    strip_newline(&mut line1);
    if !line1.starts_with("#!") {
        return Ok(PropLine::default());
    }

    let mut line2 = String::new();
    if input.read_line(&mut line2)? == 0 {
        return Ok(PropLine::default());
    }
    strip_newline(&mut line2);
    parse_propline(&line2)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    /// Creates a file with `contents` and tries to extract its propline.
    fn do_extract(contents: &str) -> io::Result<PropLine> {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("script.bas");
        fs::write(&path, contents).unwrap();
        extract_propline(path)
    }

    #[test]
    fn test_extract_propline_no_shebang() {
        let propline = do_extract("PRINT \"hello\"\n").unwrap();
        assert_eq!(PropLine::default(), propline);
    }

    #[test]
    fn test_extract_propline_apostrophe() {
        let propline =
            do_extract("#!/usr/bin/env endbasic\n' endbasic cli: console=sdl\nPRINT 1\n").unwrap();
        assert_eq!(Some("sdl".to_owned()), propline.console_spec);
    }

    #[test]
    fn test_extract_propline_rem_mixed_case() {
        let propline =
            do_extract("#!/usr/bin/env endbasic\nReM endbasic cli: console=sdl:fs\n").unwrap();
        assert_eq!(Some("sdl:fs".to_owned()), propline.console_spec);
    }

    #[test]
    fn test_extract_propline_ignores_unrelated_comment() {
        let propline = do_extract("#!/usr/bin/env endbasic\nREM regular comment\n").unwrap();
        assert_eq!(PropLine::default(), propline);
    }

    #[test]
    fn test_extract_propline_errors_on_bad_prefix() {
        let error = do_extract("#!/usr/bin/env endbasic\n' endbasic cli: nope\n").unwrap_err();
        assert_eq!(io::ErrorKind::InvalidInput, error.kind());
        assert_eq!("Invalid EndBASIC propline: ' endbasic cli: nope", error.to_string());
    }

    #[test]
    fn test_extract_propline_errors_on_empty_console_spec() {
        let error =
            do_extract("#!/usr/bin/env endbasic\nREM endbasic cli: console=\n").unwrap_err();
        assert_eq!(io::ErrorKind::InvalidInput, error.kind());
        assert_eq!("Invalid EndBASIC propline: missing console specification", error.to_string());
    }
}
