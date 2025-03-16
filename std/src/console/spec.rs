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

use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::io;
use std::num::NonZeroU32;
use std::str::FromStr;

/// An error while parsing a console specification.
#[derive(Debug, thiserror::Error)]
#[error("{}", .0)]
pub struct ParseError(pub String);

impl From<ParseError> for io::Error {
    fn from(value: ParseError) -> Self {
        Self::new(io::ErrorKind::InvalidInput, value.0)
    }
}

/// Syntactic sugar to create an error.
macro_rules! mkerror {
    ($($arg:tt)*) => ({
        ParseError(format!($($arg)*))
    })
}

/// Result type for console specification parse errors.
type Result<T> = std::result::Result<T, ParseError>;

/// Representation of a screen resolution in pixels.
#[derive(Debug, PartialEq)]
pub enum Resolution {
    /// Tells the console to start in full screen mode at the current desktop resolution.
    FullScreenDesktop,

    /// Tells the console to start in full screen mode at the given resolution.
    FullScreen((NonZeroU32, NonZeroU32)),

    /// Tells the console to start in windowed mode at the given resolution.
    Windowed((NonZeroU32, NonZeroU32)),
}

/// Parses a graphical `resolution` of the form `[WIDTHxHEIGHT][fs]`.
fn parse_resolution(resolution: &str) -> Result<Resolution> {
    if resolution == "fs" {
        return Ok(Resolution::FullScreenDesktop);
    }

    let (dimensions, fullscreen) = match resolution.strip_suffix("fs") {
        Some(prefix) => (prefix, true),
        None => (resolution, false),
    };

    match dimensions.split_once('x') {
        Some((width, height)) => {
            let width = NonZeroU32::from_str(width).map_err(|e| {
                mkerror!("Invalid width {} in resolution {}: {}", width, resolution, e)
            })?;
            let height = NonZeroU32::from_str(height).map_err(|e| {
                mkerror!("Invalid height {} in resolution {}: {}", height, resolution, e)
            })?;

            if fullscreen {
                Ok(Resolution::FullScreen((width, height)))
            } else {
                Ok(Resolution::Windowed((width, height)))
            }
        }
        _ => Err(mkerror!(
            "Invalid resolution {}: must be of the form [WIDTHxHEIGHT][fs]",
            resolution
        )),
    }
}

impl FromStr for Resolution {
    type Err = ParseError;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        parse_resolution(s)
    }
}

/// Parser for a console specification.
///
/// A console specification is a string of the form `driver[:flags]`.  The optional flags are a
/// sequence of comma-separated flags where each flag can be a a boolean flag represented as a plain
/// string or keyed flag represented as a `key=value` string.
///
/// The interface of this parser is designed to be instantiated from `main` based on a user-supplied
/// flag and then passed on to the specific console drivers for additional parsing.  `main` then
/// needs to call `finish` to ensure that all provided flags have been parsed.
pub struct ConsoleSpec<'a> {
    /// The name of the desired console driver.
    pub driver: &'a str,

    /// Collection of boolean flags that appear in the input specification and that haven't been
    /// queried yet.
    flags: HashSet<&'a str>,

    /// Collection of keyed flags that appear in the input specification and that haven't been
    /// queried yet.
    keyed_flags: HashMap<&'a str, &'a str>,
}

impl<'a> ConsoleSpec<'a> {
    /// Initializes the console specification parser from `s`.
    ///
    /// `s` *must* not be empty.  The caller must supply, at least, a default console driver name
    /// if the user did not specify any console flag.
    pub fn init(s: &'a str) -> Self {
        assert!(!s.is_empty());

        let (driver, rest) = s.split_once(':').unwrap_or((s, ""));

        let mut flags = HashSet::default();
        let mut keyed_flags = HashMap::default();
        for pair in rest.split(',') {
            if pair.is_empty() {
                continue;
            }

            match pair.split_once('=') {
                None => {
                    let _exists = flags.insert(pair);
                }
                Some((k, v)) => {
                    let _old = keyed_flags.insert(k, v);
                }
            }
        }

        Self { driver, flags, keyed_flags }
    }

    /// Queries whether the boolean `flag` is in the specification or not.
    ///
    /// The flag is marked as "checked" so that `finish` won't raise it as residual.
    pub fn take_flag(&mut self, flag: &str) -> bool {
        self.flags.remove(flag)
    }

    /// Queries the value of the keyed `flag` from the specification, which may or may not be
    /// present.  The value is returned as a raw string.
    pub fn take_keyed_flag_str(&mut self, key: &str) -> Option<&str> {
        self.keyed_flags.remove(key)
    }

    /// Queries the value of the keyed `flag` from the specification, which may or may not be
    /// present.  The value is parsed according to the type `V`.
    ///
    /// The flag is marked as  "checked" so that `finish` won't raise it as residual.
    pub fn take_keyed_flag<V>(&mut self, key: &str) -> Result<Option<V>>
    where
        V: FromStr,
        V::Err: Display,
    {
        match self.take_keyed_flag_str(key) {
            Some(v) => V::from_str(v)
                .map(|v| Some(v))
                .map_err(|e| mkerror!("Invalid console flag {}: {}", key, e)),
            None => Ok(None),
        }
    }

    /// Validates that all provided flags have been queried by the driver.
    pub fn finish(self) -> Result<()> {
        if self.flags.is_empty() && self.keyed_flags.is_empty() {
            Ok(())
        } else {
            let flags_iter = self.flags.into_iter();
            let keyed_iter = self.keyed_flags.into_keys();
            let mut unknown = flags_iter.chain(keyed_iter).collect::<Vec<&'a str>>();
            unknown.sort();
            Err(mkerror!(
                "Console driver {} does not recognize flags: {}",
                self.driver,
                unknown.join(", ")
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resolution_ok() -> Result<()> {
        let nz100 = NonZeroU32::new(100).unwrap();
        let nz200 = NonZeroU32::new(200).unwrap();
        for (s, exp_resolution) in [
            ("100x200", Resolution::Windowed((nz100, nz200))),
            ("100x200fs", Resolution::FullScreen((nz100, nz200))),
            ("fs", Resolution::FullScreenDesktop),
        ] {
            assert_eq!(exp_resolution, Resolution::from_str(s)?);
        }
        Ok(())
    }

    #[test]
    fn test_resolution_errors() -> Result<()> {
        for (s, exp_error) in [
            ("100", "Invalid resolution 100: must be of the form [WIDTHxHEIGHT][fs]"),
            ("100fs", "Invalid resolution 100fs: must be of the form [WIDTHxHEIGHT][fs]"),
            (
                "100x200x300",
                "Invalid height 200x300 in resolution 100x200x300: invalid digit found in string",
            ),
            ("100x", "Invalid height  in resolution 100x: cannot parse integer from empty string"),
            ("x200", "Invalid width  in resolution x200: cannot parse integer from empty string"),
            ("0x2", "Invalid width 0 in resolution 0x2: number would be zero for non-zero type"),
            ("1x0", "Invalid height 0 in resolution 1x0: number would be zero for non-zero type"),
        ] {
            match Resolution::from_str(s) {
                Ok(_) => panic!("Invalid resolution {} not raised as an error", s),
                Err(e) => assert_eq!(exp_error, e.0),
            }
        }
        Ok(())
    }

    #[test]
    fn test_console_spec_just_driver() -> Result<()> {
        let spec = ConsoleSpec::init("default");
        assert_eq!("default", spec.driver);
        spec.finish()
    }

    #[test]
    fn test_console_spec_driver_no_opts() -> Result<()> {
        let spec = ConsoleSpec::init("default:");
        assert_eq!("default", spec.driver);
        spec.finish()
    }

    #[test]
    fn test_console_spec_flags() -> Result<()> {
        let mut spec = ConsoleSpec::init("default:foo,baz");
        assert_eq!("default", spec.driver);
        assert!(spec.take_flag("foo"));
        assert!(!spec.take_flag("bar"));
        assert!(spec.take_flag("baz"));
        spec.finish()
    }

    #[test]
    fn test_console_spec_keyed_flags() -> Result<()> {
        let mut spec = ConsoleSpec::init("default:a=b=c,foo=bar");
        assert_eq!("default", spec.driver);
        assert_eq!(Some("b=c"), spec.take_keyed_flag_str("a"));
        assert_eq!(Some("bar"), spec.take_keyed_flag_str("foo"));
        assert_eq!(None, spec.take_keyed_flag_str("baz"));
        spec.finish()
    }

    #[test]
    fn test_console_spec_keyed_flags_last_wins() -> Result<()> {
        let mut spec = ConsoleSpec::init("default:x=1,y=2,x=3");
        assert_eq!("default", spec.driver);
        assert_eq!(Some("3"), spec.take_keyed_flag_str("x"));
        assert_eq!(Some("2"), spec.take_keyed_flag_str("y"));
        spec.finish()
    }

    #[test]
    fn test_console_spec_keyed_flags_typed_ok() -> Result<()> {
        let mut spec = ConsoleSpec::init("default:x=1");
        assert_eq!("default", spec.driver);
        assert_eq!(Some(1_i32), spec.take_keyed_flag("x")?);
        assert_eq!(None as Option<i32>, spec.take_keyed_flag("x")?);
        spec.finish()
    }

    #[test]
    fn test_console_spec_keyed_flags_typed_err() -> Result<()> {
        let mut spec = ConsoleSpec::init("default:x=0");
        assert_eq!("default", spec.driver);
        assert_eq!(
            "Invalid console flag x: number would be zero for non-zero type",
            spec.take_keyed_flag::<NonZeroU32>("x").unwrap_err().0
        );
        spec.finish()
    }

    #[test]
    fn test_console_spec_residue_errors() -> Result<()> {
        let mut spec = ConsoleSpec::init("abc:foo,y,x=z,bar=baz");
        assert!(spec.take_flag("foo"));
        assert!(!spec.take_flag("x"));
        assert_eq!(Some("baz"), spec.take_keyed_flag_str("bar"));
        assert_eq!(None, spec.take_keyed_flag_str("y"));
        match spec.finish() {
            Ok(()) => panic!("Residual flags not detected"),
            Err(e) => {
                assert_eq!("Console driver abc does not recognize flags: x, y", e.0);
                Ok(())
            }
        }
    }
}
