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

//! SDL2-based graphics terminal emulator.

// Keep these in sync with other top-level files.
#![allow(clippy::await_holding_refcell_ref)]
#![allow(clippy::collapsible_else_if)]
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(unused, unused_extern_crates, unused_import_braces, unused_qualifications)]
#![warn(unsafe_code)]

use async_channel::Sender;
use endbasic_core::exec::Signal;
use endbasic_std::console::{Console, ConsoleSpec, Resolution};
use std::cell::RefCell;
use std::fs::File;
use std::io::{self, Write};
use std::num::NonZeroU32;
use std::path::PathBuf;
use std::rc::Rc;
use tempfile::TempDir;

mod console;
mod font;
mod host;

/// Default resolution to use when none is provided.
const DEFAULT_RESOLUTION_PIXELS: (u32, u32) = (800, 600);

/// Default font to use when none is provided.
const DEFAULT_FONT_BYTES: &[u8] = include_bytes!("IBMPlexMono-Regular-6.0.0.ttf");

/// Default font size.
const DEFAULT_FONT_SIZE: u16 = 16;

/// Converts a flat string error message to an `io::Error`.
fn string_error_to_io_error(e: String) -> io::Error {
    io::Error::other(e)
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

/// Creates the graphical console based on the given `spec`.
pub fn setup(
    spec: &mut ConsoleSpec,
    signals_tx: Sender<Signal>,
) -> io::Result<Rc<RefCell<dyn Console>>> {
    let resolution: Resolution = spec.take_keyed_flag("resolution")?.unwrap_or_else(|| {
        let width = NonZeroU32::new(DEFAULT_RESOLUTION_PIXELS.0).unwrap();
        let height = NonZeroU32::new(DEFAULT_RESOLUTION_PIXELS.1).unwrap();
        Resolution::Windowed((width, height))
    });

    let default_fg_color = spec.take_keyed_flag::<u8>("fg_color")?;
    let default_bg_color = spec.take_keyed_flag::<u8>("bg_color")?;

    let font_path = spec.take_keyed_flag::<PathBuf>("font_path")?;

    let font_size = spec.take_keyed_flag("font_size")?.unwrap_or(DEFAULT_FONT_SIZE);

    let console = match font_path {
        None => {
            let default_font = TempFont::default_font()?;
            console::SdlConsole::new(
                resolution,
                default_fg_color,
                default_bg_color,
                default_font.path(),
                font_size,
                signals_tx,
            )?
            // The console has been created at this point, so it should be safe to drop
            // default_font and clean up the on-disk file backing it up.
        }
        Some(font_path) => console::SdlConsole::new(
            resolution,
            default_fg_color,
            default_bg_color,
            font_path.to_owned(),
            font_size,
            signals_tx,
        )?,
    };
    Ok(Rc::from(RefCell::from(console)))
}
