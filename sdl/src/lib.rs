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

use endbasic_std::console::Console;
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

mod colors;
mod console;
mod spec;

/// Creates the graphical console based on the given `spec`.
pub fn setup(spec: &str) -> io::Result<Rc<RefCell<dyn Console>>> {
    let spec = spec::parse_graphics_spec(spec)?;
    let console = match spec.1 {
        None => {
            let default_font = spec::TempFont::default_font()?;
            console::SdlConsole::new(spec.0, &default_font.path(), spec.2)?
            // The console has been created at this point, so it should be safe to drop
            // default_font and clean up the on-disk file backing it up.
        }
        Some(font_path) => console::SdlConsole::new(spec.0, font_path, spec.2)?,
    };
    Ok(Rc::from(RefCell::from(console)))
}
