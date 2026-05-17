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

//! Logic to instantiate the storage subsystem for the CLI.

use anyhow::{Result, anyhow};
use endbasic_repl::demos::DemoDriveFactory;
use endbasic_std::storage::{DirectoryDriveFactory, Storage};
use std::io;

/// Returns `flag` if present, or else returns the URI of the default `LOCAL` drive.
pub fn get_local_drive_spec(flag: Option<String>) -> Result<String> {
    let dir = flag.or_else(|| {
        dirs::document_dir().map(|d| format!("file://{}", d.join("endbasic").display())).or_else(
            || {
                // On Linux, dirs::document_dir() seems to return None whenever user-dirs.dirs is
                // not present... which is suboptimal.  Compute a reasonable default based on the
                // home directory.
                dirs::home_dir()
                    .map(|h| format!("file://{}", h.join("Documents/endbasic").display()))
            },
        )
    });

    // Instead of aborting on a missing programs directory, we could disable the LOAD/SAVE commands
    // when we cannot compute this folder, but that seems like hiding a corner case that is unlikely
    // to surface.  A good reason to do this, however, would be to allow the user to explicitly
    // disable this functionality to keep the interpreter from touching the disk.
    match dir {
        Some(dir) => Ok(dir),
        None => Err(anyhow!("Cannot compute default path to the Documents folder")),
    }
}

/// Sets up the common storage drives.
///
/// This instantiates non-optional drives, such as `MEMORY:` and `DEMOS:`, maps `LOCAL` the
/// location given in `local_drive_spec`.
pub(crate) fn setup_storage(storage: &mut Storage, local_drive_spec: &str) -> io::Result<()> {
    storage.register_scheme("demos", Box::from(DemoDriveFactory::default()));
    storage.mount("demos", "demos://").expect("Demos drive shouldn't fail to mount");
    storage.register_scheme("file", Box::from(DirectoryDriveFactory::default()));
    storage.mount("local", local_drive_spec)?;
    storage.cd("local:").expect("Local drive was just registered");
    Ok(())
}
