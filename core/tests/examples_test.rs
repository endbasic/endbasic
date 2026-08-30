// EndBASIC
// Copyright 2020 Julio Merino
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

//! Integration tests that use golden input and output files.

use assert_cmd::Command;
use std::env;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};

/// Computes the path to the source file `name`.
fn src_path(name: &str) -> PathBuf {
    let dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).parent().expect("Failed to get parent directory");

    assert!(dir.join("Cargo.lock").exists());
    dir.join(name)
}

/// Reads the contents of a golden data file.
fn read_golden(name: &str) -> String {
    let path = src_path(name);
    let mut f = File::open(&path).expect("Failed to open golden data file");
    let mut golden = vec![];
    f.read_to_end(&mut golden).expect("Failed to read golden data file");
    let raw = String::from_utf8(golden).expect("Golden data file is not valid UTF-8");
    if cfg!(target_os = "windows") { raw.replace("\r\n", "\n") } else { raw }
}

#[test]
fn test_config() {
    Command::cargo_bin("examples/core-config")
        .unwrap()
        .assert()
        .success()
        .stdout(read_golden("core/tests/config.out"))
        .stderr("");
}
