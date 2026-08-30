// EndBASIC
// Copyright 2020 Julio Merino
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

    // Sanity-check that we landed in the right location.
    assert!(dir.join("Cargo.lock").exists());

    dir.join(name)
}

/// Same as `src_path` but returns a string reference for command arguments.
fn src_str(p: &str) -> String {
    src_path(p).to_str().expect("Need paths to be valid strings").to_owned()
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
fn test_example_script_runner() {
    Command::cargo_bin("examples/script-runner")
        .unwrap()
        .arg(src_str("std/tests/script.bas"))
        .assert()
        .success()
        .stdout(read_golden("std/tests/script.out"))
        .stderr("");
}

#[test]
fn test_example_script_runner_errors() {
    Command::cargo_bin("examples/script-runner")
        .unwrap()
        .arg(src_str("std/tests/script-errors.bas"))
        .assert()
        .code(1)
        .stdout("")
        .stderr(read_golden("std/tests/script-errors.err"));
}
