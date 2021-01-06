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

// TODO(jmmv): All of the supporting code here is duplicated in the other EndBASIC crates.
// Should probably add a separate testutils crate, but I'm hesitant for now.

// Keep these in sync with other top-level files.
#![allow(clippy::await_holding_refcell_ref)]
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(unused, unused_extern_crates, unused_import_braces, unused_qualifications)]
#![warn(unsafe_code)]

use std::env;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process;

/// Computes the path to the directory where this test's binary lives.
fn self_dir() -> PathBuf {
    let self_exe = env::current_exe().expect("Cannot get self's executable path");
    let dir = self_exe.parent().expect("Cannot get self's directory");
    assert!(dir.ends_with("target/debug/deps") || dir.ends_with("target/release/deps"));
    dir.to_owned()
}

/// Computes the path to the built binary `name`.
fn bin_path<P: AsRef<Path>>(name: P) -> PathBuf {
    let test_dir = self_dir();
    let debug_or_release_dir = test_dir.parent().expect("Failed to get parent directory");
    debug_or_release_dir.join(name).with_extension(env::consts::EXE_EXTENSION)
}

/// Computes the path to the source file `name`.
fn src_path(name: &str) -> PathBuf {
    let test_dir = self_dir();
    let debug_or_release_dir = test_dir.parent().expect("Failed to get parent directory");
    let target_dir = debug_or_release_dir.parent().expect("Failed to get parent directory");
    let dir = target_dir.parent().expect("Failed to get parent directory");

    // Sanity-check that we landed in the right location.
    assert!(dir.join("Cargo.toml").exists());

    dir.join(name)
}

/// Describes the behavior for one of the three streams (stdin, stdout, stderr) connected to a
/// program.
enum Behavior {
    /// Ensure the stream is silent.
    Null,

    /// If stdin, feed the given path as the program's input.  If stdout/stderr, expect the contents
    /// of the stream to match this file.
    File(PathBuf),
}

/// Reads the contents of a golden data file.
fn read_golden(path: &Path) -> String {
    let mut f = File::open(path).expect("Failed to open golden data file");
    let mut golden = vec![];
    f.read_to_end(&mut golden).expect("Failed to read golden data file");
    let raw = String::from_utf8(golden).expect("Golden data file is not valid UTF-8");
    if cfg!(target_os = "windows") {
        raw.replace("\r\n", "\n")
    } else {
        raw
    }
}

/// Runs `bin` with arguments `args` and checks its behavior against expectations.
///
/// `exp_code` is the expected error code from the program.  `stdin_behavior` indicates what to feed
/// to the program's stdin.  `stdout_behavior` and `stderr_behavior` indicate what to expect from
/// the program's textual output.
fn check<P: AsRef<Path>>(
    bin: P,
    args: &[&str],
    exp_code: i32,
    stdin_behavior: Behavior,
    stdout_behavior: Behavior,
    stderr_behavior: Behavior,
) {
    let golden_stdin = match stdin_behavior {
        Behavior::Null => process::Stdio::null(),
        Behavior::File(path) => File::open(path).unwrap().into(),
    };

    let exp_stdout = match stdout_behavior {
        Behavior::Null => "".to_owned(),
        Behavior::File(path) => read_golden(&path),
    };

    let exp_stderr = match stderr_behavior {
        Behavior::Null => "".to_owned(),
        Behavior::File(path) => read_golden(&path),
    };

    let result = process::Command::new(bin.as_ref())
        .args(args)
        .stdin(golden_stdin)
        .output()
        .expect("Failed to execute subprocess");
    let code = result.status.code().expect("Subprocess didn't exit cleanly");
    let stdout = String::from_utf8(result.stdout).expect("Stdout not is not valid UTF-8");
    let stderr = String::from_utf8(result.stderr).expect("Stderr not is not valid UTF-8");

    if exp_code != code || exp_stdout != stdout || exp_stderr != stderr {
        eprintln!("Exit code: {}", code);
        eprintln!("stdout:\n{}", stdout);
        eprintln!("stderr:\n{}", stderr);
        assert_eq!(exp_code, code);
        assert_eq!(exp_stdout, stdout);
        assert_eq!(exp_stderr, stderr);
    }
}

#[test]
fn test_example_config() {
    check(
        bin_path("examples/config"),
        &[],
        0,
        Behavior::Null,
        Behavior::File(src_path("core/tests/config.out")),
        Behavior::Null,
    );
}

#[test]
fn test_example_dsl() {
    check(
        bin_path("examples/dsl"),
        &[],
        0,
        Behavior::Null,
        Behavior::File(src_path("core/tests/dsl.out")),
        Behavior::Null,
    );
}
