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
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(
    unused,
    unused_extern_crates,
    unused_import_braces,
    unused_qualifications
)]
#![warn(unsafe_code)]

use std::env;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process;

/// Matches a formatted date.
const DATE_RE: &str = "[0-9]{4}-[0-9]{2}-[0-9]{2} [0-2][0-9]:[0-5][0-9]";

/// Matches a version number.
const VERSION_RE: &str = "[0-9]+\\.[0-9]+\\.[0-9]+";

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
    debug_or_release_dir
        .join(name)
        .with_extension(env::consts::EXE_EXTENSION)
}

/// Computes the path to the source file `name`.
fn src_path(name: &str) -> PathBuf {
    let test_dir = self_dir();
    let debug_or_release_dir = test_dir.parent().expect("Failed to get parent directory");
    let target_dir = debug_or_release_dir
        .parent()
        .expect("Failed to get parent directory");
    let dir = target_dir.parent().expect("Failed to get parent directory");

    // Sanity-check that we landed in the right location.
    assert!(dir.join("Cargo.toml").exists());

    dir.join(name)
}

/// Same as `src_path` but returns a string reference for the few places where we need this.
fn src_str(p: &str) -> String {
    src_path(p)
        .to_str()
        .expect("Need paths to be valid strings")
        .to_owned()
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
    f.read_to_end(&mut golden)
        .expect("Failed to read golden data file");
    let raw = String::from_utf8(golden).expect("Golden data file is not valid UTF-8");
    let golden = if cfg!(target_os = "windows") {
        raw.replace("\r\n", "\n")
    } else {
        raw
    };

    // This is the opposite of apply_mocks and ensures we don't leak actual values into the golden
    // files by mistake.
    let version_re = regex::Regex::new(VERSION_RE).unwrap();
    assert!(
        !version_re.is_match(&golden),
        "Golden file {} contains a version number",
        path.display()
    );
    let date_re = regex::Regex::new(DATE_RE).unwrap();
    assert!(
        !date_re.is_match(&golden),
        "Golden file {} contains a date",
        path.display()
    );

    golden
}

/// Replaces the parts of the output that can change due to the environment with placeholders.
fn apply_mocks(input: String) -> String {
    let version_re = regex::Regex::new(VERSION_RE).unwrap();
    let input = version_re.replace_all(&input, "X.Y.Z").to_owned();

    let date_re = regex::Regex::new(DATE_RE).unwrap();
    date_re.replace_all(&input, "YYYY-MM-DD HH:MM").into()
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
    let code = result
        .status
        .code()
        .expect("Subprocess didn't exit cleanly");
    let stdout =
        apply_mocks(String::from_utf8(result.stdout).expect("Stdout not is not valid UTF-8"));
    let stderr =
        apply_mocks(String::from_utf8(result.stderr).expect("Stderr not is not valid UTF-8"));

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
fn test_example_complete() {
    // Nothing to do.  We use this example program to run all language tests below.
}

#[test]
fn test_example_custom_commands() {
    check(
        bin_path("examples/custom-commands"),
        &[],
        0,
        Behavior::Null,
        Behavior::File(src_path("core/examples/custom-commands.out")),
        Behavior::Null,
    );
}

#[test]
fn test_example_minimal() {
    check(
        bin_path("examples/minimal"),
        &[],
        0,
        Behavior::Null,
        Behavior::File(src_path("core/examples/minimal.out")),
        Behavior::Null,
    );
}

#[test]
fn test_lang_console() {
    check(
        bin_path("examples/complete"),
        &[&src_str("core/tests/console.bas")],
        0,
        Behavior::Null,
        Behavior::File(src_path("core/tests/console.out")),
        Behavior::Null,
    );
}

#[test]
fn test_lang_control_flow() {
    check(
        bin_path("examples/complete"),
        &[&src_str("core/tests/control-flow.bas")],
        0,
        Behavior::Null,
        Behavior::File(src_path("core/tests/control-flow.out")),
        Behavior::Null,
    );
}

#[test]
fn test_lang_exec_error() {
    check(
        bin_path("examples/complete"),
        &[&src_str("core/tests/exec-error.bas")],
        1,
        Behavior::Null,
        Behavior::File(src_path("core/tests/exec-error.out")),
        Behavior::File(src_path("core/tests/exec-error.err")),
    );
}

#[test]
fn test_lang_hello() {
    check(
        bin_path("examples/complete"),
        &[&src_str("core/tests/hello.bas")],
        0,
        Behavior::Null,
        Behavior::File(src_path("core/tests/hello.out")),
        Behavior::Null,
    );
}

#[test]
fn test_lang_lexer_error() {
    check(
        bin_path("examples/complete"),
        &[&src_str("core/tests/lexer-error.bas")],
        1,
        Behavior::Null,
        Behavior::File(src_path("core/tests/lexer-error.out")),
        Behavior::File(src_path("core/tests/lexer-error.err")),
    );
}

#[test]
fn test_lang_no_repl_commands() {
    check(
        bin_path("examples/complete"),
        &[&src_str("core/tests/no-repl-commands.bas")],
        1,
        Behavior::Null,
        Behavior::File(src_path("core/tests/no-repl-commands.out")),
        Behavior::File(src_path("core/tests/no-repl-commands.err")),
    );
}

#[test]
fn test_lang_parser_error() {
    check(
        bin_path("examples/complete"),
        &[&src_str("core/tests/parser-error.bas")],
        1,
        Behavior::Null,
        Behavior::File(src_path("core/tests/parser-error.out")),
        Behavior::File(src_path("core/tests/parser-error.err")),
    );
}

#[test]
fn test_lang_types() {
    check(
        bin_path("examples/complete"),
        &[&src_str("core/tests/types.bas")],
        0,
        Behavior::Null,
        Behavior::File(src_path("core/tests/types.out")),
        Behavior::Null,
    );
}

#[test]
fn test_lang_utf8() {
    check(
        bin_path("examples/complete"),
        &[&src_str("core/tests/utf8.bas")],
        0,
        Behavior::File(src_path("core/tests/utf8.in")),
        Behavior::File(src_path("core/tests/utf8.out")),
        Behavior::Null,
    );
}

#[test]
fn test_lang_yes_no() {
    check(
        bin_path("examples/complete"),
        &[&src_str("core/tests/yes-no.bas")],
        0,
        Behavior::File(src_path("core/tests/yes-no.in")),
        Behavior::File(src_path("core/tests/yes-no.out")),
        Behavior::Null,
    );
}
