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

    /// If stdin, this is not supported.  If stdout/stderr, expect the contents of the stream to
    /// match this literal string.
    Literal(String),
}

/// Reads the contents of a golden data file.
fn read_golden(path: &Path) -> String {
    let mut f = File::open(path).expect("Failed to open golden data file");
    let mut golden = vec![];
    f.read_to_end(&mut golden)
        .expect("Failed to read golden data file");
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
        Behavior::Literal(_) => panic!("Literals not supported for stdin"),
    };

    let exp_stdout = match stdout_behavior {
        Behavior::Null => "".to_owned(),
        Behavior::File(path) => read_golden(&path),
        Behavior::Literal(text) => text,
    };

    let exp_stderr = match stderr_behavior {
        Behavior::Null => "".to_owned(),
        Behavior::File(path) => read_golden(&path),
        Behavior::Literal(text) => text,
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

// TODO(jmmv): This test fails almost always on Linux CI builds with `Text file busy` when
// attempting to run the copied binary.  I've also gotten it to occasionally fail on a local Linux
// installation in the same way, but that's much harder to trigger.  Investigate what's going on.
#[cfg(not(target_os = "linux"))]
#[test]
fn test_cli_program_name_uses_arg0() {
    use std::fs;

    struct DeleteOnDrop<'a> {
        path: &'a Path,
    }

    impl<'a> Drop for DeleteOnDrop<'a> {
        fn drop(&mut self) {
            let _best_effort_removal = fs::remove_file(self.path);
        }
    }

    let original = bin_path("endbasic");
    let custom = self_dir()
        .join("custom-name")
        .with_extension(env::consts::EXE_EXTENSION);
    let _delete_custom = DeleteOnDrop { path: &custom };
    fs::copy(&original, &custom).unwrap();
    check(
        &custom,
        &["one", "two", "three"],
        2,
        Behavior::Null,
        Behavior::Null,
        Behavior::Literal("custom-name: Usage error: Too many arguments\n".to_owned()),
    );
}

#[test]
fn test_cli_too_many_args() {
    check(
        &bin_path("endbasic"),
        &["foo", "bar"],
        2,
        Behavior::Null,
        Behavior::Null,
        Behavior::Literal("endbasic: Usage error: Too many arguments\n".to_owned()),
    );
}

#[test]
fn test_example_custom_commands() {
    check(
        bin_path("examples/custom-commands"),
        &[],
        0,
        Behavior::Null,
        Behavior::File(src_path("examples/custom-commands.out")),
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
        Behavior::File(src_path("examples/minimal.out")),
        Behavior::Null,
    );
}

#[test]
fn test_lang_control_flow() {
    check(
        bin_path("endbasic"),
        &[&src_str("tests/lang/control-flow.bas")],
        0,
        Behavior::Null,
        Behavior::File(src_path("tests/lang/control-flow.out")),
        Behavior::Null,
    );
}

#[test]
fn test_lang_exec_error() {
    check(
        bin_path("endbasic"),
        &[&src_str("tests/lang/exec-error.bas")],
        1,
        Behavior::Null,
        Behavior::File(src_path("tests/lang/exec-error.out")),
        Behavior::File(src_path("tests/lang/exec-error.err")),
    );
}

#[test]
fn test_lang_hello() {
    check(
        bin_path("endbasic"),
        &[&src_str("tests/lang/hello.bas")],
        0,
        Behavior::Null,
        Behavior::File(src_path("tests/lang/hello.out")),
        Behavior::Null,
    );
}

#[test]
fn test_lang_lexer_error() {
    check(
        bin_path("endbasic"),
        &[&src_str("tests/lang/lexer-error.bas")],
        1,
        Behavior::Null,
        Behavior::File(src_path("tests/lang/lexer-error.out")),
        Behavior::File(src_path("tests/lang/lexer-error.err")),
    );
}

#[test]
fn test_lang_no_repl_commands() {
    check(
        bin_path("endbasic"),
        &[&src_str("tests/lang/no-repl-commands.bas")],
        1,
        Behavior::Null,
        Behavior::File(src_path("tests/lang/no-repl-commands.out")),
        Behavior::File(src_path("tests/lang/no-repl-commands.err")),
    );
}

#[test]
fn test_lang_parser_error() {
    check(
        bin_path("endbasic"),
        &[&src_str("tests/lang/parser-error.bas")],
        1,
        Behavior::Null,
        Behavior::File(src_path("tests/lang/parser-error.out")),
        Behavior::File(src_path("tests/lang/parser-error.err")),
    );
}

#[test]
fn test_lang_types() {
    check(
        bin_path("endbasic"),
        &[&src_str("tests/lang/types.bas")],
        0,
        Behavior::Null,
        Behavior::File(src_path("tests/lang/types.out")),
        Behavior::Null,
    );
}

#[test]
fn test_lang_utf8() {
    check(
        bin_path("endbasic"),
        &[&src_str("tests/lang/utf8.bas")],
        0,
        Behavior::File(src_path("tests/lang/utf8.in")),
        Behavior::File(src_path("tests/lang/utf8.out")),
        Behavior::Null,
    );
}

#[test]
fn test_lang_yes_no() {
    check(
        bin_path("endbasic"),
        &[&src_str("tests/lang/yes-no.bas")],
        0,
        Behavior::File(src_path("tests/lang/yes-no.in")),
        Behavior::File(src_path("tests/lang/yes-no.out")),
        Behavior::Null,
    );
}

#[test]
fn test_repl_editor() {
    check(
        bin_path("endbasic"),
        &[],
        0,
        Behavior::File(src_path("tests/repl/editor.in")),
        Behavior::File(src_path("tests/repl/editor.out")),
        Behavior::Null,
    );
}

#[test]
fn test_repl_help() {
    check(
        bin_path("endbasic"),
        &[],
        0,
        Behavior::File(src_path("tests/repl/help.in")),
        Behavior::File(src_path("tests/repl/help.out")),
        Behavior::Null,
    );
}

#[test]
fn test_repl_interactive() {
    check(
        bin_path("endbasic"),
        &[],
        0,
        Behavior::File(src_path("tests/repl/interactive.in")),
        Behavior::File(src_path("tests/repl/interactive.out")),
        Behavior::Null,
    );
}

#[test]
fn test_repl_state_sharing() {
    check(
        bin_path("endbasic"),
        &[],
        0,
        Behavior::File(src_path("tests/repl/state-sharing.in")),
        Behavior::File(src_path("tests/repl/state-sharing.out")),
        Behavior::Null,
    );
}
