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
fn get_test_dir() -> PathBuf {
    let self_exe = env::current_exe().expect("Cannot get self's executable path");
    let dir = self_exe.parent().expect("Cannot get self's directory");
    assert!(dir.ends_with("target/debug/deps") || dir.ends_with("target/release/deps"));
    dir.to_owned()
}

/// Computes the path the tested binary.
fn get_bin(bin: &str) -> PathBuf {
    let test_dir = get_test_dir();
    let debug_or_release_dir = test_dir.parent().expect("Failed to get parent directory");
    debug_or_release_dir
        .join(bin)
        .with_extension(env::consts::EXE_EXTENSION)
}

/// Computes the path to the root of the source tree.
fn get_src_dir() -> PathBuf {
    let test_dir = get_test_dir();
    let debug_or_release_dir = test_dir.parent().expect("Failed to get parent directory");
    let target_dir = debug_or_release_dir
        .parent()
        .expect("Failed to get parent directory");
    let dir = target_dir.parent().expect("Failed to get parent directory");

    // Sanity-check that we landed in the right location.
    assert!(dir.join("Cargo.toml").exists());

    dir.to_owned()
}

/// Runs the binary from `path` with `args` and compares its output against expected values.
///
/// `exp-code` specifies the expected exit code of the binary.  `golden_stdin` provides the input
/// to feed to stdin.  `exp_stdout` and `exp_stderr` specify the expected stdout and stderr
/// contents.
fn check_program<I: Into<process::Stdio>>(
    bin: &Path,
    args: &[&str],
    exp_code: i32,
    golden_stdin: I,
    exp_stdout: &str,
    exp_stderr: &str,
) {
    let result = process::Command::new(bin)
        .args(args)
        .stdin(golden_stdin)
        .output()
        .expect("Failed to execute subprocess");
    let code = result
        .status
        .code()
        .expect("Subprocess didn't exit cleanly");
    let stdout = String::from_utf8(result.stdout).expect("Actual stdout not is not valid UTF-8");
    let stderr = String::from_utf8(result.stderr).expect("Actual stderr not is not valid UTF-8");

    if exp_code != code || exp_stdout != stdout || exp_stderr != stderr {
        eprintln!("Exit code: {}", code);
        eprintln!("stdout:\n{}", stdout);
        eprintln!("stderr:\n{}", stderr);
        assert_eq!(exp_code, code);
        assert_eq!(exp_stdout, stdout);
        assert_eq!(exp_stderr, stderr);
    }
}

/// Runs the interpreter with `args` and compares its output against expected values.
///
/// `exp-code` specifies the expected exit code of the binary.  `exp_stdout` and `exp_stderr`
/// specify the expected stdout and stderr contents.
fn check(args: &[&str], exp_code: i32, exp_stdout: &str, exp_stderr: &str) {
    let bin = get_bin("endbasic");
    check_program(
        &bin,
        args,
        exp_code,
        process::Stdio::null(),
        exp_stdout,
        exp_stderr,
    )
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

/// Runs the `name.bas` program and compares its output against golden data in files.
///
/// A `name.in` file next to the source file, if present, is fed to the program as its stdin.
///
/// The `name.out` and `name.err` files next to the source file, if present, contain the golden
/// stdout and stderr for the program, respectively.  Furthermore, if `name.err` exists, the
/// program is expected to exit with an error; otherwise, it is expected to exit successfully.
fn do_golden_test(name: &str) {
    let bas_path = get_src_dir().join("tests").join(name).with_extension("bas");
    let in_path = get_src_dir().join("tests").join(name).with_extension("in");
    let out_path = get_src_dir().join("tests").join(name).with_extension("out");
    let err_path = get_src_dir().join("tests").join(name).with_extension("err");

    let input = if in_path.exists() {
        File::open(in_path).unwrap().into()
    } else {
        process::Stdio::null()
    };

    let golden_code = if err_path.exists() { 1 } else { 0 };

    let golden_stdout = if out_path.exists() {
        read_golden(&out_path)
    } else {
        "".to_owned()
    };

    let golden_stderr = if err_path.exists() {
        read_golden(&err_path)
    } else {
        "".to_owned()
    };

    let bin = get_bin("endbasic");
    check_program(
        &bin,
        &[bas_path.to_str().unwrap()],
        golden_code,
        input,
        &golden_stdout,
        &golden_stderr,
    )
}

#[test]
fn test_golden_control_flow() {
    do_golden_test("control-flow");
}

#[test]
fn test_golden_exec_error() {
    do_golden_test("exec-error");
}

#[test]
fn test_golden_hello() {
    do_golden_test("hello");
}

#[test]
fn test_golden_lexer_error() {
    do_golden_test("lexer-error");
}

#[test]
fn test_golden_parser_error() {
    do_golden_test("parser-error");
}

#[test]
fn test_golden_types() {
    do_golden_test("types");
}

#[test]
fn test_golden_utf8() {
    do_golden_test("utf8");
}

#[test]
fn test_no_args() {
    check(&[], 1, "", "endbasic: E: No program specified\n");
}

#[test]
fn test_too_many_args() {
    check(&["foo", "bar"], 1, "", "endbasic: E: Too many arguments\n");
}

// TODO(jmmv): This test fails almost always on Linux CI builds with `Text file busy` when
// attempting to run the copied binary.  I've also gotten it to occasionally fail on a local Linux
// installation in the same way, but that's much harder to trigger.  Investigate what's going on.
#[cfg(not(target_os = "linux"))]
#[test]
fn test_program_name_uses_arg0() {
    use std::fs;

    struct DeleteOnDrop<'a> {
        path: &'a Path,
    }

    impl<'a> Drop for DeleteOnDrop<'a> {
        fn drop(&mut self) {
            let _best_effort_removal = fs::remove_file(self.path);
        }
    }

    let original = get_bin("endbasic");
    let custom = get_test_dir()
        .join("custom-name")
        .with_extension(env::consts::EXE_EXTENSION);
    let _delete_custom = DeleteOnDrop { path: &custom };
    fs::copy(&original, &custom).unwrap();
    check_program(
        &custom,
        &[],
        1,
        process::Stdio::null(),
        "",
        "custom-name: E: No program specified\n",
    );
}
