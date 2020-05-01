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
fn get_bin<P: AsRef<Path>>(bin: P) -> PathBuf {
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

/// Runs the program `bin_path` with `args` and compares its output against golden data files.
///
/// A `data_dir/name.in` file, if present, is fed to the program as its stdin.
///
/// The `data_dir/name.out` and `data_dir/name.err` files, if present, contain the golden stdout
/// and stderr for the program, respectively.  Furthermore, if `data_dir/name.err` exists, the
/// program is expected to exit with an error; otherwise, it is expected to exit successfully.
fn check<P: AsRef<Path>>(bin_path: P, args: &[&str], name: &str, data_dir: P) {
    let bin_path = bin_path.as_ref();
    let data_dir = data_dir.as_ref();

    let in_path = data_dir.join(name).with_extension("in");
    let out_path = data_dir.join(name).with_extension("out");
    let err_path = data_dir.join(name).with_extension("err");

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

    check_program(
        &bin_path,
        args,
        golden_code,
        input,
        &golden_stdout,
        &golden_stderr,
    )
}

/// Runs the given example program and compares its output against golden data files.
///
/// The data files are expected to be in the `examples` subdirectory and have `name` as their
/// basename.  See the description in `check` for more details.
fn do_example_test(name: &str) {
    // TODO(jmmv): This breaks if we run `cargo test --all-targets` because the binary we
    // look for here ends up being the runner for the unit tests of the example, not the
    // example itself.  Should find a better way of doing this so that we can reenable the
    // usage of `--all-targets` in CI.
    let bin_path = get_bin(PathBuf::from("examples").join(name));
    let data_dir = get_src_dir().join("examples");
    check(bin_path, &[], name, data_dir);
}

/// Runs the `name.bas` program and compares its output against golden data in files.
///
/// The data files are expected to be in the `tests` subdirectory and have `name` as their
/// basename.  See the description in `check` for more details.
fn do_golden_script_test(name: &str) {
    let bin_path = get_bin("endbasic");
    let data_dir = get_src_dir().join("tests");
    let bas_path = data_dir.join(name).with_extension("bas");
    check(bin_path, &[bas_path.to_str().unwrap()], name, data_dir);
}

/// Feeds `name.in` to the interpreter and compares its output against golden data in files.
///
/// The data files are expected to be in the `tests` subdirectory and have `name` as their
/// basename.  See the description in `check` for more details.
fn do_golden_interactive_test(name: &str) {
    let bin_path = get_bin("endbasic");
    let data_dir = get_src_dir().join("tests");
    check(bin_path, &[], name, data_dir);
}

#[test]
fn test_example_custom_commands() {
    do_example_test("custom-commands");
}

#[test]
fn test_example_minimal() {
    do_example_test("minimal");
}

#[test]
fn test_golden_control_flow() {
    do_golden_script_test("control-flow");
}

#[test]
fn test_golden_editor() {
    do_golden_interactive_test("editor");
}

#[test]
fn test_golden_exec_error() {
    do_golden_script_test("exec-error");
}

#[test]
fn test_golden_hello() {
    do_golden_script_test("hello");
}

#[test]
fn test_golden_interactive() {
    do_golden_interactive_test("interactive");
}

#[test]
fn test_golden_help() {
    do_golden_interactive_test("help");
}

#[test]
fn test_golden_lexer_error() {
    do_golden_script_test("lexer-error");
}

#[test]
fn test_golden_parser_error() {
    do_golden_script_test("parser-error");
}

#[test]
fn test_golden_script() {
    do_golden_script_test("script");
}

#[test]
fn test_golden_state_sharing() {
    do_golden_interactive_test("state-sharing");
}

#[test]
fn test_golden_types() {
    do_golden_script_test("types");
}

#[test]
fn test_golden_utf8() {
    do_golden_script_test("utf8");
}

#[test]
fn test_golden_yes_no() {
    do_golden_script_test("yes-no");
}

#[test]
fn test_too_many_args() {
    check_program(
        &get_bin("endbasic"),
        &["foo", "bar"],
        1,
        process::Stdio::null(),
        "",
        "endbasic: E: Too many arguments\n",
    );
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
        &["one", "two", "three"],
        1,
        process::Stdio::null(),
        "",
        "custom-name: E: Too many arguments\n",
    );
}
