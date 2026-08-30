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
use predicates::prelude::{Predicate, predicate};
use std::env;
use std::fs::{self, File};
use std::io::Read;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};

/// Matches a formatted date.
const DATE_RE: &str = "[0-9]{4}-[0-9]{2}-[0-9]{2} [0-2][0-9]:[0-5][0-9]";

/// Matches a `file://` URI.
const FILE_URI_RE: &str = "file://[^ \n\"]+";

/// Placeholder for the source directory in test output.
const SOURCE_DIR: &str = "/PATH/TO/SRCDIR";

/// Matches a version number.
const VERSION_RE: &str = "[0-9]+\\.[0-9]+\\.[0-9]+";

/// Matches a year range.
const YEAR_RANGE_RE: &str = "[0-9]{4}-[0-9]{4}";

/// Configures a command with a deterministic terminal environment.
fn configure_cmd(mut cmd: Command) -> Command {
    cmd.env("LINES", "24").env("COLUMNS", "80").env_remove("NO_COLOR");
    cmd
}

/// Creates a command to run EndBASIC with a deterministic terminal environment.
fn endbasic_cmd() -> Command {
    configure_cmd(Command::cargo_bin("endbasic").unwrap())
}

/// Computes the path to the source file `name`.
fn src_path(name: &str) -> PathBuf {
    let dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).parent().expect("Failed to get parent directory");

    // Sanity-check that we landed in the right location.
    assert!(dir.join("Cargo.lock").exists());

    dir.join(name)
}

/// Same as `src_path` but returns a string reference for the few places where we need this.
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
    let golden = if cfg!(target_os = "windows") { raw.replace("\r\n", "\n") } else { raw };

    // This is the opposite of apply_mocks and ensures we don't leak actual values into the golden
    // files by mistake.
    let version_re = regex::Regex::new(VERSION_RE).unwrap();
    assert!(
        !version_re.is_match(&golden),
        "Golden file {} contains a version number",
        path.display()
    );
    let date_re = regex::Regex::new(DATE_RE).unwrap();
    assert!(!date_re.is_match(&golden), "Golden file {} contains a date", path.display());
    let year_range_re = regex::Regex::new(YEAR_RANGE_RE).unwrap();
    assert!(
        !year_range_re.is_match(&golden),
        "Golden file {} contains a year range",
        path.display()
    );

    golden
}

/// Replaces the parts of the output that can change due to the environment with placeholders.
fn apply_mocks(input: String) -> String {
    let input = input.replace(env!("CARGO_MANIFEST_DIR"), SOURCE_DIR);

    let version_re = regex::Regex::new(VERSION_RE).unwrap();
    let input = version_re.replace_all(&input, "X.Y.Z").into_owned();

    let date_re = regex::Regex::new(DATE_RE).unwrap();
    let input = date_re.replace_all(&input, "YYYY-MM-DD HH:MM").into_owned();

    let year_range_re = regex::Regex::new(YEAR_RANGE_RE).unwrap();
    let input = year_range_re.replace_all(&input, "YYYY-YYYY").into_owned();

    let file_uri_re = regex::Regex::new(FILE_URI_RE).unwrap();
    file_uri_re.replace_all(&input, "file:///PATH/TO/TMPDIR").into()
}

/// Compares a sanitized output stream against a golden file.
fn golden(name: &str) -> impl Predicate<[u8]> {
    let regen = matches!(env::var("REGEN").as_deref(), Ok("1") | Ok("true") | Ok("yes"));
    let path = src_path(name);
    let expected = read_golden(name);
    predicate::function(move |actual: &[u8]| {
        let actual =
            apply_mocks(String::from_utf8(actual.to_owned()).expect("Output is not valid UTF-8"));
        if expected == actual {
            return true;
        }
        if regen {
            fs::write(&path, actual).expect("Failed to rewrite golden output file");
            panic!("Golden data regenerated; flip REGEN back to false");
        }
        false
    })
    .fn_name("matches golden output")
}

#[test]
fn test_cli_autoexec_is_ignored() {
    let dir = tempfile::tempdir().unwrap();
    fs::copy(src_path("cli/tests/repl/autoexec.bas"), dir.path().join("AUTOEXEC.BAS")).unwrap();
    endbasic_cmd()
        .args([
            &format!("--local-drive=file://{}", dir.path().to_str().unwrap()),
            &src_str("cli/tests/cli/interactive.bas"),
        ])
        .assert()
        .code(1)
        .stdout("")
        .stderr(golden("cli/tests/cli/interactive.err"));
}

#[cfg(unix)]
#[test]
fn test_lang_shebang_exec() {
    let dir = tempfile::tempdir().unwrap();
    let script = dir.path().join("shebang-exec");

    let mut template = read_golden("cli/tests/cli/shebang-exec.bas");
    let interpreter = assert_cmd::cargo::cargo_bin("endbasic");
    template = template.replace(
        "__ENDBASIC__",
        interpreter.to_str().expect("Interpreter path must be valid UTF-8"),
    );
    fs::write(&script, template).unwrap();

    let mut perms = fs::metadata(&script).unwrap().permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&script, perms).unwrap();

    configure_cmd(Command::new(script))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/cli/shebang-exec.out"))
        .stderr("");
}

#[test]
fn test_cli_propline_errors() {
    endbasic_cmd()
        .args([&src_str("cli/tests/cli/propline-bad-comment.bas")])
        .assert()
        .code(1)
        .stdout("")
        .stderr(golden("cli/tests/cli/propline-bad-comment.err"));
}

#[test]
fn test_cli_missing_program() {
    let stderr = if cfg!(target_os = "windows") {
        "endbasic: Cannot extract properties from program file missing.bas: The system cannot find the file specified. (os error 2)\n"
    } else {
        "endbasic: Cannot extract properties from program file missing.bas: No such file or directory (os error 2)\n"
    };

    endbasic_cmd().args(["missing.bas"]).assert().code(1).stdout("").stderr(stderr);
}

#[test]
fn test_cli_propline_sets_default_console() {
    endbasic_cmd()
        .args([&src_str("cli/tests/cli/propline-bad-console.bas")])
        .assert()
        .code(1)
        .stdout("")
        .stderr(golden("cli/tests/cli/propline-bad-console.err"));
}

#[test]
fn test_cli_flag_overrides_propline_console() {
    endbasic_cmd()
        .args(["--console=text", &src_str("cli/tests/cli/propline-override-console.bas")])
        .assert()
        .code(0)
        .stdout(golden("cli/tests/cli/propline-override-console.out"))
        .stderr("");
}

#[test]
fn test_cli_help() {
    fn check_with_args(args: &[&str]) {
        let mut src = String::from("cli/tests/cli/help.out");
        if cfg!(feature = "rpi") {
            src.push_str(".rpi");
        }
        if cfg!(feature = "sdl") {
            src.push_str(".sdl");
        }
        endbasic_cmd().args(args).assert().code(0).stdout(golden(&src)).stderr("");
    }
    check_with_args(&["-h"]);
    check_with_args(&["--help"]);
    check_with_args(&["--version", "--help"]);
    check_with_args(&["the", "--help", "flag always wins"]);
}

#[test]
fn test_cli_interactive() {
    endbasic_cmd()
        .args(["--local-drive=memory://", &src_str("cli/tests/cli/interactive.bas")])
        .assert()
        .code(1)
        .stdout("")
        .stderr(golden("cli/tests/cli/interactive.err"));

    endbasic_cmd()
        .args(["--local-drive=memory://", "-i", &src_str("cli/tests/cli/interactive.bas")])
        .assert()
        .code(0)
        .stdout(golden("cli/tests/cli/interactive.out"))
        .stderr("");

    endbasic_cmd()
        .args([
            "--local-drive=memory://",
            "--interactive",
            &src_str("cli/tests/cli/interactive.bas"),
        ])
        .assert()
        .code(0)
        .stdout(golden("cli/tests/cli/interactive.out"))
        .stderr("");
}

#[test]
#[ignore = "Requires environment configuration and is expensive"]
fn test_cli_run_from_cloud() {
    let service_url = env::var("SERVICE_URL").expect("Expected env config not found");

    endbasic_cmd()
        .args(["--service-url", &service_url, "--interactive", "cloud://endbasic/welcome.bas"])
        .assert()
        .code(0)
        .stdout(golden("cli/tests/cli/run-from-cloud.out"))
        .stderr("");
}

// TODO(jmmv): This test fails almost always on Linux CI builds with `Text file busy` when
// attempting to run the copied binary.  I've also gotten it to occasionally fail on a local Linux
// installation in the same way, but that's much harder to trigger.  Investigate what's going on.
#[cfg(not(target_os = "linux"))]
#[test]
fn test_cli_program_name_uses_arg0() {
    let dir = tempfile::tempdir().unwrap();
    let original = assert_cmd::cargo::cargo_bin("endbasic");
    let custom = dir.path().join("custom-name").with_extension(env::consts::EXE_EXTENSION);
    fs::copy(&original, &custom).unwrap();
    configure_cmd(Command::new(&custom))
        .args(["one", "two", "three"])
        .assert()
        .code(2)
        .stdout("")
        .stderr(
            "Usage error: Too many arguments\nType `custom-name --help` for more information\n"
                .to_owned(),
        );
}

#[test]
fn test_cli_too_many_args() {
    endbasic_cmd().args(["foo", "bar"]).assert().code(2).stdout("").stderr(
        "Usage error: Too many arguments\nType `endbasic --help` for more information\n".to_owned(),
    );
}

#[test]
fn test_cli_unknown_option() {
    endbasic_cmd().args(["-Z", "some-file"]).assert().code(2).stdout("").stderr(
        "Usage error: Unrecognized option: 'Z'\nType `endbasic --help` for more information\n"
            .to_owned(),
    );
}

#[test]
fn test_cli_version() {
    fn check_with_args(args: &[&str]) {
        endbasic_cmd()
            .args(args)
            .assert()
            .code(0)
            .stdout(golden("cli/tests/cli/version.out"))
            .stderr("");
    }
    check_with_args(&["--version"]);
    check_with_args(&["the", "--version", "flag wins over arguments"]);
}

#[test]
fn test_example_alarm() {
    endbasic_cmd()
        .args(["--local-drive=memory://", "--interactive"])
        .write_stdin(read_golden("cli/tests/examples/alarm.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/examples/alarm.out"))
        .stderr("");
}

#[test]
fn test_example_bounce() {
    endbasic_cmd()
        .args(["--local-drive=memory://", "--interactive"])
        .write_stdin(read_golden("cli/tests/examples/bounce.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/examples/bounce.out"))
        .stderr("");
}

#[test]
fn test_example_fibonacci() {
    endbasic_cmd()
        .args(["--local-drive=memory://", "--interactive"])
        .write_stdin(read_golden("cli/tests/examples/fibonacci.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/examples/fibonacci.out"))
        .stderr("");
}

#[test]
fn test_example_gpio() {
    endbasic_cmd()
        .args(["--gpio-pins=mock", "--local-drive=memory://", "--interactive"])
        .write_stdin(read_golden("cli/tests/examples/gpio.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/examples/gpio.out"))
        .stderr("");
}

#[test]
fn test_example_guess() {
    endbasic_cmd()
        .args(["--local-drive=memory://", "--interactive"])
        .write_stdin(read_golden("cli/tests/examples/guess.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/examples/guess.out"))
        .stderr("");
}

#[test]
fn test_example_hello() {
    endbasic_cmd()
        .args(["--local-drive=memory://", "--interactive"])
        .write_stdin(read_golden("cli/tests/examples/hello.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/examples/hello.out"))
        .stderr("");
}

#[test]
fn test_example_palette() {
    endbasic_cmd()
        .args(["--local-drive=memory://", "--interactive"])
        .write_stdin(read_golden("cli/tests/examples/palette.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/examples/palette.out"))
        .stderr("");
}

#[test]
fn test_example_tour() {
    endbasic_cmd()
        .args(["--local-drive=memory://", "--interactive"])
        .write_stdin(read_golden("cli/tests/examples/tour.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/examples/tour.out"))
        .stderr("");
}

#[test]
fn test_lang_bitwise() {
    endbasic_cmd()
        .args(["--local-drive=memory://", &src_str("cli/tests/lang/bitwise.bas")])
        .assert()
        .code(0)
        .stdout(golden("cli/tests/lang/bitwise.out"))
        .stderr("");
}

#[test]
fn test_lang_control_flow() {
    endbasic_cmd()
        .args(["--local-drive=memory://", &src_str("cli/tests/lang/control-flow.bas")])
        .assert()
        .code(0)
        .stdout(golden("cli/tests/lang/control-flow.out"))
        .stderr("");
}

#[test]
fn test_lang_control_flow_errors() {
    endbasic_cmd()
        .args(["--local-drive=memory://"])
        .write_stdin(read_golden("cli/tests/lang/control-flow-errors.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/lang/control-flow-errors.out"))
        .stderr("");
}

#[test]
fn test_lang_exec_error() {
    endbasic_cmd()
        .args(["--local-drive=memory://", &src_str("cli/tests/lang/exec-error.bas")])
        .assert()
        .code(1)
        .stdout(golden("cli/tests/lang/exec-error.out"))
        .stderr(golden("cli/tests/lang/exec-error.err"));
}

#[test]
fn test_lang_exprs() {
    endbasic_cmd()
        .args(["--local-drive=memory://", &src_str("cli/tests/lang/exprs.bas")])
        .assert()
        .code(0)
        .stdout(golden("cli/tests/lang/exprs.out"))
        .stderr("");
}

#[test]
fn test_lang_exprs_errors() {
    endbasic_cmd()
        .args(["--local-drive=memory://"])
        .write_stdin(read_golden("cli/tests/lang/exprs-errors.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/lang/exprs-errors.out"))
        .stderr("");
}

#[test]
fn test_lang_functions() {
    endbasic_cmd()
        .args(["--local-drive=memory://", &src_str("cli/tests/lang/functions.bas")])
        .assert()
        .code(0)
        .stdout(golden("cli/tests/lang/functions.out"))
        .stderr("");
}

#[test]
fn test_lang_hello() {
    endbasic_cmd()
        .args(["--local-drive=memory://", &src_str("cli/tests/lang/hello.bas")])
        .assert()
        .code(0)
        .stdout(golden("cli/tests/lang/hello.out"))
        .stderr("");
}

#[test]
fn test_lang_lexer_error() {
    endbasic_cmd()
        .args(["--local-drive=memory://", &src_str("cli/tests/lang/lexer-error.bas")])
        .assert()
        .code(1)
        .stdout("")
        .stderr(golden("cli/tests/lang/lexer-error.err"));
}

#[test]
fn test_lang_matrix() {
    endbasic_cmd()
        .args(["--local-drive=memory://", &src_str("cli/tests/lang/matrix.bas")])
        .assert()
        .code(0)
        .stdout(golden("cli/tests/lang/matrix.out"))
        .stderr("");
}

#[test]
fn test_lang_operators() {
    endbasic_cmd()
        .args(["--local-drive=memory://"])
        .write_stdin(read_golden("cli/tests/lang/operators.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/lang/operators.out"))
        .stderr("");
}

#[test]
fn test_lang_parser_error() {
    endbasic_cmd()
        .args(["--local-drive=memory://", &src_str("cli/tests/lang/parser-error.bas")])
        .assert()
        .code(1)
        .stdout("")
        .stderr(golden("cli/tests/lang/parser-error.err"));
}

#[test]
fn test_lang_types() {
    endbasic_cmd()
        .args(["--local-drive=memory://"])
        .write_stdin(read_golden("cli/tests/lang/types.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/lang/types.out"))
        .stderr("");
}

#[test]
fn test_lang_utf8() {
    endbasic_cmd()
        .args(["--local-drive=memory://", &src_str("cli/tests/lang/utf8.bas")])
        .write_stdin(read_golden("cli/tests/lang/utf8.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/lang/utf8.out"))
        .stderr("");
}

#[test]
fn test_lang_yes_no() {
    endbasic_cmd()
        .args(["--local-drive=memory://", &src_str("cli/tests/lang/yes-no.bas")])
        .write_stdin(read_golden("cli/tests/lang/yes-no.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/lang/yes-no.out"))
        .stderr("");
}

#[test]
fn test_repl_autoexec() {
    let dir = tempfile::tempdir().unwrap();
    fs::copy(src_path("cli/tests/repl/autoexec.bas"), dir.path().join("AUTOEXEC.BAS")).unwrap();
    endbasic_cmd()
        .args([&format!("--local-drive=file://{}", dir.path().to_str().unwrap())])
        .write_stdin(read_golden("cli/tests/repl/hello.bas"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/repl/autoexec.out"))
        .stderr("");
}

#[test]
fn test_repl_colors() {
    endbasic_cmd()
        .args(["--local-drive=memory://"])
        .write_stdin(read_golden("cli/tests/repl/colors.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/repl/colors.out"))
        .stderr("");
}

#[test]
fn test_repl_console() {
    endbasic_cmd()
        .args(["--local-drive=memory://", &src_str("cli/tests/repl/console.bas")])
        .assert()
        .code(0)
        .stdout(golden("cli/tests/repl/console.out"))
        .stderr("");
}

#[test]
fn test_repl_dir() {
    endbasic_cmd()
        .args(["--local-drive=memory://"])
        .write_stdin(read_golden("cli/tests/repl/dir.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/repl/dir.out"))
        .stderr("");
}

#[test]
fn test_repl_editor() {
    endbasic_cmd()
        .args(["--local-drive=memory://"])
        .write_stdin(read_golden("cli/tests/repl/editor.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/repl/editor.out"))
        .stderr("");
}

#[test]
fn test_repl_exit_nonzero() {
    endbasic_cmd()
        .args(["--local-drive=memory://", &src_str("cli/tests/repl/exit-nonzero.bas")])
        .assert()
        .code(78)
        .stdout("")
        .stderr("");

    endbasic_cmd()
        .args(["--local-drive=memory://"])
        .write_stdin(read_golden("cli/tests/repl/exit-nonzero.bas"))
        .assert()
        .code(78)
        .stdout(golden("cli/tests/repl/exit.out"))
        .stderr("");
}

#[test]
fn test_repl_exit_saved() {
    endbasic_cmd()
        .args(["--local-drive=memory://"])
        .write_stdin(read_golden("cli/tests/repl/exit-saved.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/repl/exit-saved.out"))
        .stderr("");
}

#[test]
fn test_repl_exit_unsaved() {
    endbasic_cmd()
        .args(["--local-drive=memory://"])
        .write_stdin(read_golden("cli/tests/repl/exit-unsaved.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/repl/exit-unsaved.out"))
        .stderr("");
}

#[test]
fn test_repl_exit_zero() {
    endbasic_cmd()
        .args(["--local-drive=memory://", &src_str("cli/tests/repl/exit-zero.bas")])
        .assert()
        .code(0)
        .stdout("")
        .stderr("");

    endbasic_cmd()
        .args(["--local-drive=memory://"])
        .write_stdin(read_golden("cli/tests/repl/exit-zero.bas"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/repl/exit.out"))
        .stderr("");
}

#[test]
fn test_repl_help() {
    endbasic_cmd()
        .args(["--local-drive=memory://", "--interactive", &src_str("cli/tests/repl/help.bas")])
        .assert()
        .code(0)
        .stdout(golden("cli/tests/repl/help.out"))
        .stderr("");
}

#[test]
fn test_repl_interactive() {
    endbasic_cmd()
        .args(["--local-drive=memory://"])
        .write_stdin(read_golden("cli/tests/repl/interactive.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/repl/interactive.out"))
        .stderr("");
}

#[test]
fn test_repl_load_save() {
    let dir = tempfile::tempdir().unwrap();
    fs::copy(src_path("cli/tests/repl/hello.bas"), dir.path().join("hello.bas")).unwrap();
    assert!(!dir.path().join("hello2.bas").exists());
    endbasic_cmd()
        .args([&format!("--local-drive=file://{}", dir.path().to_str().unwrap())])
        .write_stdin(read_golden("cli/tests/repl/load-save.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/repl/load-save.out"))
        .stderr("");
    assert!(dir.path().join("hello2.bas").exists());
}

#[test]
fn test_repl_state_sharing() {
    endbasic_cmd()
        .args(["--local-drive=memory://"])
        .write_stdin(read_golden("cli/tests/repl/state-sharing.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/repl/state-sharing.out"))
        .stderr("");
}

#[test]
fn test_repl_storage() {
    let dir = tempfile::tempdir().unwrap();
    let dir = dir.path().join("create-me");
    endbasic_cmd()
        .args([&format!("--local-drive=file://{}", dir.to_str().unwrap())])
        .write_stdin(read_golden("cli/tests/repl/storage.in"))
        .assert()
        .code(0)
        .stdout(golden("cli/tests/repl/storage.out"))
        .stderr("");
    assert!(dir.exists());
}
