// EndBASIC
// Copyright 2026 Julio Merino
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

//! Support functions to implement the integration tests.

use endbasic_core2::*;
use std::cell::RefCell;
use std::collections::HashMap;
use std::env;
use std::ffi::OsStr;
use std::fs::{self, File};
use std::io::{self, BufRead, BufReader, Seek, Write};
use std::path::{Path, PathBuf};
use std::process;
use std::rc::Rc;
use tempfile::NamedTempFile;

mod callables;

/// Computes the path to the directory where this test's binary lives.
fn self_dir() -> PathBuf {
    let self_exe = env::current_exe().expect("Cannot get self's executable path");
    let dir = self_exe.parent().expect("Cannot get self's directory");
    assert!(dir.ends_with("target/debug/deps") || dir.ends_with("target/release/deps"));
    dir.to_owned()
}

/// Computes the path to the source file `name`.
pub(super) fn src_path(name: &str) -> PathBuf {
    let test_dir = self_dir();
    let debug_or_release_dir = test_dir.parent().expect("Failed to get parent directory");
    let target_dir = debug_or_release_dir.parent().expect("Failed to get parent directory");
    let dir = target_dir.parent().expect("Failed to get parent directory");

    // Sanity-check that we landed in the right location.
    assert!(dir.join("Cargo.lock").exists());

    dir.join(name)
}

/// A type describing the golden data of various tests in a file.
///
/// The first string is the test's name and the second is the input source code.
type Tests = Vec<(String, String)>;

/// Reads the source sections of a golden test description file.
fn read_sources(path: &Path) -> io::Result<Tests> {
    let file = File::open(path).expect("Failed to open golden data file");
    let reader = BufReader::new(file);

    fn add_test(tests: &mut Tests, name: String, source: Option<String>) -> io::Result<()> {
        match source {
            Some(source) => {
                tests.push((name, source.trim_end().to_owned()));
                Ok(())
            }
            None => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Test case '{}' has no Source section", name),
            )),
        }
    }

    let mut tests = vec![];
    let mut current_test = None;
    let mut source: Option<String> = None;
    for line in reader.lines() {
        let line = line?;

        if let Some(stripped) = line.strip_prefix("# Test: ") {
            if let Some(name) = current_test.take() {
                add_test(&mut tests, name, source.take())?;
            }
            current_test = Some(stripped.to_owned());
            source = None;
            continue;
        } else if line.starts_with("# ") {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Unexpected section header {}", line),
            ));
        } else if line == "```basic" {
            if current_test.is_none() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "Source section without test header",
                ));
            }
            source = Some(String::new());
            continue;
        } else if line == "```" {
            if let Some(name) = current_test.take() {
                add_test(&mut tests, name, source.take())?;
            }
            source = None;
            continue;
        }

        if let Some(source) = source.as_mut() {
            source.push_str(&line);
            source.push('\n');
        }
    }

    if let Some(name) = current_test {
        add_test(&mut tests, name, source.take())?;
    }

    if tests.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("Test file '{}' has no tests", path.display()),
        ));
    }

    Ok(tests)
}

#[test]
fn test_read_sources_one() -> io::Result<()> {
    let mut file = NamedTempFile::new()?;
    write!(
        file,
        "junk
# Test: first

## Source

```basic
First line

Second line
```

## Disassembly

```asm
foo bar
```
"
    )?;
    file.flush()?;

    assert_eq!(
        [("first".to_owned(), "First line\n\nSecond line".to_owned())],
        read_sources(file.path())?.as_slice()
    );

    Ok(())
}

#[test]
fn test_read_sources_two() -> io::Result<()> {
    let mut file = NamedTempFile::new()?;
    write!(
        file,
        "junk
# Test: first

## Source

```basic
First line

Second line
```

## Disassembly

```asm
foo bar
```

# Test: second

## Source

```basic
The line
```
"
    )?;
    file.flush()?;

    assert_eq!(
        [
            ("first".to_owned(), "First line\n\nSecond line".to_owned()),
            ("second".to_owned(), "The line".to_owned()),
        ],
        read_sources(file.path())?.as_slice()
    );

    Ok(())
}

/// Generates a textual diff of `golden` and `generated`.  The output is meant to be useful for
/// human consumption when a test fails and is not guaranteed to be in patch format.
///
/// Returns the empty string when the two files match.
fn diff(golden: &Path, generated: &Path) -> io::Result<String> {
    match process::Command::new("diff")
        .args([OsStr::new("-u"), golden.as_os_str(), generated.as_os_str()])
        .output()
    {
        Ok(result) => {
            let Some(code) = result.status.code() else {
                return Err(io::Error::other("diff crashed"));
            };
            let Ok(stdout) = String::from_utf8(result.stdout) else {
                return Err(io::Error::other("diff printed non-UTF8 content to stdout"));
            };
            let Ok(stderr) = String::from_utf8(result.stderr) else {
                return Err(io::Error::other("diff printed non-UTF8 content to stderr"));
            };

            let mut diff = stdout;
            diff.push_str(&stderr);
            if code == 0 && !diff.is_empty() {
                return Err(io::Error::other("diff succeeded but output is not empty"));
            } else if code != 0 && diff.is_empty() {
                return Err(io::Error::other("diff succeeded but output is empty"));
            }

            Ok(diff)
        }

        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            let left = fs::read_to_string(golden)?;
            let right = fs::read_to_string(generated)?;

            let mut diff = String::new();
            if left != right {
                diff.push_str("Golden\n");
                diff.push_str("======\n");
                diff.push_str(&left);
                diff.push_str("\n\nActual\n");
                diff.push_str("======\n");
                diff.push_str(&right);
            }
            Ok(diff)
        }

        Err(e) => Err(e),
    }
}

#[test]
fn test_diff_same() -> io::Result<()> {
    let mut f1 = NamedTempFile::new()?;
    let mut f2 = NamedTempFile::new()?;

    writeln!(f1, "Line 1")?;
    writeln!(f1, "Line 2")?;
    f1.flush()?;
    f1.seek(io::SeekFrom::Start(0))?;

    writeln!(f2, "Line 1")?;
    writeln!(f2, "Line 2")?;
    f2.flush()?;
    f2.seek(io::SeekFrom::Start(0))?;

    let diff = diff(f1.path(), f2.path())?;
    assert!(diff.is_empty());
    Ok(())
}

#[test]
fn test_diff_different() -> io::Result<()> {
    let mut f1 = NamedTempFile::new()?;
    let mut f2 = NamedTempFile::new()?;

    writeln!(f1, "Line 1")?;
    writeln!(f1, "Line 2")?;
    f1.flush()?;
    f1.seek(io::SeekFrom::Start(0))?;

    writeln!(f2, "Line 1")?;
    writeln!(f2, "Line2")?;
    f2.flush()?;
    f2.seek(io::SeekFrom::Start(0))?;

    let diff = diff(f1.path(), f2.path())?;
    assert!(!diff.is_empty());
    Ok(())
}

/// Given a `golden` test definition, executes its source part and writes the corresponding
/// `generated` file.  The test is expected to pass when both match, but the caller is responsible
/// for checking this condition.
#[allow(clippy::write_with_newline)]
async fn regenerate<W: Write>(golden: &Path, generated: &mut W) -> io::Result<()> {
    let tests = read_sources(golden)?;

    let mut first = true;
    for (name, source) in tests {
        if !first {
            write!(generated, "\n")?;
        }
        write!(generated, "# Test: {}\n\n", name)?;
        first = false;

        write!(generated, "## Source\n\n")?;
        write!(generated, "```basic\n")?;
        if !source.is_empty() {
            write!(generated, "{}\n", source)?;
        }
        write!(generated, "```\n")?;

        let console = Rc::from(RefCell::from(String::new()));
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::default();
        callables::register_all(&mut upcalls_by_name, console.clone());
        let image = { compile(&mut source.as_bytes(), &only_metadata(&upcalls_by_name)) };

        let image = match image {
            Ok(image) => image,
            Err(e) => {
                write!(generated, "\n## Compilation errors\n\n")?;
                write!(generated, "```plain\n")?;
                write!(generated, "{}\n", e)?;
                write!(generated, "```\n")?;
                continue;
            }
        };

        write!(generated, "\n## Disassembly\n\n")?;
        write!(generated, "```asm\n")?;
        for line in image.disasm() {
            write!(generated, "{}\n", line)?;
        }
        write!(generated, "```\n")?;

        let mut vm = Vm::new(upcalls_by_name);
        vm.load(image);
        let mut stop: Option<Result<i32, String>> = None;
        while stop.is_none() {
            match vm.exec() {
                StopReason::End(code) => stop = Some(Ok(code)),
                StopReason::Upcall(handle) => {
                    if let Err(e) = handle.invoke().await {
                        stop = Some(Err(e.to_string()));
                    }
                }
                StopReason::Exception(pos, e) => {
                    stop = Some(Err(format!("{}: {}", pos, e)));
                }
            }
        }

        match stop.expect("The loop can only exit when this is set") {
            Ok(0) => {
                // Keep quiet in the common case.
            }
            Ok(i) => {
                write!(generated, "\n## Exit code\n\n")?;
                write!(generated, "```plain\n")?;
                write!(generated, "{}\n", i)?;
                write!(generated, "```\n")?;
            }
            Err(e) => {
                write!(generated, "\n## Runtime errors\n\n")?;
                write!(generated, "```plain\n")?;
                write!(generated, "{}\n", e)?;
                write!(generated, "```\n")?;
            }
        }

        let console = console.borrow();
        if !console.is_empty() {
            write!(generated, "\n## Output\n\n")?;
            write!(generated, "```plain\n")?;
            write!(generated, "{}", console)?;
            write!(generated, "```\n")?;
        }
    }

    Ok(())
}

/// Executes the test described in the `core2/tests/<name>.md` file.
pub(super) async fn run_one_test(name: &'static str) -> io::Result<()> {
    let golden = src_path(&format!("core2/tests/{}.md", name));

    let mut generated = NamedTempFile::new()?;
    regenerate(&golden, &mut generated).await?;
    generated.flush()?;

    let diff = diff(&golden, generated.path())?;
    if !diff.is_empty() {
        if env::var("REGEN").as_ref().map(String::as_str) == Ok("true") {
            {
                let mut output = File::create(golden)?;
                generated.as_file_mut().seek(io::SeekFrom::Start(0))?;
                io::copy(&mut generated, &mut output)?;
            }
            panic!("Golden data regenerated; flip REGEN back to false");
        } else {
            eprintln!("{}", diff);
            panic!("Test failed; see stderr for details");
        }
    }

    Ok(())
}
