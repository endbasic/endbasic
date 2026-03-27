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

/// A parsed test case from a golden data file.
#[derive(Debug, Eq, PartialEq)]
struct Test {
    name: String,
    sources: Vec<String>,
}

/// A type describing the golden data of various tests in a file.
type Tests = Vec<Test>;

/// Returns true if the `line` corresponds to a source section.
fn is_source_header(line: &str) -> bool {
    line == "## Source" || line == "## Source (partial)"
}

/// Reads the source sections of a golden test description file.
fn read_sources(path: &Path) -> io::Result<Tests> {
    let file = File::open(path).expect("Failed to open golden data file");
    let reader = BufReader::new(file);

    fn add_test(tests: &mut Tests, name: String, sources: Vec<String>) -> io::Result<()> {
        if sources.is_empty() {
            Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Test case '{}' has no Source section", name),
            ))
        } else {
            tests.push(Test { name, sources });
            Ok(())
        }
    }

    fn finish_source(sources: &mut Vec<String>, source: &mut Option<String>) {
        if let Some(source) = source.take() {
            sources.push(source.trim_end().to_owned());
        }
    }

    #[derive(Clone, Copy, Eq, PartialEq)]
    enum Section {
        Other,
        Source,
    }

    let mut tests = vec![];
    let mut current_test = None;
    let mut current_section = Section::Other;
    let mut sources = vec![];
    let mut source: Option<String> = None;
    for line in reader.lines() {
        let line = line?;

        if let Some(stripped) = line.strip_prefix("# Test: ") {
            finish_source(&mut sources, &mut source);
            if let Some(name) = current_test.take() {
                add_test(&mut tests, name, std::mem::take(&mut sources))?;
            }
            current_test = Some(stripped.to_owned());
            current_section = Section::Other;
            continue;
        } else if line.starts_with("# ") {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Unexpected section header {}", line),
            ));
        } else if is_source_header(&line) {
            current_section = Section::Source;
            continue;
        } else if line.starts_with("## ") {
            finish_source(&mut sources, &mut source);
            current_section = Section::Other;
            continue;
        } else if line == "```basic" {
            if current_section == Section::Source {
                if current_test.is_none() {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "Source section without test header",
                    ));
                }
                source = Some(String::new());
            }
            continue;
        } else if line == "```" {
            finish_source(&mut sources, &mut source);
            continue;
        }

        if let Some(source) = source.as_mut() {
            source.push_str(&line);
            source.push('\n');
        }
    }

    finish_source(&mut sources, &mut source);
    if let Some(name) = current_test {
        add_test(&mut tests, name, std::mem::take(&mut sources))?;
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
        [Test { name: "first".to_owned(), sources: vec!["First line\n\nSecond line".to_owned()] }],
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
            Test {
                name: "first".to_owned(),
                sources: vec!["First line\n\nSecond line".to_owned()],
            },
            Test { name: "second".to_owned(), sources: vec!["The line".to_owned()] },
        ],
        read_sources(file.path())?.as_slice()
    );

    Ok(())
}

#[test]
fn test_read_sources_many_sources_per_test() -> io::Result<()> {
    let mut file = NamedTempFile::new()?;
    write!(
        file,
        "junk
# Test: first

## Source (partial)

```basic
First line
```

## Output

```plain
ignored
```

## Source (partial)

```basic
Second line

Third line
```
"
    )?;
    file.flush()?;

    assert_eq!(
        [Test {
            name: "first".to_owned(),
            sources: vec!["First line".to_owned(), "Second line\n\nThird line".to_owned()],
        }],
        read_sources(file.path())?.as_slice()
    );

    Ok(())
}

/// Collection of section markers for a golden file.
struct Labels {
    source: &'static str,
    disassembly: &'static str,
    compiler_errors: &'static str,
    exit_code: &'static str,
    output: &'static str,
    runtime_errors: &'static str,
}

/// Obtains the section markers to use when writing out the data of `test`.
fn labels_for(test: &Test) -> Labels {
    if test.sources.len() > 1 {
        Labels {
            source: "## Source (partial)",
            disassembly: "## Disassembly (full)",
            compiler_errors: "## Compiler errors (partial)",
            exit_code: "## Exit code (partial)",
            output: "## Output (partial)",
            runtime_errors: "## Runtime errors (partial)",
        }
    } else {
        Labels {
            source: "## Source",
            disassembly: "## Disassembly",
            compiler_errors: "## Compilation errors",
            exit_code: "## Exit code",
            output: "## Output",
            runtime_errors: "## Runtime errors",
        }
    }
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

/// Executes `image` through completion in `vm`, and converts the result into an exit code.
async fn run_image(vm: &mut Vm, image: &Image) -> Result<i32, String> {
    loop {
        match vm.exec(image) {
            StopReason::End(code) => return Ok(code.to_i32()),
            StopReason::Eof => return Ok(0),
            StopReason::Upcall(handle) => {
                if let Err(e) = handle.invoke().await {
                    return Err(e.to_string());
                }
            }
            StopReason::Exception(pos, e) => return Err(format!("{}: {}", pos, e)),
        }
    }
}

/// Given a `golden` test definition, executes its source part and writes the corresponding
/// `generated` file.  The test is expected to pass when both match, but the caller is responsible
/// for checking this condition.
#[allow(clippy::write_with_newline)]
async fn regenerate<W: Write>(golden: &Path, generated: &mut W) -> io::Result<()> {
    let tests = read_sources(golden)?;

    let mut first = true;
    for test in tests {
        if !first {
            write!(generated, "\n")?;
        }
        write!(generated, "# Test: {}\n", test.name)?;
        first = false;
        let labels = labels_for(&test);

        let console = Rc::from(RefCell::from(String::new()));
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::default();
        callables::register_all(&mut upcalls_by_name, console.clone());
        let mut compiler = Compiler::new(&upcalls_by_name, &[]).expect("Cannot fail");
        let mut image = Image::default();
        let mut vm = Vm::new(upcalls_by_name.clone());

        for source in test.sources {
            write!(generated, "\n{}\n\n", labels.source)?;
            write!(generated, "```basic\n")?;
            if !source.is_empty() {
                write!(generated, "{}\n", source)?;
            }
            write!(generated, "```\n")?;

            if let Err(e) = compiler.compile_more(&mut image, &mut source.as_bytes()) {
                write!(generated, "\n{}\n\n", labels.compiler_errors)?;
                write!(generated, "```plain\n")?;
                write!(generated, "{}\n", e)?;
                write!(generated, "```\n")?;
                continue;
            }

            write!(generated, "\n{}\n\n", labels.disassembly)?;
            write!(generated, "```asm\n")?;
            for line in image.disasm() {
                write!(generated, "{}\n", line)?;
            }
            write!(generated, "```\n")?;

            console.borrow_mut().clear();
            match run_image(&mut vm, &image).await {
                Ok(0) => (),
                Ok(i) => {
                    write!(generated, "\n{}\n\n", labels.exit_code)?;
                    write!(generated, "```plain\n")?;
                    write!(generated, "{}\n", i)?;
                    write!(generated, "```\n")?;
                }
                Err(e) => {
                    write!(generated, "\n{}\n\n", labels.runtime_errors)?;
                    write!(generated, "```plain\n")?;
                    write!(generated, "{}\n", e)?;
                    write!(generated, "```\n")?;
                }
            }

            let console = console.borrow();
            if !console.is_empty() {
                write!(generated, "\n{}\n\n", labels.output)?;
                write!(generated, "```plain\n")?;
                write!(generated, "{}", console)?;
                write!(generated, "```\n")?;
            }
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
