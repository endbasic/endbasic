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

//! Integration tests for the core language.

mod testutils {
    use async_trait::async_trait;
    use endbasic_core2::*;
    use std::cell::RefCell;
    use std::collections::{HashMap, HashSet};
    use std::env;
    use std::ffi::OsStr;
    use std::fs::{self, File};
    use std::io::{self, BufRead, BufReader, Seek, Write};
    use std::path::{Path, PathBuf};
    use std::process;
    use std::rc::Rc;
    use tempfile::NamedTempFile;

    /// Computes the path to the directory where this test's binary lives.
    fn self_dir() -> PathBuf {
        let self_exe = env::current_exe().expect("Cannot get self's executable path");
        let dir = self_exe.parent().expect("Cannot get self's directory");
        assert!(dir.ends_with("target/debug/deps") || dir.ends_with("target/release/deps"));
        dir.to_owned()
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

    /// Reads the source section of a golden test description file.
    fn read_source(path: &Path) -> io::Result<String> {
        let file = File::open(path).expect("Failed to open golden data file");
        let reader = BufReader::new(file);

        let mut in_source = false;
        let mut started = false;
        let mut source = String::new();
        for line in reader.lines() {
            let line = line?;

            if line == "# Source" {
                in_source = true;
                continue;
            } else if line.starts_with("# ") {
                in_source = false;
                continue;
            }

            if in_source {
                if !started && !line.is_empty() {
                    started = true;
                }

                if started {
                    source.push_str(&line);
                    source.push('\n');
                }
            }
        }

        Ok(source.trim_end().to_owned())
    }

    #[test]
    fn test_read_source() -> io::Result<()> {
        let mut file = NamedTempFile::new()?;
        write!(
            file,
            "junk
# Source

First line

Second line

# Disassembly

foo bar
"
        )?;
        file.flush()?;

        assert_eq!(
            "First line

Second line",
            read_source(file.path())?
        );

        Ok(())
    }

    /// Generates a textual diff of `golden` and `generated`.  The output is meant to be useful for
    /// human consumption when a test fails and is not guaranteed to be in patch format.
    ///
    /// Returns the empty string when the two files match.
    fn diff(golden: &Path, generated: &Path) -> io::Result<String> {
        match process::Command::new("diff")
            .args(&[OsStr::new("-u"), golden.as_os_str(), generated.as_os_str()])
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

        write!(f1, "Line 1\n")?;
        write!(f1, "Line 2\n")?;
        f1.flush()?;
        f1.seek(io::SeekFrom::Start(0))?;

        write!(f2, "Line 1\n")?;
        write!(f2, "Line 2\n")?;
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

        write!(f1, "Line 1\n")?;
        write!(f1, "Line 2\n")?;
        f1.flush()?;
        f1.seek(io::SeekFrom::Start(0))?;

        write!(f2, "Line 1\n")?;
        write!(f2, "Line2\n")?;
        f2.flush()?;
        f2.seek(io::SeekFrom::Start(0))?;

        let diff = diff(f1.path(), f2.path())?;
        assert!(!diff.is_empty());
        Ok(())
    }

    /// A command that prints its arguments to a virtual console.
    struct OutCommand {
        metadata: CallableMetadata,
        output: Rc<RefCell<String>>,
    }

    impl OutCommand {
        pub fn new(output: Rc<RefCell<String>>) -> Rc<Self> {
            Rc::from(Self {
                metadata: CallableMetadataBuilder::new("OUT")
                    .with_syntax(&[(&[], None)])
                    .with_category("Testing")
                    .with_description("Prints arguments")
                    .build(),
                output,
            })
        }
    }

    #[async_trait(?Send)]
    impl Callable for OutCommand {
        fn metadata(&self) -> &CallableMetadata {
            &self.metadata
        }

        async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
            let mut line = String::new();
            let mut argi = 0;
            let mut reg = 0;
            loop {
                let sep = match scope.get_type(reg) {
                    VarArgTag::Immediate(sep, etype @ ExprType::Boolean) => {
                        reg += 1;
                        line.push_str(&format!(
                            "({}, {}, {})",
                            scope.get_boolean(reg),
                            argi,
                            etype.annotation()
                        ));
                        sep
                    }
                    VarArgTag::Immediate(sep, etype @ ExprType::Double) => {
                        reg += 1;
                        line.push_str(&format!(
                            "({}, {}, {})",
                            scope.get_double(reg),
                            argi,
                            etype.annotation()
                        ));
                        sep
                    }
                    VarArgTag::Immediate(sep, etype @ ExprType::Integer) => {
                        reg += 1;
                        line.push_str(&format!(
                            "({}, {}, {})",
                            scope.get_integer(reg),
                            argi,
                            etype.annotation()
                        ));
                        sep
                    }
                    VarArgTag::Immediate(sep, etype @ ExprType::Text) => {
                        reg += 1;
                        line.push_str(&format!(
                            "(\"{}\", {}, {})",
                            scope.get_string(reg),
                            argi,
                            etype.annotation()
                        ));
                        sep
                    }
                    VarArgTag::Missing(sep) => {
                        line.push_str(&format!("({})", argi));
                        sep
                    }
                    VarArgTag::Pointer(_sep) => todo!(),
                };
                argi += 1;
                reg += 1;

                if sep == ArgSep::End {
                    break;
                }
                line.push(' ');
                line.push_str(&sep.to_string());
                line.push(' ');
            }
            let mut output = self.output.borrow_mut();
            output.push_str(&line);
            output.push('\n');
            Ok(())
        }
    }

    /// Given a `golden` test definition, executes its source part and writes the corresponding
    /// `generated` file.  The test is expected to pass when both match, but the caller is responsible
    /// for checking this condition.
    async fn regenerate<W: io::Write>(golden: &Path, generated: &mut W) -> io::Result<()> {
        let source = read_source(&golden)?;

        write!(generated, "# Source\n\n")?;
        write!(generated, "{}\n", source)?;

        let console = Rc::from(RefCell::from(String::new()));
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::default();
        upcalls_by_name.insert(SymbolKey::from("OUT"), OutCommand::new(console.clone()));
        let image = compile(&mut source.as_bytes(), &upcalls_by_name);

        let image = match image {
            Ok(image) => image,
            Err(e) => {
                write!(generated, "\n# Compilation errors\n\n")?;
                write!(generated, "{}\n", e)?;
                return Ok(());
            }
        };

        write!(generated, "\n# Disassembly\n\n")?;
        for line in image.disasm() {
            write!(generated, "{}\n", line)?;
        }

        let mut vm = Vm::new(upcalls_by_name);
        vm.load(image);
        let mut error = None;
        while error.is_none() {
            match vm.exec() {
                StopReason::Eof => break,
                StopReason::Upcall(handle) => {
                    if let Err(e) = handle.invoke().await {
                        error = Some(e.to_string());
                    }
                }
                StopReason::Exception(pos, e) => {
                    error = Some(format!("{}: {}", pos, e));
                }
            }
        }

        if let Some(e) = error {
            write!(generated, "\n# Runtime errors\n\n")?;
            write!(generated, "{}", e)?;
            write!(generated, "\n")?;
        }

        let console = console.borrow();
        if !console.is_empty() {
            write!(generated, "\n# Output\n\n{}", console)?;
        }

        Ok(())
    }

    /// Executes the test described in the `core2/tests/<name>.txt` file.
    pub(super) async fn run_one_test(name: &'static str) -> io::Result<()> {
        let golden = src_path(&format!("core2/tests/{}.txt", name));

        let mut generated = NamedTempFile::new()?;
        regenerate(&golden, &mut generated).await?;
        generated.flush()?;

        let diff = diff(&golden, generated.path())?;
        if env::var("REGEN").as_ref().map(String::as_str) == Ok("true") {
            {
                let mut output = File::create(golden)?;
                generated.as_file_mut().seek(io::SeekFrom::Start(0))?;
                io::copy(&mut generated, &mut output)?;
            }
            panic!("Golden data regenerated; flip REGEN back to false");
        }
        if !diff.is_empty() {
            eprintln!("{}", diff);
            panic!("Test failed; see stderr for details");
        }

        Ok(())
    }

    #[test]
    fn test_all_txt_files_registered() -> io::Result<()> {
        let mut registered: HashSet<String> = HashSet::default();
        {
            let file = File::open(src_path("core2/tests/integration_test.rs"))?;
            let reader = BufReader::new(file);
            for line in reader.lines() {
                let line = line?;

                if line.starts_with("    one_test!(") {
                    let name = &line["    one_test!(".len()..line.len() - 2];
                    registered.insert(format!("{}.txt", name));
                }
            }
        }

        // Sanity-check to ensure that the code right above actually discovered what we expect.
        assert!(registered.contains("test_values.txt"));

        // Make sure that every txt test case definition in the file system is in the list of
        // tests discovered from code scanning.  We don't have to do the opposite because, if
        // this program registers a txt file that doesn't actually exist, the test itself will
        // fail.
        for entry in fs::read_dir(src_path("core2/tests"))? {
            let entry = entry?;

            let Ok(name) = entry.file_name().into_string() else {
                continue;
            };

            if name.starts_with("test_") && name.ends_with(".txt") {
                if !registered.contains(&name) {
                    return Err(io::Error::new(
                        io::ErrorKind::NotFound,
                        format!("Test case {} is not registered", name),
                    ));
                }
            }
        }

        Ok(())
    }
}

mod tests {
    use super::testutils::*;
    use std::io;

    /// Instantiates a test case for the test described in `core2/tests/<name>.txt`.
    macro_rules! one_test {
        ( $name:ident ) => {
            #[tokio::test]
            async fn $name() -> io::Result<()> {
                run_one_test(stringify!($name)).await
            }
        };
    }

    one_test!(test_arithmetic_errors);
    one_test!(test_empty);
    one_test!(test_functions);
    one_test!(test_out_of_locals);
    one_test!(test_string_ops);
    one_test!(test_values);
    one_test!(test_varargs_command);
}
