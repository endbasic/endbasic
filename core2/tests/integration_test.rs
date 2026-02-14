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

use std::fs::{self, File};
use std::io::{self, BufRead, BufReader};

mod testutils;
use testutils::*;

/// Instantiates a test case for the test described in `core2/tests/<name>.md`.
macro_rules! one_test {
    ( $name:ident ) => {
        #[tokio::test]
        async fn $name() -> io::Result<()> {
            run_one_test(stringify!($name)).await
        }
    };
}

one_test!(test_arithmetic);
one_test!(test_assignments);
one_test!(test_empty);
one_test!(test_end);
one_test!(test_functions);
one_test!(test_globals);
one_test!(test_gosub);
one_test!(test_goto);
one_test!(test_out_of_registers);
one_test!(test_strings);
one_test!(test_subs);
one_test!(test_types);
one_test!(test_varargs);

#[test]
fn test_all_md_files_registered() -> io::Result<()> {
    let mut registered = vec![];
    {
        let file = File::open(src_path("core2/tests/integration_test.rs"))?;
        let reader = BufReader::new(file);
        for line in reader.lines() {
            let line = line?;

            if line.starts_with("one_test!(") {
                let name = &line["one_test!(".len()..line.len() - 2];
                registered.push(format!("{}.md", name));
            }
        }
    }

    // Sanity-check to ensure that the code right above actually discovered what we expect.
    assert!(registered.iter().any(|s| s == "test_types.md"));

    // Make sure that every md test case definition in the file system is in the list of
    // tests discovered from code scanning.  We don't have to do the opposite because, if
    // this program registers a md file that doesn't actually exist, the test itself will
    // fail.
    let mut found = vec![];
    for entry in fs::read_dir(src_path("core2/tests"))? {
        let entry = entry?;

        let Ok(name) = entry.file_name().into_string() else {
            continue;
        };

        #[allow(clippy::collapsible_if)]
        if name.starts_with("test_") && name.ends_with(".md") {
            found.push(name);
        }
    }

    // We want the list of tests below to be sorted, so sort the list of found tests and
    // use that when comparing against the list of registered tests.
    found.sort();

    assert_eq!(registered, found);

    Ok(())
}
