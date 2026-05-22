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

//! Integration tests for the core language.

use std::fs::{self, File};
use std::io::{self, BufRead, BufReader};

mod testutils;
use testutils::*;

/// Instantiates a test case for the test described in `core/tests/<name>.md`.
macro_rules! one_test {
    ( $name:ident ) => {
        #[tokio::test]
        async fn $name() -> io::Result<()> {
            run_one_test(stringify!($name)).await
        }
    };
    ( $name:ident, $ignore:expr ) => {
        #[tokio::test]
        #[ignore = $ignore]
        async fn $name() -> io::Result<()> {
            run_one_test(stringify!($name)).await
        }
    };
}

one_test!(test_args);
one_test!(test_arithmetic_add);
one_test!(test_arithmetic_div);
one_test!(test_arithmetic_mod);
one_test!(test_arithmetic_mul);
one_test!(test_arithmetic_neg);
one_test!(test_arithmetic_pow);
one_test!(test_arithmetic_sub);
one_test!(test_arrays);
one_test!(test_assignments);
one_test!(test_bitwise_and);
one_test!(test_bitwise_not);
one_test!(test_bitwise_or);
one_test!(test_bitwise_shl);
one_test!(test_bitwise_shr);
one_test!(test_bitwise_xor);
one_test!(test_call_errors);
one_test!(test_case_insensitivity);
one_test!(test_data);
one_test!(test_do);
one_test!(test_empty);
one_test!(test_end);
one_test!(test_for);
one_test!(test_functions);
one_test!(test_globals);
one_test!(test_gosub);
one_test!(test_goto);
one_test!(test_if);
one_test!(test_incremental);
one_test!(test_limits, "Very slow for regular development");
one_test!(test_locals);
one_test!(test_numerics);
one_test!(test_on_error);
one_test!(test_out_of_registers);
one_test!(test_relational_eq);
one_test!(test_relational_ge);
one_test!(test_relational_gt);
one_test!(test_relational_le);
one_test!(test_relational_lt);
one_test!(test_relational_ne);
one_test!(test_select);
one_test!(test_strings);
one_test!(test_subs);
one_test!(test_types);
one_test!(test_unary_neg_depth);
one_test!(test_unary_not_depth);
one_test!(test_while);

#[test]
fn test_all_md_files_registered() -> io::Result<()> {
    let mut registered = vec![];
    {
        let file = File::open(src_path("core/tests/integration_test.rs"))?;
        let reader = BufReader::new(file);
        for line in reader.lines() {
            let line = line?;

            if line.starts_with("one_test!(") {
                let delim = line.find([',', ')']).unwrap();
                let name = &line["one_test!(".len()..delim];
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
    for entry in fs::read_dir(src_path("core/tests"))? {
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
