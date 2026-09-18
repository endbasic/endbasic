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

//! rustc wrapper for Windows to deal with long command lines.
//!
//! This wrapper skips sccache for crates that require very long command lines.
//! Cargo correctly produces response files but sccache expands them and leads
//! to problems.

use std::env;
use std::ffi::OsString;
use std::process::{Command, exit};

const COMMAND_LINE_LIMIT: usize = 7000;

/// Calculates the length of the command in `args`.
fn command_length(args: &[OsString]) -> usize {
    args.iter().map(|arg| arg.to_string_lossy().len() + 1).sum()
}

/// Checks if the command in `args` uses a response file.
fn has_response_file(args: &[OsString]) -> bool {
    args.first().map(|arg| arg.to_string_lossy().starts_with('@')).unwrap_or(false)
}

/// Wrapper entry point.
fn main() {
    let mut args = env::args_os();
    let _program = args.next();
    let rustc = args.next().expect("missing rustc path");
    let rustc_args: Vec<OsString> = args.collect();

    let use_sccache =
        !has_response_file(&rustc_args) && command_length(&rustc_args) < COMMAND_LINE_LIMIT;
    let mut command = if use_sccache {
        let mut command = Command::new("sccache");
        command.arg(&rustc);
        command
    } else {
        Command::new(&rustc)
    };
    let status = command.args(rustc_args).status().expect("failed to execute compiler");
    exit(status.code().unwrap_or(1));
}
