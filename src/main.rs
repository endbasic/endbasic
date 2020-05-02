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

//! Command-line interface for the EndBASIC language.

// Keep these in sync with other top-level files.
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(
    unused,
    unused_extern_crates,
    unused_import_braces,
    unused_qualifications
)]
#![warn(unsafe_code)]

#[macro_use]
extern crate failure;

use failure::{Error, Fail, Fallible};
use std::env;
use std::fs::File;
use std::path::Path;
use std::process;

/// Errors caused by the user when invoking this binary (invalid options or arguments).
#[derive(Debug, Fail)]
#[fail(display = "{}", message)]
struct UsageError {
    message: String,
}

impl UsageError {
    /// Creates a new usage error with `message`.
    fn new<T: Into<String>>(message: T) -> Self {
        Self {
            message: message.into(),
        }
    }
}

/// Flattens all causes of an error into a single string.
fn flatten_causes(err: &Error) -> String {
    err.iter_chain().fold(String::new(), |flattened, cause| {
        let flattened = if flattened.is_empty() {
            flattened
        } else {
            flattened + ": "
        };
        flattened + &format!("{}", cause)
    })
}

/// Consumes and returns the program name from `env::Args`.
///
/// If the program name cannot be obtained, return `default_name` instead.
fn program_name(mut args: env::Args, default_name: &'static str) -> (String, env::Args) {
    let name = match args.next() {
        Some(arg0) => match Path::new(&arg0).file_stem() {
            Some(basename) => match basename.to_str() {
                Some(s) => s.to_owned(),
                None => default_name.to_owned(),
            },
            None => default_name.to_owned(),
        },
        None => default_name.to_owned(),
    };
    (name, args)
}

/// Implementation of the EndBASIC console to interact with stdin and stdout.
#[derive(Default)]
struct StdioConsole {}

/// Executes the `path` program in a fresh machine.
fn run<P: AsRef<Path>>(path: P) -> Fallible<()> {
    let console = endbasic::repl::new_console();
    let mut machine = endbasic::exec::MachineBuilder::default()
        .add_builtins(endbasic::console::all_commands(console.clone()))
        .build();

    let mut input = File::open(path)?;
    machine.exec(&mut input)
}

/// Version of `main` that returns errors to the caller for reporting.
fn safe_main(args: env::Args) -> Fallible<()> {
    let args: Vec<String> = args.collect();
    match args.as_slice() {
        [] => Ok(endbasic::repl::run_repl_loop()?),
        [file] => run(file),
        [_, ..] => Err(UsageError::new("Too many arguments").into()),
    }
}

fn main() {
    let (name, args) = program_name(env::args(), "endbasic");
    if let Err(e) = safe_main(args) {
        if let Some(e) = e.downcast_ref::<UsageError>() {
            eprintln!("{}: Usage error: {}", name, e);
            process::exit(2);
        } else {
            eprintln!("{}: {}", name, flatten_causes(&e));
            process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flatten_causes_one() {
        assert_eq!("the error", flatten_causes(&format_err!("the error")));
    }

    #[test]
    fn flatten_causes_several() {
        let err = Error::from(format_err!("first").context("second").context("and last"));
        assert_eq!("and last: second: first", flatten_causes(&err));
    }
}
