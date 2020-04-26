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

use failure::Fallible;
use std::cell::RefCell;
use std::env;
use std::fs::File;
use std::io::{self, BufRead, Write};
use std::path::Path;
use std::process;
use std::rc::Rc;

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

impl endbasic::console::Console for StdioConsole {
    fn input(&mut self, prompt: &str) -> io::Result<String> {
        if !prompt.is_empty() {
            print!("{}", prompt);
            io::stdout().lock().flush()?;
        }

        let mut answer = String::new();
        {
            let stdin = io::stdin();
            let mut handle = stdin.lock();
            handle.read_line(&mut answer)?;
        }
        Ok(answer.trim_end().to_owned())
    }

    fn print(&mut self, text: &str) -> io::Result<()> {
        println!("{}", text);
        Ok(())
    }
}

/// Executes the `path` program in a fresh machine.
fn run<P: AsRef<Path>>(path: P) -> Fallible<()> {
    let console = Rc::from(RefCell::from(StdioConsole::default()));
    let mut machine = endbasic::exec::MachineBuilder::default()
        .add_builtins(endbasic::console::all_commands(console.clone()))
        .build();

    let mut input = File::open(path)?;
    machine.exec(&mut input)
}

fn main() {
    let (progname, args) = program_name(env::args(), "endbasic");
    let args: Vec<String> = args.collect();

    match args.as_slice() {
        [file] => match run(file) {
            Ok(()) => (),
            Err(e) => {
                eprintln!("{}: E: Execution failed: {}", progname, e);
                process::exit(1);
            }
        },
        [_, ..] => {
            eprintln!("{}: E: Too many arguments", progname);
            process::exit(1);
        }
        [] => {
            eprintln!("{}: E: No program specified", progname);
            process::exit(1);
        }
    }
}
