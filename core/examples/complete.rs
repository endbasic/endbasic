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

//! Complete EndBASIC interpreter for programs given as arguments.
//!
//! This example sets up a complete EndBASIC interpreter: that is, one with all available commands,
//! and processes the given file.

use std::cell::RefCell;
use std::env;
use std::fs;
use std::process;
use std::rc::Rc;

fn main() {
    let args: Vec<String> = env::args().collect();
    let path = match args.as_slice() {
        [_, path] => path,
        _ => {
            eprintln!("Usage error: expected a file name");
            process::exit(1);
        }
    };

    // TODO(jmmv): Truly add all commands in the core library and test for them.
    let console = Rc::from(RefCell::from(endbasic_core::repl::TextConsole::from_stdio()));
    let mut machine = endbasic_core::exec::MachineBuilder::default()
        .add_builtins(endbasic_core::console::all_commands(console))
        .build();

    let mut input = match fs::File::open(path) {
        Ok(file) => file,
        Err(e) => {
            eprintln!("ERROR: {}", e);
            process::exit(1);
        }
    };

    match machine.exec(&mut input) {
        Ok(()) => (),
        Err(e) => {
            eprintln!("ERROR: {}", e);
            process::exit(1);
        }
    }
}
