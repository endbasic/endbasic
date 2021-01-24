// EndBASIC
// Copyright 2021 Julio Merino
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

//! Complete EndBASIC script executor for programs given as arguments.
//!
//! This example sets up a complete EndBASIC interpreter with the commands and functions that should
//! be allowed in scripts (and not in a REPL).

use endbasic_std::terminal::TerminalConsole;
use futures_lite::future::block_on;
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

    let console = Rc::from(RefCell::from(TerminalConsole::from_stdio().unwrap()));
    let mut machine = endbasic_std::scripting_machine(console);

    let mut input = match fs::File::open(path) {
        Ok(file) => file,
        Err(e) => {
            eprintln!("ERROR: {}", e);
            process::exit(1);
        }
    };

    match block_on(machine.exec(&mut input)) {
        Ok(stop_reason) => process::exit(stop_reason.as_exit_code()),
        Err(e) => {
            eprintln!("ERROR: {}", e);
            process::exit(1);
        }
    }
}
