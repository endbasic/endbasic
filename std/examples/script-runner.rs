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

use futures_lite::future::block_on;
use std::env;
use std::fs;
use std::process;

fn safe_main() -> i32 {
    let args: Vec<String> = env::args().collect();
    let path = match args.as_slice() {
        [_, path] => path,
        _ => {
            eprintln!("Usage error: expected a file name");
            process::exit(1);
        }
    };

    let mut machine = endbasic_std::MachineBuilder::default().build().unwrap();

    let mut input = match fs::File::open(path) {
        Ok(file) => file,
        Err(e) => {
            eprintln!("ERROR: {}", e);
            process::exit(1);
        }
    };

    let mut context = match machine.compile(&mut input) {
        Ok(context) => context,
        Err(e) => {
            eprintln!("ERROR: {}", e);
            process::exit(1);
        }
    };

    match block_on(machine.exec(&mut context)) {
        Ok(stop_reason) => stop_reason.as_exit_code(),
        Err(e) => {
            eprintln!("ERROR: {}", e);
            1
        }
    }
}

fn main() {
    // We must ensure that all destructors run (in particular, the console's destructor) before
    // exiting.  `process:exit` doesn't do that for us, so wrap the program's code into a separate
    // function so that we can guarantee that the destructors have run here.
    process::exit(safe_main());
}
