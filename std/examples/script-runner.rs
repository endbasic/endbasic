// EndBASIC
// Copyright 2021 Julio Merino
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

    let mut machine = endbasic_std::MachineBuilder::default().build();

    let mut input = match fs::File::open(path) {
        Ok(file) => file,
        Err(e) => {
            eprintln!("ERROR: {}", e);
            process::exit(1);
        }
    };

    match machine.compile(&mut input) {
        Ok(()) => match block_on(machine.exec()) {
            Ok(None) => 0,
            Ok(Some(code)) => code,
            Err(e) => {
                eprintln!("ERROR: {}", e);
                1
            }
        },
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
