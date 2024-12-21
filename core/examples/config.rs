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

//! Configuration file parser using an EndBASIC interpreter.
//!
//! This example sets up a minimal EndBASIC interpreter and uses it to parse what could be a
//! configuration file.  Because the interpreter is configured without any commands or functions,
//! the scripted code cannot call back into Rust land, so the script's execution is guaranteed to
//! not have side-effects.

use endbasic_core::{
    ast::Value,
    exec::{Machine, StopReason},
    syms::Symbol,
};
use futures_lite::future::block_on;

/// Sample configuration file to parse.
const INPUT: &str = r#"
foo_value = 123
enable_bar = (foo_value > 122)
'enable_baz = "this is commented out"
"#;

fn main() {
    // Create an empty machine.
    let mut machine = Machine::default();

    // Execute the sample script.  All this script can do is modify the state of the machine itself.
    // In other words: the script can set variables in the machine's environment, but that's it.
    let mut context = machine.compile(&mut INPUT.as_bytes()).expect("Compilation error");
    loop {
        match block_on(machine.exec(&mut context)).expect("Execution error") {
            StopReason::Eof => break,
            StopReason::Exited(i, _is_final) => {
                println!("Script explicitly exited with code {}", i)
            }
        }
    }

    // Now that our script has run, inspect the variables it set on the machine.
    match machine.get_symbols().get_auto("foo_value") {
        Some(Symbol::Variable(Value::Integer(i))) => {
            println!("foo_value is {}", i)
        }
        _ => println!("Input did not contain foo_value or is of an invalid type"),
    }
    match machine.get_symbols().get_auto("enable_bar") {
        Some(Symbol::Variable(Value::Boolean(b))) => {
            println!("enable_bar is {}", b)
        }
        _ => println!("Input did not contain enable_bar or is of an invalid type"),
    }
    match machine.get_symbols().get_auto("enable_baz") {
        Some(_) => {
            println!("enable_baz should not have been set")
        }
        _ => println!("enable_baz is not set"),
    }
}
