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

//! A modified EndBASIC interpreter with custom commands.
//!
//! This example sets up a EndBASIC interpreter and adds a couple of custom commands to it to show
//! how to hook up native Rust code into the interpreter.  These commands share some out-of-band
//! state not represented within the variables of the machine.

#[macro_use]
extern crate failure;

use endbasic::ast::{ArgSep, Expr, Value};
use endbasic::exec::{BuiltinCommand, Machine, MachineBuilder};
use failure::Fallible;
use std::cell::RefCell;
use std::io;
use std::rc::Rc;

/// Sample code to parse in this example.
const INPUT: &str = r#"
' Use the custom STORE command to save a string value "out of band".
STORE "some long text"

' Use the custom RETRIEVE command to print the previously-stored value by STORE.
RETRIEVE
"#;

/// The `STORE` command.
struct StoreCommand {
    state: Rc<RefCell<String>>,
}

impl BuiltinCommand for StoreCommand {
    fn name(&self) -> &'static str {
        "STORE"
    }

    fn syntax(&self) -> &'static str {
        "\"string to save\""
    }

    fn description(&self) -> &'static str {
        "Saves the string argument given to it in a Rust variable."
    }

    fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
        ensure!(args.len() == 1, "STORE takes one argument only");
        let expr = args[0]
            .0
            .as_ref()
            .expect("A single argument can never be empty");
        match expr.eval(machine.get_vars())? {
            Value::Text(t) => *self.state.borrow_mut() = t,
            _ => bail!("Mismatched expression type"),
        }
        Ok(())
    }
}

/// The `RETRIEVE` command.
struct RetrieveCommand {
    state: Rc<RefCell<String>>,
}

impl BuiltinCommand for RetrieveCommand {
    fn name(&self) -> &'static str {
        "RETRIEVE"
    }

    fn syntax(&self) -> &'static str {
        ""
    }

    fn description(&self) -> &'static str {
        "Retrieves the string saved by `StoreCommand` and prints it to the console."
    }

    fn exec(&self, args: &[(Option<Expr>, ArgSep)], _machine: &mut Machine) -> Fallible<()> {
        ensure!(args.is_empty(), "RETRIEVE takes no arguments");
        println!("The stored value was: {}", self.state.borrow());
        Ok(())
    }
}

fn main() {
    // Create an empty machine.
    let state = Rc::from(RefCell::from(String::new()));
    let mut machine = MachineBuilder::default()
        .add_builtin(Rc::from(StoreCommand {
            state: state.clone(),
        }))
        .add_builtin(Rc::from(RetrieveCommand { state }))
        .build();

    // Execute the sample script.  The script will call back into our custom commands, one of which
    // will update state in Rust land and the other will have side-effects in the console.
    let mut cursor = io::Cursor::new(INPUT.as_bytes());
    machine.exec(&mut cursor).expect("Execution error");
}
