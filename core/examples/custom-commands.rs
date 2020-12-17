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

use async_trait::async_trait;
use endbasic_core::ast::{ArgSep, Expr, Value, VarType};
use endbasic_core::eval::{CallableMetadata, CallableMetadataBuilder};
use endbasic_core::exec::{self, BuiltinCommand, Machine, MachineBuilder};
use futures_lite::future::block_on;
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
    metadata: CallableMetadata,
    state: Rc<RefCell<String>>,
}

impl StoreCommand {
    /// Creates a new `STORE` command that updates the string in `state`.
    pub fn new(state: Rc<RefCell<String>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("STORE", VarType::Void)
                .with_syntax("\"string to save\"")
                .with_category("Demonstration")
                .with_description("Saves the string argument given to it in a Rust variable.")
                .build(),
            state,
        })
    }
}

#[async_trait(?Send)]
impl BuiltinCommand for StoreCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        machine: &mut Machine,
    ) -> exec::Result<()> {
        if args.len() != 1 {
            return exec::new_usage_error("STORE takes one argument only");
        }
        let expr = args[0].0.as_ref().expect("A single argument can never be empty");
        match expr.eval(machine.get_vars(), machine.get_functions())? {
            Value::Text(t) => *self.state.borrow_mut() = t,
            _ => return exec::new_usage_error("Mismatched expression type"),
        }
        Ok(())
    }
}

/// The `RETRIEVE` command.
struct RetrieveCommand {
    metadata: CallableMetadata,
    state: Rc<RefCell<String>>,
}

impl RetrieveCommand {
    /// Creates a new `RETRIEVE` command that prints the string in `state`.
    pub fn new(state: Rc<RefCell<String>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("RETRIEVE", VarType::Void)
                .with_syntax("")
                .with_category("Demonstration")
                .with_description(
                    "Retrieves the string saved by STORE and prints it to the console.",
                )
                .build(),
            state,
        })
    }
}

#[async_trait(?Send)]
impl BuiltinCommand for RetrieveCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        _machine: &mut Machine,
    ) -> exec::Result<()> {
        if !args.is_empty() {
            return exec::new_usage_error("RETRIEVE takes no arguments");
        }
        println!("The stored value was: {}", self.state.borrow());
        Ok(())
    }
}

fn main() {
    // Create an empty machine.
    let state = Rc::from(RefCell::from(String::new()));
    let mut machine = MachineBuilder::default()
        .add_command(StoreCommand::new(state.clone()))
        .add_command(RetrieveCommand::new(state))
        .build();

    // Execute the sample script.  The script will call back into our custom commands, one of which
    // will update state in Rust land and the other will have side-effects in the console.
    let mut cursor = io::Cursor::new(INPUT.as_bytes());
    block_on(machine.exec(&mut cursor)).expect("Execution error");
}
