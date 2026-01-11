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

use std::collections::HashMap;
use std::rc::Rc;

use async_trait::async_trait;
use endbasic_core2::*;

/// Sample configuration file to parse.
const INPUT: &str = r#"
foo_value = 123
bar_value = 2147483640
TEST 10 + 2
foo_value = 123
TEST 212
'Enable_bar = (foo_value > 122)
'enable_baz = "this is commented out"
"#;

struct TestCommand {
    metadata: CallableMetadata,
}

impl TestCommand {
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("TEST")
                .with_syntax(&[(&[], None)])
                .with_category("Demonstration")
                .with_description("Turns the light identified by 'id' on or off.")
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for TestCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    //async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> Result<()> {
    async fn exec(&self, scope: Scope<'_>) {
        eprintln!("TEST with arg {}", scope.get_integer(0));
    }
}

#[tokio::main]
async fn main() {
    let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::default();
    upcalls_by_name.insert(SymbolKey::from("TEST"), TestCommand::new());
    let image = compile(&mut INPUT.as_bytes(), &upcalls_by_name).unwrap();

    let mut vm = Vm::new(upcalls_by_name);
    let mut context = vm.load(image);
    loop {
        match vm.exec(&mut context) {
            StopReason::Eof => break,
            StopReason::Upcall => vm.handle_upcall(&mut context).await,
        }
    }

    //    // Create an empty machine.
    //    let mut machine = Machine::default();
    //
    //    // Execute the sample script.  All this script can do is modify the state of the machine itself.
    //    // In other words: the script can set variables in the machine's environment, but that's it.
    //    loop {
    //        match block_on(machine.exec(&mut INPUT.as_bytes())).expect("Execution error") {
    //            StopReason::Eof => break,
    //            StopReason::Exited(i) => println!("Script explicitly exited with code {}", i),
    //            StopReason::Break => (), // Ignore signals.
    //        }
    //    }
    //
    //    // Now that our script has run, inspect the variables it set on the machine.
    //    match machine.get_symbols().get_auto("foo_value") {
    //        Some(Symbol::Variable(Value::Integer(i))) => {
    //            println!("foo_value is {}", i)
    //        }
    //        _ => println!("Input did not contain foo_value or is of an invalid type"),
    //    }
    //    match machine.get_symbols().get_auto("enable_bar") {
    //        Some(Symbol::Variable(Value::Boolean(b))) => {
    //            println!("enable_bar is {}", b)
    //        }
    //        _ => println!("Input did not contain enable_bar or is of an invalid type"),
    //    }
    //    match machine.get_symbols().get_auto("enable_baz") {
    //        Some(_) => {
    //            println!("enable_baz should not have been set")
    //        }
    //        _ => println!("enable_baz is not set"),
    //    }
}
