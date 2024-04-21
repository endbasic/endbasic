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

//! A domain-specific language (DSL) to control some hypothetical light fixtures.
//!
//! This example sets up a minimal EndBASIC interpreter without any parts of the standard library
//! and registers a custom function `NUM_LIGHTS` to query the number of available lights and a
//! custom command `SWITCH_LIGHT` to flip the status of the given light.  With these configured,
//! this example then runs a piece of EndBASIC code that uses these primitives to control the state
//! of the lights, and finally dumps the resulting state to the screen.

use async_trait::async_trait;
use endbasic_core::ast::{Value, VarType};
use endbasic_core::exec::{Machine, StopReason};
use endbasic_core::syms::{
    CallError, CallResult, Callable, CallableMetadata, CallableMetadataBuilder,
};
use endbasic_core::LineCol;
use futures_lite::future::block_on;
use std::cell::RefCell;
use std::rc::Rc;

/// Sample code that uses our DSL to control the lights.
const INPUT: &str = r#"
total = NUM_LIGHTS

' Start by turning all lights on.
FOR i = 1 TO total
    SWITCH_LIGHT i
NEXT

' And then switch every other light to off.
FOR i = 1 TO total STEP 2
    SWITCH_LIGHT i
NEXT
"#;

type Lights = Vec<bool>;

/// The `NUM_LIGHTS` function.
struct NumLightsFunction {
    metadata: CallableMetadata,
    lights: Rc<RefCell<Lights>>,
}

impl NumLightsFunction {
    /// Creates a new function that queries the `lights` state.
    pub fn new(lights: Rc<RefCell<Lights>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("NUM_LIGHTS", VarType::Integer)
                .with_syntax("")
                .with_category("Demonstration")
                .with_description("Returns the number of available lights.")
                .build(),
            lights,
        })
    }
}

#[async_trait(?Send)]
impl Callable for NumLightsFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, _machine: &mut Machine) -> CallResult {
        if !args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        let num = self.lights.borrow().len();
        assert!(num <= std::i32::MAX as usize, "Ended up with too many lights");
        Ok(Value::Integer(num as i32))
    }
}

/// The `SWITCH_LIGHT` command.
struct SwitchLightCommand {
    metadata: CallableMetadata,
    lights: Rc<RefCell<Lights>>,
}

impl SwitchLightCommand {
    /// Creates a new command that modifies the `lights` state.
    pub fn new(lights: Rc<RefCell<Lights>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("SWITCH_LIGHT", VarType::Void)
                .with_syntax("id")
                .with_category("Demonstration")
                .with_description("Turns the light identified by 'id' on or off.")
                .build(),
            lights,
        })
    }
}

#[async_trait(?Send)]
impl Callable for SwitchLightCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, machine: &mut Machine) -> CallResult {
        let mut iter = machine.load_all(args)?.into_iter();
        let (i, ipos) = match iter.next() {
            Some((Value::Integer(i), pos)) => (i, pos),
            _ => return Err(CallError::SyntaxError),
        };
        if iter.next().is_some() {
            return Err(CallError::SyntaxError);
        }

        let lights = &mut *self.lights.borrow_mut();
        if i < 1 {
            return Err(CallError::ArgumentError(
                ipos,
                "Light id cannot be zero or negative".to_owned(),
            ));
        }
        let i = i as usize;
        if i > lights.len() {
            return Err(CallError::ArgumentError(ipos, "Light id out of range".to_owned()));
        }
        if lights[i - 1] {
            println!("Turning light {} off", i);
        } else {
            println!("Turning light {} on", i);
        }
        lights[i - 1] = !lights[i - 1];
        Ok(Value::Void)
    }
}

fn main() {
    // Create the state of the lights.  We have to gate this state behind an Rc and a RefCell in
    // order to pass it around the callable objects used by EndBASIC.
    let lights = Rc::from(RefCell::from(vec![false; 10]));

    // Create the EndBASIC machine and register our callable objects to create our DSL.
    let mut machine = Machine::default();
    machine.add_command(SwitchLightCommand::new(lights.clone()));
    machine.add_function(NumLightsFunction::new(lights.clone()));

    // Execute the sample script, which will call back into our callable objects in Rust land to
    // manipulate the state of the lights.
    println!("Running script");
    loop {
        match block_on(machine.exec(&mut INPUT.as_bytes())).expect("Execution error") {
            StopReason::Eof => break,
            StopReason::Exited(i) => println!("Script explicitly exited with code {}", i),
            StopReason::Break => (), // Ignore signals.
        }
    }

    // Finally, print out the resulting state to verify that it is what we expect.
    println!("Script done. Dumping final lights state:");
    for (i, on) in lights.borrow().iter().enumerate() {
        if *on {
            println!("Light {} is on", i + 1);
        } else {
            println!("Light {} is off", i + 1);
        }
    }
}
