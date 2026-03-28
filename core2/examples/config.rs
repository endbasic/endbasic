// EndBASIC
// Copyright 2026 Julio Merino
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

//! Configuration file parser using an EndBASIC interpreter.
//!
//! This example sets up a minimal EndBASIC interpreter and uses it to parse what could be a
//! configuration file.  Because the interpreter is configured without any commands or functions,
//! the scripted code cannot call back into Rust land, so the script's execution is guaranteed to
//! not have side-effects.

use endbasic_core2::{Compiler, ConstantDatum, ExprType, GlobalDef, GlobalDefKind, StopReason, Vm};
use std::collections::HashMap;

/// Sample configuration file to parse.
const SCRIPT: &str = r#"
foo_value% = 123
result_total% = foo_value% + 456
status$ = "Processing complete"
results%(0) = 10
results%(1) = 20
results%(2) = 30

DIM SHARED defined_within
defined_within = 42

injected_value% = injected_value% + 1
"#;

fn main() {
    // Describe the global variables the script is expected to read and write.
    // Note that "optional_flag" is declared so the script could set it, but the
    // script does not assign it.  Its value will be the zero default.
    // "injected_value" is pre-initialized to a value that we expect the script
    // to read and modify.
    let global_defs = vec![
        GlobalDef {
            name: "foo_value".to_owned(),
            kind: GlobalDefKind::Scalar { etype: ExprType::Integer, initial_value: None },
        },
        GlobalDef {
            name: "result_total".to_owned(),
            kind: GlobalDefKind::Scalar { etype: ExprType::Integer, initial_value: None },
        },
        GlobalDef {
            name: "status".to_owned(),
            kind: GlobalDefKind::Scalar { etype: ExprType::Text, initial_value: None },
        },
        GlobalDef {
            name: "results".to_owned(),
            kind: GlobalDefKind::Array { subtype: ExprType::Integer, dimensions: vec![3] },
        },
        GlobalDef {
            name: "optional_flag".to_owned(),
            kind: GlobalDefKind::Scalar { etype: ExprType::Boolean, initial_value: None },
        },
        GlobalDef {
            name: "injected_value".to_owned(),
            kind: GlobalDefKind::Scalar {
                etype: ExprType::Integer,
                initial_value: Some(ConstantDatum::Integer(5)),
            },
        },
    ];

    // Compile the script, making the pre-defined globals visible to it.
    let upcalls = HashMap::default();
    let compiler = Compiler::new(&upcalls, &global_defs).expect("Globals initialization failed");
    let image = compiler.compile(&mut SCRIPT.as_bytes()).expect("Compilation failed");

    // Execute the compiled image.
    let mut vm = Vm::new(upcalls);
    match vm.exec(&image) {
        StopReason::End(code) => {
            if !code.is_success() {
                eprintln!("Script exited with code {}", code.to_i32());
            }
        }
        StopReason::Eof => (),
        StopReason::Exception(pos, msg) => {
            eprintln!("Script raised an exception at {}: {}", pos, msg);
            std::process::exit(1);
        }
        StopReason::Upcall(_) => {
            eprintln!("Unexpected upcall (no upcalls are registered)");
            std::process::exit(1);
        }
    }

    // Query the global variables by key.
    match vm.get_global(&image, &"foo_value".into()) {
        Ok(Some(ConstantDatum::Integer(v))) => println!("foo_value% = {}", v),
        Ok(Some(other)) => println!("foo_value% has unexpected type: {:?}", other),
        Ok(None) => println!("foo_value% is not set"),
        Err(e) => println!("foo_value%: error: {}", e),
    }
    match vm.get_global(&image, &"result_total".into()) {
        Ok(Some(ConstantDatum::Integer(v))) => println!("result_total% = {}", v),
        Ok(Some(other)) => println!("result_total% has unexpected type: {:?}", other),
        Ok(None) => println!("result_total% is not set"),
        Err(e) => println!("result_total%: error: {}", e),
    }
    match vm.get_global(&image, &"status".into()) {
        Ok(Some(ConstantDatum::Text(v))) => println!("status$ = {:?}", v),
        Ok(Some(other)) => println!("status$ has unexpected type: {:?}", other),
        Ok(None) => println!("status$ is not set"),
        Err(e) => println!("status$: error: {}", e),
    }
    // defined_within was not provided upfront but was declared as a global within
    // the script.  We can query it here too.
    match vm.get_global(&image, &"defined_within".into()) {
        Ok(Some(ConstantDatum::Integer(v))) => println!("defined_within% = {}", v),
        Ok(Some(other)) => println!("result_total% has unexpected type: {:?}", other),
        Ok(None) => println!("defined_within% is not set"),
        Err(e) => println!("defined_within%: error: {}", e),
    }
    // optional_flag was declared but the script never assigned it, so it should
    // receive its "zero value".
    match vm.get_global(&image, &"optional_flag".into()) {
        Ok(Some(ConstantDatum::Boolean(v))) => println!("optional_flag? = {}", v),
        Ok(Some(other)) => println!("optional_flag? has unexpected type: {:?}", other),
        Ok(None) => println!("optional_flag? is not declared"),
        Err(e) => println!("optional_flag?: error: {}", e),
    }
    // injected_value was pre-initialized to 5 before compilation.  The script incremented
    // it by 1, so we expect 6 here.
    match vm.get_global(&image, &"injected_value".into()) {
        Ok(Some(ConstantDatum::Integer(v))) => println!("injected_value% = {}", v),
        Ok(Some(other)) => println!("injected_value% has unexpected type: {:?}", other),
        Ok(None) => println!("injected_value% is not set"),
        Err(e) => println!("injected_value%: error: {}", e),
    }
    // "unknown" was never declared at all, so get_global returns Ok(None).
    match vm.get_global(&image, &"unknown".into()) {
        Ok(Some(v)) => println!("unknown = {:?}", v),
        Ok(None) => println!("unknown is not declared"),
        Err(e) => println!("unknown: error: {}", e),
    }
    for i in 0..3_i32 {
        match vm.get_global_array(&image, &"results".into(), &[i]) {
            Ok(Some(ConstantDatum::Integer(v))) => println!("results%({}) = {}", i, v),
            Ok(Some(other)) => println!("results%({}) has unexpected type: {:?}", i, other),
            Ok(None) => println!("results%({}) is not set", i),
            Err(e) => println!("results%({}): error: {}", i, e),
        }
    }
    // Demonstrate that querying a scalar as an array yields an error.
    match vm.get_global_array(&image, &"foo_value".into(), &[0]) {
        Ok(v) => println!("foo_value%(0) = {:?}", v),
        Err(e) => println!("foo_value%(0): error: {}", e),
    }
}
