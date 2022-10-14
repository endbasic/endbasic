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

//! Test utilities.

use crate::ast::{ArgSep, Expr, Value, VarType};
use crate::eval::{eval_all, Error};
use crate::exec::Machine;
use crate::syms::{
    Array, CallError, CallableMetadata, CallableMetadataBuilder, Command, CommandResult, Function,
    FunctionResult, Symbol, Symbols,
};
use async_trait::async_trait;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

/// Returns the error type asked for in an argument.
pub struct ErrorFunction {
    metadata: CallableMetadata,
}

impl ErrorFunction {
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("ERROR", VarType::Boolean)
                .with_syntax("arg1$")
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for ErrorFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[Expr], symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(args, symbols).await?;
        match args.as_slice() {
            [Value::Text(s)] => {
                if s == "argument" {
                    Err(CallError::ArgumentError("Bad argument".to_owned()))
                } else if s == "eval" {
                    Err(Error::new("Some eval error").into())
                } else if s == "internal" {
                    Err(CallError::InternalError("Some internal error".to_owned()))
                } else if s == "syntax" {
                    Err(CallError::SyntaxError)
                } else {
                    panic!("Unknown argument");
                }
            }
            _ => panic!("Invalid arguments"),
        }
    }
}

/// Simplified version of `EXIT` to test the machine's `exit()` method.
pub struct ExitCommand {
    metadata: CallableMetadata,
}

impl ExitCommand {
    /// Creates a new command that terminates execution once called.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("EXIT", VarType::Void).test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Command for ExitCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        let arg = match args {
            [(Some(expr), ArgSep::End)] => match expr.eval(machine.get_mut_symbols()).await? {
                Value::Integer(n) => {
                    assert!((0..128).contains(&n), "Exit code out of range");
                    n as u8
                }
                _ => panic!("Exit code must be a positive integer"),
            },
            _ => panic!("EXIT takes one argument"),
        };
        machine.exit(arg);
        Ok(())
    }
}

/// Simplified version of `INPUT` to feed input values based on some golden `data`.
///
/// Every time this command is invoked, it yields the next value from the `data` iterator and
/// assigns it to the variable provided as its only argument.
pub struct InCommand {
    metadata: CallableMetadata,
    data: Box<RefCell<dyn Iterator<Item = &'static &'static str>>>,
}

impl InCommand {
    /// Creates a new command with the golden `data`.
    pub fn new(data: Box<RefCell<dyn Iterator<Item = &'static &'static str>>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("IN", VarType::Void).test_build(),
            data,
        })
    }
}

#[async_trait(?Send)]
impl Command for InCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        if args.len() != 1 {
            return Err(CallError::SyntaxError);
        }
        if args[0].1 != ArgSep::End {
            return Err(CallError::SyntaxError);
        }
        let vref = match &args[0].0 {
            Some(Expr::Symbol(vref)) => vref,
            _ => return Err(CallError::SyntaxError),
        };

        let mut data = self.data.borrow_mut();
        let raw_value = data.next().unwrap().to_owned();
        let value = Value::parse_as(vref.ref_type(), raw_value)?;
        machine.get_mut_symbols().set_var(vref, value)?;
        Ok(())
    }
}

/// Simplified version of `PRINT` that captures all calls to it into `data`.
///
/// This command only accepts arguments separated by the `;` short separator and concatenates
/// them with a single space.
pub struct OutCommand {
    metadata: CallableMetadata,
    data: Rc<RefCell<Vec<String>>>,
}

impl OutCommand {
    /// Creates a new command that captures all calls into `data`.
    pub fn new(data: Rc<RefCell<Vec<String>>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("OUT", VarType::Void).test_build(),
            data,
        })
    }
}

#[async_trait(?Send)]
impl Command for OutCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        let mut text = String::new();
        for arg in args.iter() {
            if let Some(expr) = arg.0.as_ref() {
                text += &expr.eval(machine.get_mut_symbols()).await?.to_output();
            }
            match arg.1 {
                ArgSep::End => break,
                ArgSep::Short => text += " ",
                ArgSep::Long => return Err(CallError::SyntaxError),
            }
        }
        self.data.borrow_mut().push(text);
        Ok(())
    }
}

/// Sums a collection of integers of arbitrary length.
pub struct SumFunction {
    metadata: CallableMetadata,
}

impl SumFunction {
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("SUM", VarType::Integer).test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for SumFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[Expr], symbols: &mut Symbols) -> FunctionResult {
        let mut result = Value::Integer(0);
        for a in args {
            let value = a.eval(symbols).await?;
            result = result.add(&value)?;
        }
        Ok(result)
    }
}

/// Builder pattern for a test `Symbols` object.
// TODO(jmmv): Consider removing this.  I originally added it to bypass all setters in tests that
// don't need them... but its value is dubious (given that it's a fragile duplication of the logic
// in the real Symbols).
#[derive(Default)]
pub struct SymbolsBuilder {
    by_name: HashMap<String, Symbol>,
}

impl SymbolsBuilder {
    /// Adds the array named `name` of type `subtype` to the list of symbols.  The dimensions
    /// and contents of the array are unspecified.
    pub fn add_array<S: Into<String>>(mut self, name: S, subtype: VarType) -> Self {
        let name = name.into();
        assert!(name == name.to_ascii_uppercase());
        let array = Array::new(subtype, vec![10]);
        self.by_name.insert(name, Symbol::Array(array));
        self
    }

    /// Adds the command `cmd` to the list of symbols.
    pub fn add_command(mut self, cmd: Rc<dyn Command>) -> Self {
        let name = cmd.metadata().name();
        assert!(name == name.to_ascii_uppercase());
        self.by_name.insert(name.to_owned(), Symbol::Command(cmd));
        self
    }

    /// Adds the function `func` to the list of symbols.
    pub fn add_function(mut self, func: Rc<dyn Function>) -> Self {
        let name = func.metadata().name();
        assert!(name == name.to_ascii_uppercase());
        self.by_name.insert(name.to_owned(), Symbol::Function(func));
        self
    }

    /// Adds the variable named `name` with an initial `value` to the list of symbols.
    pub fn add_var<S: Into<String>>(mut self, name: S, value: Value) -> Self {
        let name = name.into();
        assert!(name == name.to_ascii_uppercase());
        self.by_name.insert(name, Symbol::Variable(value));
        self
    }

    pub fn build(self) -> Symbols {
        Symbols::from(self.by_name)
    }
}

/// Returns a value provided at construction time.  Note that the return type is fixed so we use
/// this to verify if return values are correctly type-checked.
pub struct TypeCheckFunction {
    metadata: CallableMetadata,
    value: Value,
}

impl TypeCheckFunction {
    pub fn new(value: Value) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("TYPE_CHECK", VarType::Boolean).test_build(),
            value,
        })
    }
}

#[async_trait(?Send)]
impl Function for TypeCheckFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[Expr], _symbols: &mut Symbols) -> FunctionResult {
        assert!(args.is_empty());
        Ok(self.value.clone())
    }
}
