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

use crate::ast::{ArgSep, BuiltinCallSpan, Expr, FunctionCallSpan, Value, VarType};
use crate::eval::{self, eval_all, Error};
use crate::exec::Machine;
use crate::syms::{
    Array, CallError, CallableMetadata, CallableMetadataBuilder, Command, CommandResult, Function,
    FunctionResult, Symbol, Symbols,
};
use async_trait::async_trait;
use std::cell::RefCell;
use std::collections::HashMap;
use std::io;
use std::rc::Rc;

/// Formats a value `v` as text and appends it to a string `o`.
fn format_value(v: Value, o: &mut String) {
    match v {
        Value::Boolean(true) => o.push_str("TRUE"),
        Value::Boolean(false) => o.push_str("FALSE"),
        Value::Double(d) => o.push_str(&format!("{}", d)),
        Value::Integer(i) => o.push_str(&format!("{}", i)),
        Value::Text(s) => o.push_str(&s),
    }
}

/// Clears the machine state.
pub(crate) struct ClearCommand {
    metadata: CallableMetadata,
}

impl ClearCommand {
    pub(crate) fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("CLEAR", VarType::Void).test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Command for ClearCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        if !span.args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        machine.clear();
        Ok(())
    }
}

/// Counts and returns the number of times this has been evaluated.
pub(crate) struct CountFunction {
    metadata: CallableMetadata,
    counter: Rc<RefCell<i32>>,
}

impl CountFunction {
    pub(crate) fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("COUNT", VarType::Integer).test_build(),
            counter: Rc::from(RefCell::from(0)),
        })
    }
}

#[async_trait(?Send)]
impl Function for CountFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, _symbols: &mut Symbols) -> FunctionResult {
        if !span.args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        let mut counter = self.counter.borrow_mut();
        *counter += 1;
        debug_assert!(*counter >= 0);
        Ok(Value::Integer(*counter))
    }
}

/// Returns the error type asked for in an argument.
pub struct RaiseFunction {
    metadata: CallableMetadata,
}

impl RaiseFunction {
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("RAISE", VarType::Boolean)
                .with_syntax("arg1$")
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for RaiseFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        let args = eval_all(&span.args, symbols).await?;
        match args.as_slice() {
            [Value::Text(s)] => {
                let pos = span.args[0].start_pos();
                if s == "argument" {
                    Err(CallError::ArgumentError(pos, "Bad argument".to_owned()))
                } else if s == "eval" {
                    Err(Error::new(pos, "Some eval error").into())
                } else if s == "internal" {
                    Err(CallError::InternalError(pos, "Some internal error".to_owned()))
                } else if s == "io" {
                    Err(io::Error::new(io::ErrorKind::Other, "Some I/O error".to_owned()).into())
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

/// Grabs all `DATA` values available during execution.
pub(crate) struct GetDataCommand {
    metadata: CallableMetadata,
    data: Rc<RefCell<Vec<Option<Value>>>>,
}

impl GetDataCommand {
    /// Creates a new command that sets aside all data values.
    pub(crate) fn new(data: Rc<RefCell<Vec<Option<Value>>>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GETDATA", VarType::Void).test_build(),
            data,
        })
    }
}

#[async_trait(?Send)]
impl Command for GetDataCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        if !span.args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        *self.data.borrow_mut() = machine.get_data().to_vec();
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

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        if span.args.len() != 1 {
            return Err(CallError::SyntaxError);
        }
        if span.args[0].sep != ArgSep::End {
            return Err(CallError::SyntaxError);
        }
        let (vref, pos) = match &span.args[0].expr {
            Some(Expr::Symbol(span)) => (&span.vref, span.pos),
            _ => return Err(CallError::SyntaxError),
        };

        let mut data = self.data.borrow_mut();
        let raw_value = data.next().unwrap().to_owned();
        let value = Value::parse_as(vref.ref_type(), raw_value)
            .map_err(|e| eval::Error::from_value_error(e, pos))?;
        machine
            .get_mut_symbols()
            .set_var(vref, value)
            .map_err(|e| eval::Error::from_value_error(e, pos))?;
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
            metadata: CallableMetadataBuilder::new("OUT", VarType::Void)
                .with_syntax("[arg1 <;|,> argN]")
                .test_build(),
            data,
        })
    }
}

#[async_trait(?Send)]
impl Command for OutCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        let mut text = String::new();
        for arg in span.args.iter() {
            if let Some(expr) = arg.expr.as_ref() {
                format_value(expr.eval(machine.get_mut_symbols()).await?, &mut text);
            }
            match arg.sep {
                ArgSep::End => break,
                ArgSep::Short => text += " ",
                ArgSep::Long | ArgSep::As => return Err(CallError::SyntaxError),
            }
        }
        self.data.borrow_mut().push(text);
        Ok(())
    }
}

/// Simplified version of `PRINT` that captures all calls to it into `data` and that can be used
/// in the context of a function by using the first argument as the return value of the function.
pub struct OutfFunction {
    metadata: CallableMetadata,
    data: Rc<RefCell<Vec<String>>>,
}

impl OutfFunction {
    /// Creates a new function that captures all calls into `data`.
    pub fn new(data: Rc<RefCell<Vec<String>>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("OUTF", VarType::Integer)
                .with_syntax("arg1 [<;|,> argN]")
                .test_build(),
            data,
        })
    }
}

#[async_trait(?Send)]
impl Function for OutfFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        if span.args.len() < 2 {
            return Err(CallError::SyntaxError);
        }

        let args = eval_all(&span.args, symbols).await?;
        let mut iter = args.into_iter();
        let result = match iter.next() {
            Some(v @ Value::Integer(_)) => v,
            _ => return Err(CallError::SyntaxError),
        };

        let mut text = String::new();
        let mut first = true;
        for arg in iter {
            if !first {
                text += " ";
            }
            first = false;

            format_value(arg, &mut text);
        }
        self.data.borrow_mut().push(text);
        Ok(result)
    }
}

/// Sums a collection of integers of arbitrary length.
pub struct SumFunction {
    metadata: CallableMetadata,
}

impl SumFunction {
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("SUM", VarType::Integer)
                .with_syntax("[n1% .. nN%]")
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Function for SumFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult {
        let mut result = Value::Integer(0);
        for a in &span.args {
            let value = a.eval(symbols).await?;
            result =
                result.add(&value).map_err(|e| eval::Error::from_value_error(e, a.start_pos()))?;
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

    async fn exec(&self, span: &FunctionCallSpan, _symbols: &mut Symbols) -> FunctionResult {
        assert!(span.args.is_empty());
        Ok(self.value.clone())
    }
}
