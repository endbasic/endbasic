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

use crate::ast::{ArgSep, Value, VarRef, VarType};
use crate::exec::Machine;
use crate::syms::{
    Array, CallError, CallResult, Callable, CallableMetadata, CallableMetadataBuilder, Symbol,
    SymbolKey, Symbols,
};
use crate::value;
use crate::LineCol;
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
        Value::Missing => panic!("Should never try to format missing arguments in tests"),
        Value::Separator(s) => o.push_str(&format!("{:?}", s)),
        Value::Text(s) => o.push_str(&s),
        Value::VarRef(v) => o.push_str(&format!("{}", v)),
        Value::Void => panic!("Should never try to format void in tests"),
    }
}

/// Returns a constant value.
pub struct ArglessFunction {
    metadata: CallableMetadata,
    value: Value,
}

impl ArglessFunction {
    pub fn new(value: Value) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("ARGLESS", value.as_vartype()).test_build(),
            value,
        })
    }
}

#[async_trait(?Send)]
impl Callable for ArglessFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, _machine: &mut Machine) -> CallResult {
        assert!(args.is_empty());
        Ok(self.value.clone())
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
impl Callable for ClearCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, machine: &mut Machine) -> CallResult {
        assert!(args.is_empty());
        machine.clear();
        Ok(Value::Void)
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
impl Callable for CountFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, _machine: &mut Machine) -> CallResult {
        assert!(args.is_empty());
        let mut counter = self.counter.borrow_mut();
        *counter += 1;
        debug_assert!(*counter >= 0);
        Ok(Value::Integer(*counter))
    }
}

/// Raises the error type asked for in an argument.
pub struct RaisefFunction {
    metadata: CallableMetadata,
}

impl RaisefFunction {
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("RAISEF", VarType::Boolean)
                .with_syntax("arg1$")
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for RaisefFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, machine: &mut Machine) -> CallResult {
        let mut iter = machine.load_all(args)?.into_iter();
        let result = match iter.next().expect("Invalid arguments") {
            (Value::Text(s), pos) => {
                if s == "argument" {
                    Err(CallError::ArgumentError(pos, "Bad argument".to_owned()))
                } else if s == "eval" {
                    Err(CallError::EvalError(pos, "Some eval error".to_owned()))
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
        };
        if iter.next().is_some() {
            panic!("Invalid arguments");
        }
        result
    }
}

/// Raises the error type asked for in an argument.
pub struct RaiseCommand {
    metadata: CallableMetadata,
}

impl RaiseCommand {
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("RAISE", VarType::Void)
                .with_syntax("arg1$")
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for RaiseCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, machine: &mut Machine) -> CallResult {
        let mut iter = machine.load_all(args)?.into_iter();
        let result = match iter.next().expect("Invalid arguments") {
            (Value::Text(s), pos) => {
                if s == "argument" {
                    Err(CallError::ArgumentError(pos, "Bad argument".to_owned()))
                } else if s == "eval" {
                    Err(CallError::EvalError(pos, "Some eval error".to_owned()))
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
        };
        if iter.next().is_some() {
            panic!("Invalid arguments");
        }
        result
    }
}

/// Grabs the value of a hidden variable.
pub(crate) struct GetHiddenFunction {
    metadata: CallableMetadata,
}

impl GetHiddenFunction {
    /// Creates a new command that sets aside all data values.
    pub(crate) fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GETHIDDEN", VarType::Text)
                .with_syntax("varname$")
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for GetHiddenFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, machine: &mut Machine) -> CallResult {
        assert_eq!(1, args.len());
        match &args[0] {
            (Value::Text(name), _pos) => match machine.get_var(&VarRef::new(name, VarType::Text)) {
                Ok(t) => Ok(t.clone()),
                Err(_) => panic!("Invalid argument"),
            },
            _ => panic!("Invalid argument"),
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
impl Callable for GetDataCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, machine: &mut Machine) -> CallResult {
        assert!(args.is_empty());
        *self.data.borrow_mut() = machine.get_data().to_vec();
        Ok(Value::Void)
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
impl Callable for InCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, machine: &mut Machine) -> CallResult {
        let mut iter = args.into_iter();
        let (vref, pos) = match iter.next() {
            Some((Value::VarRef(vref), pos)) => (vref, pos),
            _ => panic!("Invalid arguments"),
        };
        if iter.next().is_some() {
            panic!("Invalid arguments");
        }

        let mut data = self.data.borrow_mut();
        let raw_value = data.next().unwrap().to_owned();
        let value = Value::parse_as(vref.ref_type(), raw_value)
            .map_err(|e| CallError::EvalError(pos, e.message))?;
        machine.get_mut_symbols().assign(&SymbolKey::from(vref.name()), value);
        Ok(Value::Void)
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
impl Callable for OutCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, machine: &mut Machine) -> CallResult {
        let mut iter = machine.load_all(args)?.into_iter();
        let mut text = String::new();
        loop {
            match iter.next() {
                Some((value, _pos)) => {
                    format_value(value, &mut text);
                }
                _ => panic!("Invalid arguments"),
            }
            match iter.next() {
                None => break,
                Some((Value::Separator(ArgSep::Short), _pos)) => text += " ",
                _ => panic!("Invalid arguments"),
            }
        }
        self.data.borrow_mut().push(text);
        Ok(Value::Void)
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
impl Callable for OutfFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, machine: &mut Machine) -> CallResult {
        assert!(!args.is_empty());

        let mut iter = machine.load_all(args)?.into_iter();
        let result = match iter.next() {
            Some((v @ Value::Integer(_), _pos)) => v,
            _ => unreachable!("Only supports printing integers"),
        };

        let mut text = String::new();
        let mut first = true;
        for arg in iter {
            if !first {
                text += " ";
            }
            first = false;

            format_value(arg.0, &mut text);
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
impl Callable for SumFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, machine: &mut Machine) -> CallResult {
        let mut result = Value::Integer(0);
        for (value, pos) in machine.load_all(args)? {
            result = value::add_integer(result, value)
                .map_err(|e| CallError::EvalError(pos, e.message))?;
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

    /// Adds the `callable` to the list of symbols.
    pub fn add_callable(mut self, callable: Rc<dyn Callable>) -> Self {
        let name = callable.metadata().name();
        assert!(name == name.to_ascii_uppercase());
        self.by_name.insert(name.to_owned(), Symbol::Callable(callable));
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
impl Callable for TypeCheckFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: Vec<(Value, LineCol)>, _machine: &mut Machine) -> CallResult {
        assert!(args.is_empty());
        Ok(self.value.clone())
    }
}
