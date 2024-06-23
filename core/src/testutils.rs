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

use crate::ast::{ArgSep, ExprType, Value, VarRef};
use crate::compiler::{
    ArgSepSyntax, RepeatedSyntax, RepeatedTypeSyntax, RequiredRefSyntax, RequiredValueSyntax,
    SingularArgSyntax,
};
use crate::exec::{Machine, Scope, ValueTag};
use crate::syms::{
    Array, CallError, CallResult, Callable, CallableMetadata, CallableMetadataBuilder, Symbol,
    Symbols,
};
use crate::value;
use async_trait::async_trait;
use std::cell::RefCell;
use std::collections::HashMap;
use std::io;
use std::rc::Rc;

/// Returns a constant value.
pub struct ArglessFunction {
    metadata: CallableMetadata,
    value: Value,
}

impl ArglessFunction {
    pub fn new(value: Value) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("ARGLESS")
                .with_syntax(&[(&[], None)])
                .with_return_type(value.as_exprtype())
                .test_build(),
            value,
        })
    }
}

#[async_trait(?Send)]
impl Callable for ArglessFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
        assert_eq!(0, scope.nargs());
        scope.return_any(self.value.clone())
    }
}

/// Clears the machine state.
pub(crate) struct ClearCommand {
    metadata: CallableMetadata,
}

impl ClearCommand {
    pub(crate) fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("CLEAR")
                .with_syntax(&[(&[], None)])
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for ClearCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, scope: Scope<'_>, machine: &mut Machine) -> CallResult {
        assert_eq!(0, scope.nargs());
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
            metadata: CallableMetadataBuilder::new("COUNT")
                .with_return_type(ExprType::Integer)
                .with_syntax(&[(&[], None)])
                .test_build(),
            counter: Rc::from(RefCell::from(0)),
        })
    }
}

#[async_trait(?Send)]
impl Callable for CountFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
        assert_eq!(0, scope.nargs());
        let mut counter = self.counter.borrow_mut();
        *counter += 1;
        debug_assert!(*counter >= 0);
        scope.return_integer(*counter)
    }
}

/// Raises the error type asked for in an argument.
pub struct RaisefFunction {
    metadata: CallableMetadata,
}

impl RaisefFunction {
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("RAISEF")
                .with_return_type(ExprType::Boolean)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax { name: "arg", vtype: ExprType::Text },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for RaisefFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
        assert_eq!(1, scope.nargs());
        let (arg, pos) = scope.pop_string_with_pos();
        match arg.as_str() {
            "argument" => Err(CallError::ArgumentError(pos, "Bad argument".to_owned())),
            "eval" => Err(CallError::EvalError(pos, "Some eval error".to_owned())),
            "internal" => Err(CallError::InternalError(pos, "Some internal error".to_owned())),
            "io" => Err(io::Error::new(io::ErrorKind::Other, "Some I/O error".to_owned()).into()),
            "syntax" => Err(CallError::SyntaxError),
            _ => panic!("Invalid arguments"),
        }
    }
}

/// Raises the error type asked for in an argument.
pub struct RaiseCommand {
    metadata: CallableMetadata,
}

impl RaiseCommand {
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("RAISE")
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax { name: "arg", vtype: ExprType::Text },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for RaiseCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
        assert_eq!(1, scope.nargs());
        let (arg, pos) = scope.pop_string_with_pos();
        match arg.as_str() {
            "argument" => Err(CallError::ArgumentError(pos, "Bad argument".to_owned())),
            "eval" => Err(CallError::EvalError(pos, "Some eval error".to_owned())),
            "internal" => Err(CallError::InternalError(pos, "Some internal error".to_owned())),
            "io" => Err(io::Error::new(io::ErrorKind::Other, "Some I/O error".to_owned()).into()),
            "syntax" => Err(CallError::SyntaxError),
            _ => panic!("Invalid arguments"),
        }
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
            metadata: CallableMetadataBuilder::new("GETHIDDEN")
                .with_return_type(ExprType::Text)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax { name: "varname", vtype: ExprType::Text },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for GetHiddenFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, machine: &mut Machine) -> CallResult {
        assert_eq!(1, scope.nargs());
        let name = scope.pop_string();
        match machine.get_var(&VarRef::new(name, Some(ExprType::Text))) {
            Ok(t) => scope.return_any(t.clone()),
            Err(_) => panic!("Invalid argument"),
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
            metadata: CallableMetadataBuilder::new("GETDATA")
                .with_syntax(&[(&[], None)])
                .test_build(),
            data,
        })
    }
}

#[async_trait(?Send)]
impl Callable for GetDataCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, scope: Scope<'_>, machine: &mut Machine) -> CallResult {
        assert_eq!(0, scope.nargs());
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
            metadata: CallableMetadataBuilder::new("IN")
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredRef(
                        RequiredRefSyntax {
                            name: "vref",
                            require_array: false,
                            define_undefined: true,
                        },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .test_build(),
            data,
        })
    }
}

#[async_trait(?Send)]
impl Callable for InCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, machine: &mut Machine) -> CallResult {
        debug_assert_eq!(1, scope.nargs());
        let (vname, vtype, pos) = scope.pop_varref_with_pos();

        let mut data = self.data.borrow_mut();
        let raw_value = data.next().unwrap().to_owned();
        let value =
            Value::parse_as(vtype, raw_value).map_err(|e| CallError::EvalError(pos, e.message))?;
        machine.get_mut_symbols().assign(&vname, value);
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
            metadata: CallableMetadataBuilder::new("OUT")
                .with_syntax(&[(
                    &[],
                    Some(&RepeatedSyntax {
                        name: "arg",
                        type_syn: RepeatedTypeSyntax::AnyValue,
                        sep: ArgSepSyntax::Exactly(ArgSep::Short),
                        require_one: false,
                        allow_missing: false,
                    }),
                )])
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

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
        let mut first = true;
        let mut text = String::new();
        while scope.nargs() > 0 {
            if !first {
                text += " ";
            }
            first = false;

            match scope.pop_value_tag() {
                ValueTag::Boolean => {
                    let b = scope.pop_boolean();
                    if b {
                        text.push_str("TRUE");
                    } else {
                        text.push_str("FALSE");
                    }
                }
                ValueTag::Double => {
                    let d = scope.pop_double();
                    text.push_str(&d.to_string());
                }
                ValueTag::Integer => {
                    let i = scope.pop_integer();
                    text.push_str(&i.to_string());
                }
                ValueTag::Text => {
                    let s = scope.pop_string();
                    text.push_str(&s);
                }
                ValueTag::Missing => {
                    unreachable!("Missing expressions aren't allowed in function calls");
                }
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
            metadata: CallableMetadataBuilder::new("OUTF")
                .with_return_type(ExprType::Integer)
                .with_syntax(&[(
                    &[],
                    Some(&RepeatedSyntax {
                        name: "expr",
                        type_syn: RepeatedTypeSyntax::TypedValue(ExprType::Integer),
                        sep: ArgSepSyntax::Exactly(ArgSep::Long),
                        require_one: false,
                        allow_missing: false,
                    }),
                )])
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

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
        assert_ne!(0, scope.nargs());

        let result = scope.pop_integer();

        let mut text = String::new();
        let mut first = true;
        while scope.nargs() > 0 {
            let arg = scope.pop_integer();

            if !first {
                text += " ";
            }
            first = false;

            text.push_str(&arg.to_string());
        }
        self.data.borrow_mut().push(text);
        scope.return_integer(result)
    }
}

/// Sums a collection of integers of arbitrary length.
pub struct SumFunction {
    metadata: CallableMetadata,
}

impl SumFunction {
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("SUM")
                .with_return_type(ExprType::Integer)
                .with_syntax(&[(
                    &[],
                    Some(&RepeatedSyntax {
                        name: "n",
                        type_syn: RepeatedTypeSyntax::TypedValue(ExprType::Integer),
                        sep: ArgSepSyntax::Exactly(ArgSep::Long),
                        require_one: false,
                        allow_missing: false,
                    }),
                )])
                .test_build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for SumFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
        let mut result = 0;
        while scope.nargs() > 0 {
            let (i, pos) = scope.pop_integer_with_pos();
            result =
                value::add_integer(result, i).map_err(|e| CallError::EvalError(pos, e.message))?;
        }
        scope.return_integer(result)
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
    pub fn add_array<S: Into<String>>(mut self, name: S, subtype: ExprType) -> Self {
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
            metadata: CallableMetadataBuilder::new("TYPE_CHECK")
                .with_return_type(ExprType::Boolean)
                .with_syntax(&[(&[], None)])
                .test_build(),
            value,
        })
    }
}

#[async_trait(?Send)]
impl Callable for TypeCheckFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
        assert_eq!(0, scope.nargs());
        scope.return_any(self.value.clone())
    }
}
