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

//! Symbol definitions and symbols table representation.

use crate::ast::{BuiltinCallSpan, FunctionCallSpan, Value, VarRef, VarType};
use crate::eval;
use crate::exec::Machine;
use crate::reader::LineCol;
use crate::value::{Error, Result};
use async_trait::async_trait;
use std::collections::HashMap;
use std::fmt;
use std::io;
use std::mem;
use std::rc::Rc;
use std::str::Lines;

/// Command or function execution errors.
///
/// These are separate from the more generic `Error` type because they are not annotated with the
/// specific callable that triggered the error.  We add such annotation once we capture the error
/// within the evaluation logic.
#[derive(Debug)]
pub enum CallError {
    /// A specific parameter had an invalid value.
    ArgumentError(LineCol, String),

    /// Error while evaluating input arguments.
    EvalError(eval::Error),

    /// Any other error not representable by other values.
    InternalError(LineCol, String),

    /// I/O error during execution.
    IoError(io::Error),

    /// Hack to support errors that arise from within a program that is `RUN`.
    // TODO(jmmv): Consider unifying `CallError` with `exec::Error`.
    NestedError(String),

    /// General mismatch of parameters given to the function with expectations (different numbers,
    /// invalid types).
    SyntaxError,
}

impl From<eval::Error> for CallError {
    fn from(e: eval::Error) -> Self {
        Self::EvalError(e)
    }
}

impl From<io::Error> for CallError {
    fn from(e: io::Error) -> Self {
        Self::IoError(e)
    }
}

/// Result for command execution return values.
pub type CommandResult = std::result::Result<(), CallError>;

/// Result for function evaluation return values.
pub type FunctionResult = std::result::Result<Value, CallError>;

/// Represents a multidimensional array.
#[derive(Clone, Debug, PartialEq)]
pub struct Array {
    /// The type of all elements in the array.
    subtype: VarType,

    /// The dimensions of the array.  At least one must be present.
    dimensions: Vec<usize>,

    /// The values in the array, flattened.  Given dimensions `(N, M, O)`, an element `(i, j, k)` is
    /// at position `i * (M * O) + j * O + k`.
    values: Vec<Value>,
}

impl Array {
    /// Creates a new array of the given `subtype` and `dimensions`.
    pub fn new(subtype: VarType, dimensions: Vec<usize>) -> Self {
        assert!(!dimensions.is_empty());
        let mut n = 1;
        for dim in &dimensions {
            assert!(n > 0);
            n *= dim;
        }
        let mut values = Vec::with_capacity(n);
        let value = subtype.default_value();
        for _ in 0..n {
            values.push(value.clone());
        }
        Self { subtype, dimensions, values }
    }

    /// Returns the dimensions of the array.
    pub fn dimensions(&self) -> &[usize] {
        &self.dimensions
    }

    /// Returns the type of the elements in this array.
    pub fn subtype(&self) -> VarType {
        self.subtype
    }

    /// Validates that the subscript `i` is in the `[0,max)` range and converts it to an `usize`.
    fn validate_subscript(i: i32, max: usize) -> Result<usize> {
        if i < 0 {
            Err(Error::new(format!("Subscript {} cannot be negative", i)))
        } else if (i as usize) >= max {
            Err(Error::new(format!("Subscript {} exceeds limit of {}", i, max)))
        } else {
            Ok(i as usize)
        }
    }

    /// Computes the index to access the flat `values` array given a list of `subscripts`.
    ///
    /// It is an error if `dimensions` and `subscripts` have different sizes, or if the values in
    /// `subscripts` are negative.
    fn native_index(dimensions: &[usize], subscripts: &[i32]) -> Result<usize> {
        if subscripts.len() != dimensions.len() {
            return Err(Error::new(format!(
                "Cannot index array with {} subscripts; need {}",
                subscripts.len(),
                dimensions.len()
            )));
        }

        let mut offset = 0;
        let mut multiplier = 1;
        let mut k = dimensions.len() - 1;
        while k > 0 {
            offset += Array::validate_subscript(subscripts[k], dimensions[k])? * multiplier;
            debug_assert!(dimensions[k] > 0);
            multiplier *= dimensions[k];
            k -= 1;
        }
        offset += Array::validate_subscript(subscripts[k], dimensions[k])? * multiplier;
        Ok(offset)
    }

    /// Assings the `value` to the array position indicated by the `subscripts`.
    pub fn assign(&mut self, subscripts: &[i32], value: Value) -> Result<()> {
        let value = value.maybe_cast(self.subtype)?;
        if value.as_vartype() != self.subtype {
            return Err(Error::new(format!(
                "Cannot assign value of type {} to array of type {}",
                value.as_vartype(),
                self.subtype
            )));
        }
        let i = Array::native_index(&self.dimensions, subscripts)?;
        self.values[i] = value;
        Ok(())
    }

    /// Obtains the value contained in the array position indicated by the `subscripts`.
    pub fn index(&self, subscripts: &[i32]) -> Result<&Value> {
        let i = Array::native_index(&self.dimensions, subscripts)?;
        let value = &self.values[i];
        debug_assert!(value.as_vartype() == self.subtype);
        Ok(value)
    }
}

/// Holds the definition of a symbol.
pub enum Symbol {
    /// An array definition.
    Array(Array),

    /// A command definition.
    Command(Rc<dyn Command>),

    /// A function definition.
    Function(Rc<dyn Function>),

    /// A variable definition.
    Variable(Value),
}

impl Symbol {
    /// Returns the type the symbol evaluates as.
    fn eval_type(&self) -> VarType {
        match self {
            Symbol::Array(array) => array.subtype(),
            Symbol::Command(command) => command.metadata().return_type(),
            Symbol::Function(function) => function.metadata().return_type(),
            Symbol::Variable(value) => value.as_vartype(),
        }
    }

    /// Returns the metadata for the symbol, if any.
    pub fn metadata(&self) -> Option<&CallableMetadata> {
        match self {
            Symbol::Array(_) => None,
            Symbol::Command(command) => Some(command.metadata()),
            Symbol::Function(function) => Some(function.metadata()),
            Symbol::Variable(_) => None,
        }
    }

    /// Returns whether the symbol was defined by the user or not.
    fn user_defined(&self) -> bool {
        match self {
            Symbol::Array(_) => true,
            Symbol::Command(_) => false,
            Symbol::Function(_) => false,
            Symbol::Variable(_) => true,
        }
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Symbol::Array(array) => write!(f, "Array({:?})", array),
            Symbol::Command(command) => write!(f, "Command({:?})", command.metadata()),
            Symbol::Function(function) => write!(f, "Function({:?})", function.metadata()),
            Symbol::Variable(value) => write!(f, "Variable({:?})", value),
        }
    }
}

/// Storage for all symbols that exist at runtime.
#[derive(Default)]
pub struct Symbols {
    /// Map of symbol names to their definitions.
    by_name: HashMap<String, Symbol>,
}

impl Symbols {
    /// Constructs a symbols object from a flat map of symbol names to their definitions.
    #[cfg(test)]
    pub(crate) fn from(by_name: HashMap<String, Symbol>) -> Self {
        Self { by_name }
    }

    /// Registers the given builtin command.
    ///
    /// Given that commands cannot be defined at runtime, specifying a non-unique name results in
    /// a panic.
    pub fn add_command(&mut self, command: Rc<dyn Command>) {
        let key = command.metadata().name();
        debug_assert!(key == key.to_ascii_uppercase());
        assert!(!self.by_name.contains_key(key));
        self.by_name.insert(key.to_owned(), Symbol::Command(command));
    }

    /// Registers the given builtin function.
    ///
    /// Given that functions cannot be defined at runtime, specifying a non-unique name results in
    /// a panic.
    pub fn add_function(&mut self, function: Rc<dyn Function>) {
        let key = function.metadata().name();
        debug_assert!(key == key.to_ascii_uppercase());
        assert!(!self.by_name.contains_key(key));
        self.by_name.insert(key.to_owned(), Symbol::Function(function));
    }

    /// Returns the mapping of all symbols.
    pub fn as_hashmap(&self) -> &HashMap<String, Symbol> {
        &self.by_name
    }

    /// Clears all user-defined symbols.
    pub fn clear(&mut self) {
        // TODO(jmmv): Preserving symbols that start with __ is a hack that was added to support
        // the already-existing GPIO tests when RUN was changed to issue a CLEAR upfront.  This
        // is undocumented behavior and we should find a nicer way to do this.
        self.by_name.retain(|name, symbol| name.starts_with("__") || !symbol.user_defined());
    }

    /// Defines a new variable `name` of type `vartype`.  The variable must not yet exist.
    pub fn dim(&mut self, name: &str, vartype: VarType) -> Result<()> {
        let key = name.to_ascii_uppercase();
        if self.by_name.contains_key(&key) {
            return Err(Error::new(format!("Cannot DIM already-defined symbol {}", name)));
        }
        self.by_name.insert(key, Symbol::Variable(vartype.default_value()));
        Ok(())
    }

    /// Defines a new array `name` of type `subtype` with `dimensions`.  The array must not yet
    /// exist, and the name may not overlap function or variable names.
    pub fn dim_array(
        &mut self,
        name: &str,
        subtype: VarType,
        dimensions: Vec<usize>,
    ) -> Result<()> {
        let key = name.to_ascii_uppercase();
        if self.by_name.contains_key(&key) {
            return Err(Error::new(format!("Cannot DIM already-defined symbol {}", name)));
        }
        self.by_name.insert(key, Symbol::Array(Array::new(subtype, dimensions)));
        Ok(())
    }

    /// Obtains the value of a symbol or `None` if it is not defined.
    ///
    /// Returns an error if the type annotation in the symbol reference does not match its type.
    pub fn get(&self, vref: &VarRef) -> Result<Option<&Symbol>> {
        let key = &vref.name().to_ascii_uppercase();
        let symbol = self.by_name.get(key);
        if let Some(symbol) = symbol {
            let stype = symbol.eval_type();
            if !vref.accepts(stype) {
                return Err(Error::new(format!("Incompatible types in {} reference", vref)));
            }
        }
        Ok(symbol)
    }

    /// Obtains the value of a symbol or `None` if it is not defined.
    pub fn get_auto(&self, var: &str) -> Option<&Symbol> {
        let key = var.to_ascii_uppercase();
        self.by_name.get(&key)
    }

    /// Obtains the value of a symbol or `None` if it is not defined.
    ///
    /// Returns an error if the type annotation in the symbol reference does not match its type.
    pub fn get_mut(&mut self, vref: &VarRef) -> Result<Option<&mut Symbol>> {
        let key = &vref.name().to_ascii_uppercase();
        match self.by_name.get_mut(key) {
            Some(symbol) => {
                let stype = symbol.eval_type();
                if !vref.accepts(stype) {
                    return Err(Error::new(format!("Incompatible types in {} reference", vref)));
                }
                Ok(Some(symbol))
            }
            None => Ok(None),
        }
    }

    /// Obtains the value of a variable.
    ///
    /// Returns an error if the variable is not defined, if the referenced symbol is not a variable,
    /// or if the type annotation in the variable reference does not match the type of the value
    /// that the variable contains.
    pub fn get_var(&self, vref: &VarRef) -> Result<&Value> {
        match self.get(vref)? {
            Some(Symbol::Variable(v)) => Ok(v),
            Some(_) => Err(Error::new(format!("{} is not a variable", vref.name()))),
            None => Err(Error::new(format!("Undefined variable {}", vref.name()))),
        }
    }

    /// Adds a type annotation to the symbol reference if the symbol is already defined and the
    /// reference lacks one.
    pub fn qualify_varref(&self, vref: &VarRef) -> Result<VarRef> {
        let key = vref.name().to_ascii_uppercase();
        match self.by_name.get(&key) {
            Some(symbol) => match vref.ref_type() {
                VarType::Auto => Ok(vref.clone().qualify(symbol.eval_type())),
                _ => {
                    if !vref.accepts(symbol.eval_type()) {
                        return Err(Error::new(format!(
                            "Incompatible types in {} reference",
                            vref
                        )));
                    }
                    Ok(vref.clone())
                }
            },
            None => Ok(vref.clone()),
        }
    }

    /// Sets the value of a variable.
    ///
    /// If `vref` contains a type annotation, the type of the value must be compatible with that
    /// type annotation.
    ///
    /// If the variable is already defined, then the type of the new value must be compatible with
    /// the existing variable.  In other words: a variable cannot change types while it's alive.
    pub fn set_var(&mut self, vref: &VarRef, value: Value) -> Result<()> {
        let value = value.maybe_cast(vref.ref_type())?;
        match self.get_mut(vref)? {
            Some(Symbol::Variable(old_value)) => {
                let value = value.maybe_cast(old_value.as_vartype())?;
                if mem::discriminant(&value) != mem::discriminant(old_value) {
                    return Err(Error::new(format!(
                        "Cannot assign value of type {} to variable of type {}",
                        value.as_vartype(),
                        old_value.as_vartype(),
                    )));
                }
                *old_value = value;
                Ok(())
            }
            Some(_) => Err(Error::new(format!("Cannot redefine {} as a variable", vref))),
            None => {
                if !vref.accepts(value.as_vartype()) {
                    return Err(Error::new(format!(
                        "Cannot assign value of type {} to variable of type {}",
                        value.as_vartype(),
                        vref.ref_type(),
                    )));
                }
                self.by_name.insert(vref.name().to_ascii_uppercase(), Symbol::Variable(value));
                Ok(())
            }
        }
    }
}

/// Builder pattern for a callable's metadata.
pub struct CallableMetadataBuilder {
    name: &'static str,
    return_type: VarType,
    category: Option<&'static str>,
    syntax: Option<&'static str>,
    description: Option<&'static str>,
}

impl CallableMetadataBuilder {
    /// Constructs a new metadata builder with the minimum information necessary.
    ///
    /// All code except tests must populate the whole builder with details.  This is enforced at
    /// construction time, where we only allow some fields to be missing under the test
    /// configuration.
    pub fn new(name: &'static str, return_type: VarType) -> Self {
        assert!(name == name.to_ascii_uppercase(), "Callable name must be in uppercase");

        Self { name, return_type, syntax: None, category: None, description: None }
    }

    /// Sets the syntax specification for this callable.  The `syntax` is provided as a free-form
    /// string that is expected to use whatever representation suits the function best.
    pub fn with_syntax(mut self, syntax: &'static str) -> Self {
        self.syntax = Some(syntax);
        self
    }

    /// Sets the category for this callable.  All callables with the same category name will be
    /// grouped together in help messages.
    pub fn with_category(mut self, category: &'static str) -> Self {
        self.category = Some(category);
        self
    }

    /// Sets the description for this callable.  The `description` is a collection of paragraphs
    /// separated by a single newline character, where the first paragraph is taken as the summary
    /// of the description.  The summary must be a short sentence that is descriptive enough to be
    /// understood without further details.  Empty lines (paragraphs) are not allowed.
    pub fn with_description(mut self, description: &'static str) -> Self {
        for l in description.lines() {
            assert!(!l.is_empty(), "Description cannot contain empty lines");
        }
        self.description = Some(description);
        self
    }

    /// Generates the final `CallableMetadata` object, ensuring all values are present.
    pub fn build(self) -> CallableMetadata {
        CallableMetadata {
            name: self.name,
            return_type: self.return_type,
            syntax: self.syntax.expect("All callables must specify a syntax"),
            category: self.category.expect("All callables must specify a category"),
            description: self.description.expect("All callables must specify a description"),
        }
    }

    /// Generates the final `CallableMetadata` object, ensuring the minimal set of values are
    /// present.  Only useful for testing.
    pub fn test_build(self) -> CallableMetadata {
        CallableMetadata {
            name: self.name,
            return_type: self.return_type,
            syntax: self.syntax.unwrap_or(""),
            category: self.category.unwrap_or(""),
            description: self.description.unwrap_or(""),
        }
    }
}

/// Representation of a callable's metadata.
///
/// The callable is expected to hold onto an instance of this object within its struct to make
/// queries fast.
#[derive(Clone, Debug)]
pub struct CallableMetadata {
    name: &'static str,
    return_type: VarType,
    syntax: &'static str,
    category: &'static str,
    description: &'static str,
}

impl CallableMetadata {
    /// Gets the callable's name, all in uppercase.
    pub fn name(&self) -> &'static str {
        self.name
    }

    /// Gets the callable's return type.
    pub fn return_type(&self) -> VarType {
        self.return_type
    }

    /// Gets the callable's syntax specification.
    pub fn syntax(&self) -> &'static str {
        self.syntax
    }

    /// Gets the callable's category as a collection of lines.  The first line is the title of the
    /// category, and any extra lines are additional information for it.
    pub fn category(&self) -> &'static str {
        self.category
    }

    /// Gets the callable's textual description as a collection of lines.  The first line is the
    /// summary of the callable's purpose.
    pub fn description(&self) -> Lines<'static> {
        self.description.lines()
    }
}

/// A trait to define a function that is executed by a `Machine`.
///
/// The functions themselves are, for now, pure.  They can only access their input arguments and
/// cannot modify the state of the machine.
///
/// Idiomatically, these objects need to provide a `new()` method that returns an `Rc<Callable>`, as
/// that's the type used throughout the execution engine.
#[async_trait(?Send)]
pub trait Function {
    /// Returns the metadata for this function.
    ///
    /// The return value takes the form of a reference to force the callable to store the metadata
    /// as a struct field so that calls to this function are guaranteed to be cheap.
    fn metadata(&self) -> &CallableMetadata;

    /// Executes the function.
    ///
    /// `span` contains the details about the function call.  The arguments within the span are
    /// unevaluated as provided in the invocation of the function.  These are needed to support
    /// functions that need unevaluated symbol references (such as `LBOUND(array)`).  Because most
    /// functions don't support this kind of input, they should use `eval::eval_all` to process all
    /// arguments.
    ///
    /// `symbols` provides mutable access to the current state of the machine's symbols.
    async fn exec(&self, args: &FunctionCallSpan, symbols: &mut Symbols) -> FunctionResult;
}

/// A trait to define a command that is executed by a `Machine`.
///
/// The commands themselves are immutable but they can reference mutable state.  Given that
/// EndBASIC is not threaded, it is sufficient for those references to be behind a `RefCell`
/// and/or an `Rc`.
///
/// Idiomatically, these objects need to provide a `new()` method that returns an `Rc<Callable>`, as
/// that's the type used throughout the execution engine.
#[async_trait(?Send)]
pub trait Command {
    /// Returns the metadata for this command.
    ///
    /// The return value takes the form of a reference to force the callable to store the metadata
    /// as a struct field so that calls to this function are guaranteed to be cheap.
    fn metadata(&self) -> &CallableMetadata;

    /// Executes the command.
    ///
    /// `span` contains the details about the command invocation.
    /// `machine` provides mutable access to the current state of the machine invoking the command.
    ///
    /// Commands cannot return any value except for errors.
    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::VarRef;
    use crate::testutils::*;

    #[test]
    fn test_array_unidimensional_ok() {
        let mut array = Array::new(VarType::Integer, vec![5]);
        assert_eq!(VarType::Integer, array.subtype());

        array.assign(&[1], 5.into()).unwrap();
        array.assign(&[4], 8.into()).unwrap();
        assert_eq!(&Value::Integer(0), array.index(&[0]).unwrap());
        assert_eq!(&Value::Integer(5), array.index(&[1]).unwrap());
        assert_eq!(&Value::Integer(0), array.index(&[2]).unwrap());
        assert_eq!(&Value::Integer(0), array.index(&[3]).unwrap());
        assert_eq!(&Value::Integer(8), array.index(&[4]).unwrap());
    }

    #[test]
    fn test_array_unidimensional_errors() {
        let mut array = Array::new(VarType::Integer, vec![5]);

        assert_eq!(
            "Cannot index array with 0 subscripts; need 1",
            format!("{}", array.assign(&[], Value::Integer(1)).unwrap_err())
        );
        assert_eq!(
            "Cannot index array with 0 subscripts; need 1",
            format!("{}", array.index(&[]).unwrap_err())
        );

        assert_eq!(
            "Cannot index array with 2 subscripts; need 1",
            format!("{}", array.assign(&[1, 2], Value::Integer(1)).unwrap_err())
        );
        assert_eq!(
            "Cannot index array with 2 subscripts; need 1",
            format!("{}", array.index(&[1, 2]).unwrap_err())
        );

        assert_eq!(
            "Subscript -1 cannot be negative",
            format!("{}", array.assign(&[-1], Value::Integer(1)).unwrap_err())
        );
        assert_eq!(
            "Subscript -1 cannot be negative",
            format!("{}", array.index(&[-1]).unwrap_err())
        );

        assert_eq!(
            "Subscript 6 exceeds limit of 5",
            format!("{}", array.assign(&[6], Value::Integer(1)).unwrap_err())
        );
        assert_eq!("Subscript 6 exceeds limit of 5", format!("{}", array.index(&[6]).unwrap_err()));

        assert_eq!(
            "Cannot assign value of type STRING to array of type INTEGER",
            format!("{}", array.assign(&[0], Value::Text("a".to_owned())).unwrap_err())
        );
    }

    #[test]
    fn test_array_bidimensional_ok() {
        let mut array = Array::new(VarType::Double, vec![2, 3]);
        assert_eq!(VarType::Double, array.subtype());

        array.assign(&[0, 1], 9.1.into()).unwrap();
        array.assign(&[1, 0], 8.1.into()).unwrap();
        array.assign(&[1, 2], 7.1.into()).unwrap();
        assert_eq!(&Value::Double(0.0), array.index(&[0, 0]).unwrap());
        assert_eq!(&Value::Double(9.1), array.index(&[0, 1]).unwrap());
        assert_eq!(&Value::Double(0.0), array.index(&[0, 2]).unwrap());
        assert_eq!(&Value::Double(8.1), array.index(&[1, 0]).unwrap());
        assert_eq!(&Value::Double(0.0), array.index(&[1, 1]).unwrap());
        assert_eq!(&Value::Double(7.1), array.index(&[1, 2]).unwrap());
    }

    #[test]
    fn test_array_bidimensional_errors() {
        let mut array = Array::new(VarType::Integer, vec![5, 2]);

        assert_eq!(
            "Cannot index array with 0 subscripts; need 2",
            format!("{}", array.assign(&[], Value::Integer(1)).unwrap_err())
        );
        assert_eq!(
            "Cannot index array with 0 subscripts; need 2",
            format!("{}", array.index(&[]).unwrap_err())
        );

        assert_eq!(
            "Cannot index array with 1 subscripts; need 2",
            format!("{}", array.assign(&[1], Value::Integer(1)).unwrap_err())
        );
        assert_eq!(
            "Cannot index array with 1 subscripts; need 2",
            format!("{}", array.index(&[1]).unwrap_err())
        );

        assert_eq!(
            "Subscript -1 cannot be negative",
            format!("{}", array.assign(&[-1, 1], Value::Integer(1)).unwrap_err())
        );
        assert_eq!(
            "Subscript -1 cannot be negative",
            format!("{}", array.index(&[-1, 1]).unwrap_err())
        );

        assert_eq!(
            "Subscript -1 cannot be negative",
            format!("{}", array.assign(&[1, -1], Value::Integer(1)).unwrap_err())
        );
        assert_eq!(
            "Subscript -1 cannot be negative",
            format!("{}", array.index(&[1, -1]).unwrap_err())
        );

        assert_eq!(
            "Subscript 2 exceeds limit of 2",
            format!("{}", array.assign(&[-1, 2], Value::Integer(1)).unwrap_err())
        );
        assert_eq!(
            "Subscript 2 exceeds limit of 2",
            format!("{}", array.index(&[-1, 2]).unwrap_err())
        );

        assert_eq!(
            "Cannot assign value of type STRING to array of type INTEGER",
            format!("{}", array.assign(&[0, 0], Value::Text("a".to_owned())).unwrap_err())
        );
    }

    #[test]
    fn test_array_multidimensional() {
        let mut array = Array::new(VarType::Integer, vec![2, 4, 3, 5]);
        assert_eq!(VarType::Integer, array.subtype());

        // First initialize the array with sequential numbers and check that they are valid
        // immediately after assignment.
        let mut n = 0;
        for i in 0..2 {
            for j in 0..4 {
                for k in 0..3 {
                    for l in 0..5 {
                        array.assign(&[i, j, k, l], n.into()).unwrap();
                        assert_eq!(&Value::Integer(n), array.index(&[i, j, k, l]).unwrap());
                        n += 1;
                    }
                }
            }
        }

        // But then also iterate over them all to ensure none were overwritten.
        let mut n = 0;
        for i in 0..2 {
            for j in 0..4 {
                for k in 0..3 {
                    for l in 0..5 {
                        assert_eq!(&Value::Integer(n), array.index(&[i, j, k, l]).unwrap());
                        n += 1;
                    }
                }
            }
        }
    }

    #[test]
    fn test_array_integer_to_double() {
        let mut array = Array::new(VarType::Double, vec![1]);
        array.assign(&[0], Value::Integer(3)).unwrap();
        assert_eq!(&Value::Double(3.0), array.index(&[0]).unwrap());
    }

    #[test]
    fn test_array_double_to_integer() {
        let mut array = Array::new(VarType::Integer, vec![3]);
        array.assign(&[0], Value::Double(5.4)).unwrap();
        array.assign(&[1], Value::Double(5.5)).unwrap();
        array.assign(&[2], Value::Double(5.6)).unwrap();
        assert_eq!(&Value::Integer(5), array.index(&[0]).unwrap());
        assert_eq!(&Value::Integer(6), array.index(&[1]).unwrap());
        assert_eq!(&Value::Integer(6), array.index(&[2]).unwrap());
    }

    #[test]
    fn test_symbols_clear() {
        let mut syms = SymbolsBuilder::default()
            .add_array("SOMEARRAY", VarType::Integer)
            .add_command(ExitCommand::new())
            .add_function(SumFunction::new())
            .add_var("SOMEVAR", Value::Boolean(true))
            .add_var("__SYSTEM_VAR", Value::Integer(42))
            .build();

        assert!(syms.get(&VarRef::new("SOMEARRAY", VarType::Auto)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("EXIT", VarType::Auto)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("SUM", VarType::Auto)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("SOMEVAR", VarType::Auto)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("__SYSTEM_VAR", VarType::Auto)).unwrap().is_some());
        syms.clear();
        assert!(syms.get(&VarRef::new("SOMEARRAY", VarType::Auto)).unwrap().is_none());
        assert!(syms.get(&VarRef::new("EXIT", VarType::Auto)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("SUM", VarType::Auto)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("SOMEVAR", VarType::Auto)).unwrap().is_none());
        assert!(syms.get(&VarRef::new("__SYSTEM_VAR", VarType::Auto)).unwrap().is_some());
    }

    #[test]
    fn test_symbols_dim_ok() {
        let mut syms = Symbols::default();

        syms.dim("a_boolean", VarType::Boolean).unwrap();
        match syms.get(&VarRef::new("a_boolean", VarType::Auto)).unwrap().unwrap() {
            Symbol::Variable(value) => assert_eq!(&Value::Boolean(false), value),
            _ => panic!("Got something that is not the variable we asked for"),
        }

        syms.dim("a_double", VarType::Double).unwrap();
        match syms.get(&VarRef::new("a_double", VarType::Auto)).unwrap().unwrap() {
            Symbol::Variable(value) => assert_eq!(&Value::Double(0.0), value),
            _ => panic!("Got something that is not the variable we asked for"),
        }

        syms.dim("an_integer", VarType::Integer).unwrap();
        match syms.get(&VarRef::new("an_integer", VarType::Auto)).unwrap().unwrap() {
            Symbol::Variable(value) => assert_eq!(&Value::Integer(0), value),
            _ => panic!("Got something that is not the variable we asked for"),
        }

        syms.dim("a_string", VarType::Text).unwrap();
        match syms.get(&VarRef::new("a_string", VarType::Auto)).unwrap().unwrap() {
            Symbol::Variable(value) => assert_eq!(&Value::Text("".to_owned()), value),
            _ => panic!("Got something that is not the variable we asked for"),
        }
    }

    #[test]
    fn test_symbols_dim_name_overlap() {
        let mut syms = SymbolsBuilder::default()
            .add_array("SOMEARRAY", VarType::Integer)
            .add_command(ExitCommand::new())
            .add_function(SumFunction::new())
            .add_var("SOMEVAR", Value::Boolean(true))
            .build();

        assert_eq!(
            "Cannot DIM already-defined symbol Exit",
            format!("{}", syms.dim("Exit", VarType::Integer).unwrap_err())
        );

        assert_eq!(
            "Cannot DIM already-defined symbol Sum",
            format!("{}", syms.dim("Sum", VarType::Integer).unwrap_err())
        );

        assert_eq!(
            "Cannot DIM already-defined symbol SomeVar",
            format!("{}", syms.dim("SomeVar", VarType::Integer).unwrap_err())
        );

        assert_eq!(
            "Cannot DIM already-defined symbol SomeArray",
            format!("{}", syms.dim("SomeArray", VarType::Integer).unwrap_err())
        );
    }

    fn assert_same_array_shape(exp_subtype: VarType, exp_dims: &[usize], symbol: &Symbol) {
        match symbol {
            Symbol::Array(array) => {
                assert_eq!(exp_subtype, array.subtype());
                assert_eq!(exp_dims, array.dimensions());
            }
            _ => panic!("Expected array symbol type, got {:?}", symbol),
        }
    }

    #[test]
    fn test_symbols_dim_array_ok() {
        let mut syms = Symbols::default();

        syms.dim_array("a_boolean", VarType::Boolean, vec![1]).unwrap();
        assert_same_array_shape(
            VarType::Boolean,
            &[1],
            syms.get(&VarRef::new("a_boolean", VarType::Auto)).unwrap().unwrap(),
        );

        syms.dim_array("a_double", VarType::Double, vec![5, 10]).unwrap();
        assert_same_array_shape(
            VarType::Double,
            &[5, 10],
            syms.get(&VarRef::new("a_double", VarType::Auto)).unwrap().unwrap(),
        );

        syms.dim_array("an_integer", VarType::Integer, vec![100]).unwrap();
        assert_same_array_shape(
            VarType::Integer,
            &[100],
            syms.get(&VarRef::new("an_integer", VarType::Auto)).unwrap().unwrap(),
        );

        syms.dim_array("a_string", VarType::Text, vec![1, 1]).unwrap();
        assert_same_array_shape(
            VarType::Text,
            &[1, 1],
            syms.get(&VarRef::new("a_string", VarType::Auto)).unwrap().unwrap(),
        );
    }

    #[test]
    fn test_symbols_dim_array_name_overlap() {
        let mut syms = SymbolsBuilder::default()
            .add_array("SOMEARRAY", VarType::Integer)
            .add_command(ExitCommand::new())
            .add_function(SumFunction::new())
            .add_var("SOMEVAR", Value::Boolean(true))
            .build();

        assert_eq!(
            "Cannot DIM already-defined symbol Exit",
            format!("{}", syms.dim_array("Exit", VarType::Integer, vec![5]).unwrap_err())
        );

        assert_eq!(
            "Cannot DIM already-defined symbol Sum",
            format!("{}", syms.dim_array("Sum", VarType::Integer, vec![5]).unwrap_err())
        );

        assert_eq!(
            "Cannot DIM already-defined symbol SomeVar",
            format!("{}", syms.dim_array("SomeVar", VarType::Integer, vec![5]).unwrap_err())
        );

        assert_eq!(
            "Cannot DIM already-defined symbol SomeArray",
            format!("{}", syms.dim_array("SomeArray", VarType::Integer, vec![5]).unwrap_err())
        );
    }

    #[test]
    fn test_symbols_get_check_types() {
        // If modifying this test, update the identical test for get_auto() and get_mut().
        let syms = SymbolsBuilder::default()
            .add_array("BOOL_ARRAY", VarType::Boolean)
            .add_command(ExitCommand::new())
            .add_function(SumFunction::new())
            .add_var("STRING_VAR", Value::Text("".to_owned()))
            .build();

        for ref_type in &[VarType::Auto, VarType::Boolean] {
            match syms.get(&VarRef::new("bool_array", *ref_type)).unwrap().unwrap() {
                Symbol::Array(array) => assert_eq!(VarType::Boolean, array.subtype()),
                _ => panic!("Got something that is not the array we asked for"),
            }
        }
        assert_eq!(
            "Incompatible types in bool_array$ reference",
            format!("{}", syms.get(&VarRef::new("bool_array", VarType::Text)).unwrap_err())
        );

        match syms.get(&VarRef::new("exit", VarType::Auto)).unwrap().unwrap() {
            Symbol::Command(c) => assert_eq!(VarType::Void, c.metadata().return_type()),
            _ => panic!("Got something that is not the command we asked for"),
        }
        assert_eq!(
            "Incompatible types in exit# reference",
            format!("{}", syms.get(&VarRef::new("exit", VarType::Double)).unwrap_err())
        );

        for ref_type in &[VarType::Auto, VarType::Integer] {
            match syms.get(&VarRef::new("sum", *ref_type)).unwrap().unwrap() {
                Symbol::Function(f) => assert_eq!(VarType::Integer, f.metadata().return_type()),
                _ => panic!("Got something that is not the function we asked for"),
            }
        }
        assert_eq!(
            "Incompatible types in sum# reference",
            format!("{}", syms.get(&VarRef::new("sum", VarType::Double)).unwrap_err())
        );

        for ref_type in &[VarType::Auto, VarType::Text] {
            match syms.get(&VarRef::new("string_var", *ref_type)).unwrap().unwrap() {
                Symbol::Variable(value) => assert_eq!(VarType::Text, value.as_vartype()),
                _ => panic!("Got something that is not the variable we asked for"),
            }
        }
        assert_eq!(
            "Incompatible types in string_var% reference",
            format!("{}", syms.get(&VarRef::new("string_var", VarType::Integer)).unwrap_err())
        );
    }

    #[test]
    fn test_symbols_get_case_insensitivity() {
        // If modifying this test, update the identical test for get_auto() and get_mut().
        let syms = SymbolsBuilder::default()
            .add_array("SOMEARRAY", VarType::Integer)
            .add_command(ExitCommand::new())
            .add_function(SumFunction::new())
            .add_var("SOMEVAR", Value::Boolean(true))
            .build();

        assert!(syms.get(&VarRef::new("somearray", VarType::Auto)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("SomeArray", VarType::Auto)).unwrap().is_some());

        assert!(syms.get(&VarRef::new("exit", VarType::Auto)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("Exit", VarType::Auto)).unwrap().is_some());

        assert!(syms.get(&VarRef::new("sum", VarType::Auto)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("Sum", VarType::Auto)).unwrap().is_some());

        assert!(syms.get(&VarRef::new("somevar", VarType::Auto)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("SomeVar", VarType::Auto)).unwrap().is_some());
    }

    #[test]
    fn test_symbols_get_undefined() {
        // If modifying this test, update the identical test for get_auto() and get_mut().
        let syms = SymbolsBuilder::default().add_var("SOMETHING", Value::Integer(3)).build();
        assert!(syms.get(&VarRef::new("SOME_THIN", VarType::Integer)).unwrap().is_none());
    }

    #[test]
    fn test_symbols_get_mut_check_types() {
        // If modifying this test, update the identical test for get() and get_auto().
        let mut syms = SymbolsBuilder::default()
            .add_array("BOOL_ARRAY", VarType::Boolean)
            .add_command(ExitCommand::new())
            .add_function(SumFunction::new())
            .add_var("STRING_VAR", Value::Text("".to_owned()))
            .build();

        for ref_type in &[VarType::Auto, VarType::Boolean] {
            match syms.get_mut(&VarRef::new("bool_array", *ref_type)).unwrap().unwrap() {
                Symbol::Array(array) => assert_eq!(VarType::Boolean, array.subtype()),
                _ => panic!("Got something that is not the array we asked for"),
            }
        }
        assert_eq!(
            "Incompatible types in bool_array$ reference",
            format!("{}", syms.get_mut(&VarRef::new("bool_array", VarType::Text)).unwrap_err())
        );

        match syms.get_mut(&VarRef::new("exit", VarType::Auto)).unwrap().unwrap() {
            Symbol::Command(c) => assert_eq!(VarType::Void, c.metadata().return_type()),
            _ => panic!("Got something that is not the command we asked for"),
        }
        assert_eq!(
            "Incompatible types in exit# reference",
            format!("{}", syms.get_mut(&VarRef::new("exit", VarType::Double)).unwrap_err())
        );

        for ref_type in &[VarType::Auto, VarType::Integer] {
            match syms.get_mut(&VarRef::new("sum", *ref_type)).unwrap().unwrap() {
                Symbol::Function(f) => assert_eq!(VarType::Integer, f.metadata().return_type()),
                _ => panic!("Got something that is not the function we asked for"),
            }
        }
        assert_eq!(
            "Incompatible types in sum# reference",
            format!("{}", syms.get_mut(&VarRef::new("sum", VarType::Double)).unwrap_err())
        );

        for ref_type in &[VarType::Auto, VarType::Text] {
            match syms.get_mut(&VarRef::new("string_var", *ref_type)).unwrap().unwrap() {
                Symbol::Variable(value) => assert_eq!(VarType::Text, value.as_vartype()),
                _ => panic!("Got something that is not the variable we asked for"),
            }
        }
        assert_eq!(
            "Incompatible types in string_var% reference",
            format!("{}", syms.get_mut(&VarRef::new("string_var", VarType::Integer)).unwrap_err())
        );
    }

    #[test]
    fn test_symbols_get_mut_case_insensitivity() {
        // If modifying this test, update the identical test for get() and get_auto().
        let mut syms = SymbolsBuilder::default()
            .add_array("SOMEARRAY", VarType::Integer)
            .add_command(ExitCommand::new())
            .add_function(SumFunction::new())
            .add_var("SOMEVAR", Value::Boolean(true))
            .build();

        assert!(syms.get_mut(&VarRef::new("somearray", VarType::Auto)).unwrap().is_some());
        assert!(syms.get_mut(&VarRef::new("SomeArray", VarType::Auto)).unwrap().is_some());

        assert!(syms.get_mut(&VarRef::new("exit", VarType::Auto)).unwrap().is_some());
        assert!(syms.get_mut(&VarRef::new("Exit", VarType::Auto)).unwrap().is_some());

        assert!(syms.get_mut(&VarRef::new("sum", VarType::Auto)).unwrap().is_some());
        assert!(syms.get_mut(&VarRef::new("Sum", VarType::Auto)).unwrap().is_some());

        assert!(syms.get_mut(&VarRef::new("somevar", VarType::Auto)).unwrap().is_some());
        assert!(syms.get_mut(&VarRef::new("SomeVar", VarType::Auto)).unwrap().is_some());
    }

    #[test]
    fn test_symbols_get_mut_undefined() {
        // If modifying this test, update the identical test for get() and get_auto().
        let mut syms = SymbolsBuilder::default().add_var("SOMETHING", Value::Integer(3)).build();
        assert!(syms.get_mut(&VarRef::new("SOME_THIN", VarType::Integer)).unwrap().is_none());
    }

    #[test]
    fn test_symbols_get_auto() {
        // If modifying this test, update the identical test for get() and get_mut().
        let syms = SymbolsBuilder::default()
            .add_array("BOOL_ARRAY", VarType::Boolean)
            .add_command(ExitCommand::new())
            .add_function(SumFunction::new())
            .add_var("STRING_VAR", Value::Text("".to_owned()))
            .build();

        match syms.get_auto("bool_array").unwrap() {
            Symbol::Array(array) => assert_eq!(VarType::Boolean, array.subtype()),
            _ => panic!("Got something that is not the array we asked for"),
        }

        match syms.get_auto("exit").unwrap() {
            Symbol::Command(c) => assert_eq!(VarType::Void, c.metadata().return_type()),
            _ => panic!("Got something that is not the command we asked for"),
        }

        match syms.get_auto("sum").unwrap() {
            Symbol::Function(f) => assert_eq!(VarType::Integer, f.metadata().return_type()),
            _ => panic!("Got something that is not the function we asked for"),
        }

        match syms.get_auto("string_var").unwrap() {
            Symbol::Variable(value) => assert_eq!(VarType::Text, value.as_vartype()),
            _ => panic!("Got something that is not the variable we asked for"),
        }
    }

    #[test]
    fn test_symbols_get_auto_case_insensitivity() {
        // If modifying this test, update the identical test for get() and get_mut().
        let syms = SymbolsBuilder::default()
            .add_array("SOMEARRAY", VarType::Integer)
            .add_command(ExitCommand::new())
            .add_function(SumFunction::new())
            .add_var("SOMEVAR", Value::Boolean(true))
            .build();

        assert!(syms.get_auto("somearray").is_some());
        assert!(syms.get_auto("SomeArray").is_some());

        assert!(syms.get_auto("exit").is_some());
        assert!(syms.get_auto("Exit").is_some());

        assert!(syms.get_auto("sum").is_some());
        assert!(syms.get_auto("Sum").is_some());

        assert!(syms.get_auto("somevar").is_some());
        assert!(syms.get_auto("SomeVar").is_some());
    }

    #[test]
    fn test_symbols_get_auto_undefined() {
        // If modifying this test, update the identical test for get() and get_mut().
        let syms = SymbolsBuilder::default().add_var("SOMETHING", Value::Integer(3)).build();
        assert!(syms.get_auto("SOME_THIN").is_none());
    }

    #[test]
    fn test_symbols_qualify_varref() {
        let syms = SymbolsBuilder::default().add_array("V", VarType::Boolean).build();

        assert_eq!(
            VarRef::new("v", VarType::Boolean),
            syms.qualify_varref(&VarRef::new("v", VarType::Auto)).unwrap(),
        );
        assert_eq!(
            VarRef::new("v", VarType::Boolean),
            syms.qualify_varref(&VarRef::new("v", VarType::Boolean)).unwrap(),
        );
        assert_eq!(
            "Incompatible types in v% reference",
            format!("{}", syms.qualify_varref(&VarRef::new("v", VarType::Integer)).unwrap_err()),
        );

        assert_eq!(
            VarRef::new("undefined", VarType::Auto),
            syms.qualify_varref(&VarRef::new("undefined", VarType::Auto)).unwrap(),
        );
        assert_eq!(
            VarRef::new("undefined", VarType::Text),
            syms.qualify_varref(&VarRef::new("undefined", VarType::Text)).unwrap(),
        );
    }

    /// Checks that the variable `name` in `syms` has the value in `exp_value`.
    fn check_var(syms: &Symbols, name: &str, exp_value: Value) {
        match syms.get(&VarRef::new(name, VarType::Auto)).unwrap().unwrap() {
            Symbol::Variable(value) => assert_eq!(exp_value, *value),
            _ => panic!("Got something that is not the variable we asked for"),
        }
    }

    #[test]
    fn test_symbols_set_var_new_check_types_ok() {
        for value in [
            Value::Boolean(true),
            Value::Double(3.4),
            Value::Integer(5),
            Value::Text("a".to_owned()),
        ] {
            let mut syms = Symbols::default();
            syms.set_var(&VarRef::new("a", VarType::Auto), value.clone()).unwrap();
            check_var(&syms, "a", value.clone());
            syms.set_var(&VarRef::new("v", value.as_vartype()), value.clone()).unwrap();
            check_var(&syms, "v", value);
        }
    }

    #[test]
    fn test_symbols_set_var_new_check_types_incompatible() {
        let mut syms = Symbols::default();
        assert_eq!(
            "Cannot assign value of type BOOLEAN to variable of type INTEGER",
            format!(
                "{}",
                syms.set_var(&VarRef::new("v", VarType::Integer), Value::Boolean(false))
                    .unwrap_err()
            )
        );
    }

    #[test]
    fn test_symbols_set_var_new_integer_to_double() {
        let mut syms = Symbols::default();
        syms.set_var(&VarRef::new("v", VarType::Double), Value::Integer(3)).unwrap();
        check_var(&syms, "v", Value::Double(3.0));
    }

    #[test]
    fn test_symbols_set_var_new_double_to_integer() {
        for (expected, actual) in [(4, 4.4), (5, 4.5), (5, 4.6)] {
            let mut syms = Symbols::default();
            syms.set_var(&VarRef::new("v", VarType::Integer), Value::Double(actual)).unwrap();
            check_var(&syms, "v", Value::Integer(expected));
        }
    }

    #[test]
    fn test_symbols_set_var_existing_check_types_ok() {
        for value in [
            Value::Boolean(true),
            Value::Double(3.4),
            Value::Integer(5),
            Value::Text("a".to_owned()),
        ] {
            let mut syms = SymbolsBuilder::default()
                .add_var("A", value.clone())
                .add_var("V", value.clone())
                .build();
            syms.set_var(&VarRef::new("a", VarType::Auto), value.clone()).unwrap();
            check_var(&syms, "a", value.clone());
            syms.set_var(&VarRef::new("v", value.as_vartype()), value.clone()).unwrap();
            check_var(&syms, "v", value);
        }
    }

    #[test]
    fn test_symbols_set_var_existing_check_types_incompatible() {
        let mut syms = SymbolsBuilder::default().add_var("V", Value::Double(10.0)).build();
        assert_eq!(
            "Cannot assign value of type BOOLEAN to variable of type DOUBLE",
            format!(
                "{}",
                syms.set_var(&VarRef::new("v", VarType::Auto), Value::Boolean(true)).unwrap_err()
            )
        );
    }

    #[test]
    fn test_symbols_set_existing_integer_to_double() {
        let mut syms = SymbolsBuilder::default()
            .add_var("A", Value::Double(1.0))
            .add_var("V", Value::Double(1.0))
            .build();
        syms.set_var(&VarRef::new("a", VarType::Auto), Value::Integer(3)).unwrap();
        syms.set_var(&VarRef::new("v", VarType::Double), Value::Integer(3)).unwrap();
        check_var(&syms, "a", Value::Double(3.0));
        check_var(&syms, "v", Value::Double(3.0));
    }

    #[test]
    fn test_symbols_set_existing_double_to_integer() {
        for (expected, actual) in [(4, 4.4), (5, 4.5), (5, 4.6)] {
            let mut syms = SymbolsBuilder::default()
                .add_var("A", Value::Integer(1))
                .add_var("V", Value::Integer(1))
                .build();
            syms.set_var(&VarRef::new("a", VarType::Auto), Value::Double(actual)).unwrap();
            syms.set_var(&VarRef::new("v", VarType::Integer), Value::Double(actual)).unwrap();
            check_var(&syms, "a", Value::Integer(expected));
            check_var(&syms, "v", Value::Integer(expected));
        }
    }

    #[test]
    fn test_symbols_set_var_name_overlap() {
        let mut syms = SymbolsBuilder::default()
            .add_array("SOMEARRAY", VarType::Integer)
            .add_command(ExitCommand::new())
            .add_function(SumFunction::new())
            .add_var("SOMEVAR", Value::Boolean(true))
            .build();

        assert_eq!(
            "Cannot redefine Exit as a variable",
            format!(
                "{}",
                syms.set_var(&VarRef::new("Exit", VarType::Auto), Value::Integer(1)).unwrap_err()
            )
        );

        assert_eq!(
            "Cannot redefine Sum% as a variable",
            format!(
                "{}",
                syms.set_var(&VarRef::new("Sum", VarType::Integer), Value::Integer(1)).unwrap_err()
            )
        );

        assert_eq!(
            "Cannot redefine SomeArray% as a variable",
            format!(
                "{}",
                syms.set_var(&VarRef::new("SomeArray", VarType::Integer), Value::Integer(1))
                    .unwrap_err()
            )
        );

        assert_eq!(
            "Incompatible types in SomeArray$ reference",
            format!(
                "{}",
                syms.set_var(&VarRef::new("SomeArray", VarType::Text), Value::Integer(1))
                    .unwrap_err()
            )
        );
    }

    #[test]
    fn test_symbols_get_var_set_var_case_insensitivity() {
        let mut syms = Symbols::default();
        syms.set_var(&VarRef::new("SomeName", VarType::Auto), Value::Integer(6)).unwrap();
        assert_eq!(
            Value::Integer(6),
            *syms.get_var(&VarRef::new("somename", VarType::Auto)).unwrap()
        );
    }

    #[test]
    fn test_symbols_get_var_set_var_replace_value() {
        let mut syms = Symbols::default();
        syms.set_var(&VarRef::new("the_var", VarType::Auto), Value::Integer(100)).unwrap();
        assert_eq!(
            Value::Integer(100),
            *syms.get_var(&VarRef::new("the_var", VarType::Auto)).unwrap()
        );
        syms.set_var(&VarRef::new("the_var", VarType::Auto), Value::Integer(200)).unwrap();
        assert_eq!(
            Value::Integer(200),
            *syms.get_var(&VarRef::new("the_var", VarType::Auto)).unwrap()
        );
    }

    #[test]
    fn test_symbols_get_var_undefined_error() {
        let syms = SymbolsBuilder::default().add_var("SOMETHING", Value::Integer(3)).build();
        assert_eq!(
            "Undefined variable SOME_THIN",
            format!("{}", syms.get_var(&VarRef::new("SOME_THIN", VarType::Integer)).unwrap_err())
        );
    }
}
