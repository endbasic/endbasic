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

use crate::ast::{ExprType, Value, VarRef};
use crate::compiler::{self, CallableSyntax, RepeatedSyntax, SingularArgSyntax};
use crate::exec::{Machine, Scope};
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
    EvalError(LineCol, String),

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

impl From<io::Error> for CallError {
    fn from(e: io::Error) -> Self {
        Self::IoError(e)
    }
}

impl From<compiler::Error> for CallError {
    fn from(value: compiler::Error) -> Self {
        Self::EvalError(value.pos, value.message)
    }
}

/// Result for callable execution return values.
pub type CallResult = std::result::Result<(), CallError>;

/// The key of a symbol in the symbols table.
#[derive(Clone, Debug, Hash, Eq, Ord, PartialEq, PartialOrd)]
pub struct SymbolKey(String);

impl<R: AsRef<str>> From<R> for SymbolKey {
    fn from(value: R) -> Self {
        Self(value.as_ref().to_ascii_uppercase())
    }
}

impl fmt::Display for SymbolKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Represents a multidimensional array.
#[derive(Clone, Debug, PartialEq)]
pub struct Array {
    /// The type of all elements in the array.
    subtype: ExprType,

    /// The dimensions of the array.  At least one must be present.
    dimensions: Vec<usize>,

    /// The values in the array, flattened.  Given dimensions `(N, M, O)`, an element `(i, j, k)` is
    /// at position `i * (M * O) + j * O + k`.
    values: Vec<Value>,
}

impl Array {
    /// Creates a new array of the given `subtype` and `dimensions`.
    pub fn new(subtype: ExprType, dimensions: Vec<usize>) -> Self {
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
    pub fn subtype(&self) -> ExprType {
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
        debug_assert_eq!(
            subscripts.len(),
            dimensions.len(),
            "Invalid number of subscripts; guaranteed valid by the compiler"
        );

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
        debug_assert_eq!(
            subscripts.len(),
            self.dimensions.len(),
            "Invalid number of subscripts; guaranteed valid by the compiler"
        );

        debug_assert_eq!(
            value.as_exprtype(),
            self.subtype,
            "Invalid types in assignment; guaranteed valid by the compiler"
        );

        let i = Array::native_index(&self.dimensions, subscripts)?;
        self.values[i] = value;
        Ok(())
    }

    /// Obtains the value contained in the array position indicated by the `subscripts`.
    pub fn index(&self, subscripts: &[i32]) -> Result<&Value> {
        let i = Array::native_index(&self.dimensions, subscripts)?;
        let value = &self.values[i];
        debug_assert!(value.as_exprtype() == self.subtype);
        Ok(value)
    }
}

/// Holds the definition of a symbol.
pub enum Symbol {
    /// An array definition.
    Array(Array),

    /// A callable definition.
    Callable(Rc<dyn Callable>),

    /// A variable definition.
    Variable(Value),
}

impl Symbol {
    /// Returns the type the symbol evaluates as.
    fn eval_type(&self) -> Option<ExprType> {
        match self {
            Symbol::Array(array) => Some(array.subtype()),
            Symbol::Callable(callable) => callable.metadata().return_type(),
            Symbol::Variable(value) => Some(value.as_exprtype()),
        }
    }

    /// Returns the metadata for the symbol, if any.
    pub fn metadata(&self) -> Option<&CallableMetadata> {
        match self {
            Symbol::Array(_) => None,
            Symbol::Callable(callable) => Some(callable.metadata()),
            Symbol::Variable(_) => None,
        }
    }

    /// Returns whether the symbol was defined by the user or not.
    fn user_defined(&self) -> bool {
        match self {
            Symbol::Array(_) => true,
            Symbol::Callable(_) => false,
            Symbol::Variable(_) => true,
        }
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Symbol::Array(array) => write!(f, "Array({:?})", array),
            Symbol::Callable(callable) => write!(f, "Callable({:?})", callable.metadata()),
            Symbol::Variable(value) => write!(f, "Variable({:?})", value),
        }
    }
}

/// Storage for all symbols that exist at runtime.
#[derive(Default)]
pub struct Symbols {
    /// Map of symbol names to their definitions.
    by_name: HashMap<SymbolKey, Symbol>,
}

impl Symbols {
    /// Constructs a symbols object from a flat map of symbol names to their definitions.
    #[cfg(test)]
    pub(crate) fn from(by_name: HashMap<SymbolKey, Symbol>) -> Self {
        Self { by_name }
    }

    /// Registers the given builtin callable.
    ///
    /// Given that callable cannot be defined at runtime, specifying a non-unique name results in
    /// a panic.
    pub fn add_callable(&mut self, callable: Rc<dyn Callable>) {
        let key = SymbolKey::from(callable.metadata().name());
        assert!(!self.by_name.contains_key(&key));
        self.by_name.insert(key.to_owned(), Symbol::Callable(callable));
    }

    /// Returns the mapping of all symbols.
    pub fn as_hashmap(&self) -> &HashMap<SymbolKey, Symbol> {
        &self.by_name
    }

    /// Clears all user-defined symbols.
    pub fn clear(&mut self) {
        self.by_name.retain(|key, symbol| {
            let is_internal = key.0.starts_with(|c: char| c.is_ascii_digit());

            // TODO(jmmv): Preserving symbols that start with __ is a hack that was added to support
            // the already-existing GPIO tests when RUN was changed to issue a CLEAR upfront.  This
            // is undocumented behavior and we should find a nicer way to do this.
            let is_gpio_hack = key.0.starts_with("__");

            is_internal || is_gpio_hack || !symbol.user_defined()
        });
    }

    /// Defines a new variable `key` of type `etype`.  The variable must not yet exist.
    pub fn dim(&mut self, key: SymbolKey, etype: ExprType) {
        let previous = self.by_name.insert(key, Symbol::Variable(etype.default_value()));
        debug_assert!(
            previous.is_none(),
            "Pre-existence of variables is checked at compilation time"
        );
    }

    /// Defines a new array `key` of type `subtype` with `dimensions`.  The array must not yet
    /// exist, and the name may not overlap function or variable names.
    pub fn dim_array(&mut self, key: SymbolKey, subtype: ExprType, dimensions: Vec<usize>) {
        let previous = self.by_name.insert(key, Symbol::Array(Array::new(subtype, dimensions)));
        debug_assert!(
            previous.is_none(),
            "Pre-existence of variables is checked at compilation time"
        );
    }

    /// Obtains the value of a symbol or `None` if it is not defined.
    ///
    /// This is meant to use by the compiler only.  All other users should call `get` instead
    /// to do the necessary runtime validity checks.
    pub(crate) fn load(&self, key: &SymbolKey) -> Option<&Symbol> {
        self.by_name.get(key)
    }

    /// Obtains the value of a symbol or `None` if it is not defined.
    ///
    /// This is meant to use by the compiler only.  All other users should call `get` instead
    /// to do the necessary runtime validity checks.
    pub(crate) fn load_mut(&mut self, key: &SymbolKey) -> Option<&mut Symbol> {
        self.by_name.get_mut(key)
    }

    /// Obtains the value of a symbol or `None` if it is not defined.
    ///
    /// Returns an error if the type annotation in the symbol reference does not match its type.
    pub fn get(&self, vref: &VarRef) -> Result<Option<&Symbol>> {
        let key = SymbolKey::from(vref.name());
        let symbol = self.load(&key);
        if let Some(symbol) = symbol {
            let stype = symbol.eval_type();
            if !vref.accepts_callable(stype) {
                return Err(Error::new(format!("Incompatible types in {} reference", vref)));
            }
        }
        Ok(symbol)
    }

    /// Obtains the value of a symbol or `None` if it is not defined.
    pub fn get_auto(&self, var: &str) -> Option<&Symbol> {
        let key = SymbolKey::from(var);
        self.by_name.get(&key)
    }

    /// Obtains the value of a symbol or `None` if it is not defined.
    ///
    /// Returns an error if the type annotation in the symbol reference does not match its type.
    pub fn get_mut(&mut self, vref: &VarRef) -> Result<Option<&mut Symbol>> {
        match self.by_name.get_mut(&vref.as_symbol_key()) {
            Some(symbol) => {
                let stype = symbol.eval_type();
                if !vref.accepts_callable(stype) {
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
        match self.by_name.get(&vref.as_symbol_key()) {
            Some(symbol) => match vref.ref_type() {
                None => Ok(vref.clone().qualify(symbol.eval_type())),
                _ => {
                    if !vref.accepts_callable(symbol.eval_type()) {
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

    /// Sets the value of a variable without type promotion nor type checking.
    ///
    /// This is meant to use by the compiler only.  All other users should call `set_var` instead
    /// to do the necessary runtime validity checks.
    pub(crate) fn assign(&mut self, key: &SymbolKey, value: Value) {
        match self.by_name.get_mut(key) {
            Some(Symbol::Variable(old_value)) => {
                debug_assert_eq!(
                    mem::discriminant(old_value),
                    mem::discriminant(&value),
                    "Type consistency is validated at compilation time"
                );
                *old_value = value;
            }
            Some(_) => unreachable!("Type consistency is validated at compilation time"),
            None => {
                self.by_name.insert(key.clone(), Symbol::Variable(value));
            }
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
        let key = vref.as_symbol_key();
        let value = value.maybe_cast(vref.ref_type())?;
        match self.get_mut(vref)? {
            Some(Symbol::Variable(old_value)) => {
                let value = value.maybe_cast(Some(old_value.as_exprtype()))?;
                if mem::discriminant(&value) != mem::discriminant(old_value) {
                    return Err(Error::new(format!(
                        "Cannot assign value of type {} to variable of type {}",
                        value.as_exprtype(),
                        old_value.as_exprtype(),
                    )));
                }
                self.assign(&key, value);
                Ok(())
            }
            Some(_) => Err(Error::new(format!("Cannot redefine {} as a variable", vref))),
            None => {
                if let Some(ref_type) = vref.ref_type() {
                    if !vref.accepts(value.as_exprtype()) {
                        return Err(Error::new(format!(
                            "Cannot assign value of type {} to variable of type {}",
                            value.as_exprtype(),
                            ref_type,
                        )));
                    }
                }
                self.by_name.insert(key, Symbol::Variable(value));
                Ok(())
            }
        }
    }

    /// Unsets the symbol `key` irrespective of its type.
    pub fn unset(&mut self, key: &SymbolKey) -> Result<()> {
        match self.by_name.remove(key) {
            Some(_) => Ok(()),
            None => Err(Error::new(format!("{} is not defined", key))),
        }
    }
}

/// Builder pattern for a callable's metadata.
pub struct CallableMetadataBuilder {
    name: &'static str,
    return_type: Option<ExprType>,
    category: Option<&'static str>,
    syntax: Option<String>,
    syntaxes: Vec<CallableSyntax>,
    description: Option<&'static str>,
}

impl CallableMetadataBuilder {
    /// Constructs a new metadata builder with the minimum information necessary.
    ///
    /// All code except tests must populate the whole builder with details.  This is enforced at
    /// construction time, where we only allow some fields to be missing under the test
    /// configuration.
    pub fn new(name: &'static str) -> Self {
        assert!(name == name.to_ascii_uppercase(), "Callable name must be in uppercase");

        Self {
            name,
            return_type: None,
            syntax: None,
            syntaxes: vec![],
            category: None,
            description: None,
        }
    }

    /// Sets the return type of the callable.
    pub fn with_return_type(mut self, return_type: ExprType) -> Self {
        self.return_type = Some(return_type);
        self
    }

    /// Sets the syntax specifications for this callable.
    pub fn with_syntax(
        mut self,
        syntaxes: &'static [(&'static [SingularArgSyntax], Option<&'static RepeatedSyntax>)],
    ) -> Self {
        let syntaxes =
            syntaxes.iter().map(|s| CallableSyntax::new(s.0, s.1)).collect::<Vec<CallableSyntax>>();
        if syntaxes.is_empty() {
            self.syntax = Some("no arguments".to_owned());
        } else if syntaxes.len() == 1 {
            self.syntax = Some(syntaxes.first().unwrap().describe());
        } else {
            self.syntax = Some(
                syntaxes
                    .iter()
                    .map(|syn| format!("<{}>", syn.describe()))
                    .collect::<Vec<String>>()
                    .join(" | "),
            );
        };
        self.syntaxes = syntaxes;
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
        assert!(!self.syntaxes.is_empty(), "All callables must specify a syntax");
        CallableMetadata {
            name: self.name,
            return_type: self.return_type,
            syntax: self.syntax.expect("All callables must specify a syntax"),
            syntaxes: self.syntaxes,
            category: self.category.expect("All callables must specify a category"),
            description: self.description.expect("All callables must specify a description"),
        }
    }

    /// Generates the final `CallableMetadata` object, ensuring the minimal set of values are
    /// present.  Only useful for testing.
    pub fn test_build(mut self) -> CallableMetadata {
        if self.syntaxes.is_empty() {
            self.syntaxes.push(CallableSyntax::new(&[], None));
        }
        CallableMetadata {
            name: self.name,
            return_type: self.return_type,
            syntax: self.syntax.unwrap_or("".to_owned()),
            syntaxes: self.syntaxes,
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
    return_type: Option<ExprType>,
    syntax: String,
    syntaxes: Vec<CallableSyntax>,
    category: &'static str,
    description: &'static str,
}

impl CallableMetadata {
    /// Gets the callable's name, all in uppercase.
    pub fn name(&self) -> &'static str {
        self.name
    }

    /// Gets the callable's return type.
    pub fn return_type(&self) -> Option<ExprType> {
        self.return_type
    }

    /// Gets the callable's syntax specification.
    pub fn syntax(&self) -> &str {
        &self.syntax
    }

    /// Returns the callable's syntax definitions.
    pub(crate) fn syntaxes(&self) -> &[CallableSyntax] {
        &self.syntaxes
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

    /// Returns true if this is a callable that takes no arguments.
    pub fn is_argless(&self) -> bool {
        self.syntax.is_empty()
    }

    /// Returns true if this callable is a function (not a command).
    pub fn is_function(&self) -> bool {
        self.return_type.is_some()
    }
}

/// A trait to define a callable that is executed by a `Machine`.
///
/// The callable themselves are immutable but they can reference mutable state.  Given that
/// EndBASIC is not threaded, it is sufficient for those references to be behind a `RefCell`
/// and/or an `Rc`.
///
/// Idiomatically, these objects need to provide a `new()` method that returns an `Rc<Callable>`, as
/// that's the type used throughout the execution engine.
#[async_trait(?Send)]
pub trait Callable {
    /// Returns the metadata for this function.
    ///
    /// The return value takes the form of a reference to force the callable to store the metadata
    /// as a struct field so that calls to this function are guaranteed to be cheap.
    fn metadata(&self) -> &CallableMetadata;

    /// Executes the function.
    ///
    /// `args` contains the arguments to the function call.
    ///
    /// `machine` provides mutable access to the current state of the machine invoking the function.
    async fn exec(&self, scope: Scope<'_>, machine: &mut Machine) -> CallResult;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{ExprType, VarRef};
    use crate::testutils::*;
    use std::cell::RefCell;

    #[test]
    fn test_array_unidimensional_ok() {
        let mut array = Array::new(ExprType::Integer, vec![5]);
        assert_eq!(ExprType::Integer, array.subtype());

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
        let mut array = Array::new(ExprType::Integer, vec![5]);

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
    }

    #[test]
    fn test_array_bidimensional_ok() {
        let mut array = Array::new(ExprType::Double, vec![2, 3]);
        assert_eq!(ExprType::Double, array.subtype());

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
        let mut array = Array::new(ExprType::Integer, vec![5, 2]);

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
    }

    #[test]
    fn test_array_multidimensional() {
        let mut array = Array::new(ExprType::Integer, vec![2, 4, 3, 5]);
        assert_eq!(ExprType::Integer, array.subtype());

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
    fn test_symbols_clear() {
        let mut syms = SymbolsBuilder::default()
            .add_array("SOMEARRAY", ExprType::Integer)
            .add_callable(OutCommand::new(Rc::from(RefCell::from(vec![]))))
            .add_callable(SumFunction::new())
            .add_var("SOMEVAR", Value::Boolean(true))
            .add_var("__SYSTEM_VAR", Value::Integer(42))
            .build();

        assert!(syms.get(&VarRef::new("SOMEARRAY", None)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("OUT", None)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("SUM", None)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("SOMEVAR", None)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("__SYSTEM_VAR", None)).unwrap().is_some());
        syms.clear();
        assert!(syms.get(&VarRef::new("SOMEARRAY", None)).unwrap().is_none());
        assert!(syms.get(&VarRef::new("OUT", None)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("SUM", None)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("SOMEVAR", None)).unwrap().is_none());
        assert!(syms.get(&VarRef::new("__SYSTEM_VAR", None)).unwrap().is_some());
    }

    #[test]
    fn test_symbols_dim_ok() {
        let mut syms = Symbols::default();

        syms.dim(SymbolKey::from("A_Boolean"), ExprType::Boolean);
        match syms.get(&VarRef::new("a_boolean", None)).unwrap().unwrap() {
            Symbol::Variable(value) => assert_eq!(&Value::Boolean(false), value),
            _ => panic!("Got something that is not the variable we asked for"),
        }
    }

    fn assert_same_array_shape(exp_subtype: ExprType, exp_dims: &[usize], symbol: &Symbol) {
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

        syms.dim_array(SymbolKey::from("A_Boolean"), ExprType::Boolean, vec![1]);
        assert_same_array_shape(
            ExprType::Boolean,
            &[1],
            syms.get(&VarRef::new("a_boolean", None)).unwrap().unwrap(),
        );
    }

    #[test]
    fn test_symbols_get_check_types() {
        // If modifying this test, update the identical test for get_auto() and get_mut().
        let syms = SymbolsBuilder::default()
            .add_array("BOOL_ARRAY", ExprType::Boolean)
            .add_callable(OutCommand::new(Rc::from(RefCell::from(vec![]))))
            .add_callable(SumFunction::new())
            .add_var("STRING_VAR", Value::Text("".to_owned()))
            .build();

        for ref_type in &[None, Some(ExprType::Boolean)] {
            match syms.get(&VarRef::new("bool_array", *ref_type)).unwrap().unwrap() {
                Symbol::Array(array) => assert_eq!(ExprType::Boolean, array.subtype()),
                _ => panic!("Got something that is not the array we asked for"),
            }
        }
        assert_eq!(
            "Incompatible types in bool_array$ reference",
            format!("{}", syms.get(&VarRef::new("bool_array", Some(ExprType::Text))).unwrap_err())
        );

        match syms.get(&VarRef::new("out", None)).unwrap().unwrap() {
            Symbol::Callable(c) => assert_eq!(None, c.metadata().return_type()),
            _ => panic!("Got something that is not the command we asked for"),
        }
        assert_eq!(
            "Incompatible types in out# reference",
            format!("{}", syms.get(&VarRef::new("out", Some(ExprType::Double))).unwrap_err())
        );

        for ref_type in &[None, Some(ExprType::Integer)] {
            match syms.get(&VarRef::new("sum", *ref_type)).unwrap().unwrap() {
                Symbol::Callable(f) => {
                    assert_eq!(Some(ExprType::Integer), f.metadata().return_type())
                }
                _ => panic!("Got something that is not the function we asked for"),
            }
        }
        assert_eq!(
            "Incompatible types in sum# reference",
            format!("{}", syms.get(&VarRef::new("sum", Some(ExprType::Double))).unwrap_err())
        );

        for ref_type in &[None, Some(ExprType::Text)] {
            match syms.get(&VarRef::new("string_var", *ref_type)).unwrap().unwrap() {
                Symbol::Variable(value) => assert_eq!(ExprType::Text, value.as_exprtype()),
                _ => panic!("Got something that is not the variable we asked for"),
            }
        }
        assert_eq!(
            "Incompatible types in string_var% reference",
            format!(
                "{}",
                syms.get(&VarRef::new("string_var", Some(ExprType::Integer))).unwrap_err()
            )
        );
    }

    #[test]
    fn test_symbols_get_case_insensitivity() {
        // If modifying this test, update the identical test for get_auto() and get_mut().
        let syms = SymbolsBuilder::default()
            .add_array("SOMEARRAY", ExprType::Integer)
            .add_callable(OutCommand::new(Rc::from(RefCell::from(vec![]))))
            .add_callable(SumFunction::new())
            .add_var("SOMEVAR", Value::Boolean(true))
            .build();

        assert!(syms.get(&VarRef::new("somearray", None)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("SomeArray", None)).unwrap().is_some());

        assert!(syms.get(&VarRef::new("out", None)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("Out", None)).unwrap().is_some());

        assert!(syms.get(&VarRef::new("sum", None)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("Sum", None)).unwrap().is_some());

        assert!(syms.get(&VarRef::new("somevar", None)).unwrap().is_some());
        assert!(syms.get(&VarRef::new("SomeVar", None)).unwrap().is_some());
    }

    #[test]
    fn test_symbols_get_undefined() {
        // If modifying this test, update the identical test for get_auto() and get_mut().
        let syms = SymbolsBuilder::default().add_var("SOMETHING", Value::Integer(3)).build();
        assert!(syms.get(&VarRef::new("SOME_THIN", Some(ExprType::Integer))).unwrap().is_none());
    }

    #[test]
    fn test_symbols_get_mut_check_types() {
        // If modifying this test, update the identical test for get() and get_auto().
        let mut syms = SymbolsBuilder::default()
            .add_array("BOOL_ARRAY", ExprType::Boolean)
            .add_callable(OutCommand::new(Rc::from(RefCell::from(vec![]))))
            .add_callable(SumFunction::new())
            .add_var("STRING_VAR", Value::Text("".to_owned()))
            .build();

        for ref_type in &[None, Some(ExprType::Boolean)] {
            match syms.get_mut(&VarRef::new("bool_array", *ref_type)).unwrap().unwrap() {
                Symbol::Array(array) => assert_eq!(ExprType::Boolean, array.subtype()),
                _ => panic!("Got something that is not the array we asked for"),
            }
        }
        assert_eq!(
            "Incompatible types in bool_array$ reference",
            format!(
                "{}",
                syms.get_mut(&VarRef::new("bool_array", Some(ExprType::Text))).unwrap_err()
            )
        );

        match syms.get_mut(&VarRef::new("out", None)).unwrap().unwrap() {
            Symbol::Callable(c) => assert_eq!(None, c.metadata().return_type()),
            _ => panic!("Got something that is not the command we asked for"),
        }
        assert_eq!(
            "Incompatible types in out# reference",
            format!("{}", syms.get_mut(&VarRef::new("out", Some(ExprType::Double))).unwrap_err())
        );

        for ref_type in &[None, Some(ExprType::Integer)] {
            match syms.get_mut(&VarRef::new("sum", *ref_type)).unwrap().unwrap() {
                Symbol::Callable(f) => {
                    assert_eq!(Some(ExprType::Integer), f.metadata().return_type())
                }
                _ => panic!("Got something that is not the function we asked for"),
            }
        }
        assert_eq!(
            "Incompatible types in sum# reference",
            format!("{}", syms.get_mut(&VarRef::new("sum", Some(ExprType::Double))).unwrap_err())
        );

        for ref_type in &[None, Some(ExprType::Text)] {
            match syms.get_mut(&VarRef::new("string_var", *ref_type)).unwrap().unwrap() {
                Symbol::Variable(value) => assert_eq!(ExprType::Text, value.as_exprtype()),
                _ => panic!("Got something that is not the variable we asked for"),
            }
        }
        assert_eq!(
            "Incompatible types in string_var% reference",
            format!(
                "{}",
                syms.get_mut(&VarRef::new("string_var", Some(ExprType::Integer))).unwrap_err()
            )
        );
    }

    #[test]
    fn test_symbols_get_mut_case_insensitivity() {
        // If modifying this test, update the identical test for get() and get_auto().
        let mut syms = SymbolsBuilder::default()
            .add_array("SOMEARRAY", ExprType::Integer)
            .add_callable(OutCommand::new(Rc::from(RefCell::from(vec![]))))
            .add_callable(SumFunction::new())
            .add_var("SOMEVAR", Value::Boolean(true))
            .build();

        assert!(syms.get_mut(&VarRef::new("somearray", None)).unwrap().is_some());
        assert!(syms.get_mut(&VarRef::new("SomeArray", None)).unwrap().is_some());

        assert!(syms.get_mut(&VarRef::new("out", None)).unwrap().is_some());
        assert!(syms.get_mut(&VarRef::new("Out", None)).unwrap().is_some());

        assert!(syms.get_mut(&VarRef::new("sum", None)).unwrap().is_some());
        assert!(syms.get_mut(&VarRef::new("Sum", None)).unwrap().is_some());

        assert!(syms.get_mut(&VarRef::new("somevar", None)).unwrap().is_some());
        assert!(syms.get_mut(&VarRef::new("SomeVar", None)).unwrap().is_some());
    }

    #[test]
    fn test_symbols_get_mut_undefined() {
        // If modifying this test, update the identical test for get() and get_auto().
        let mut syms = SymbolsBuilder::default().add_var("SOMETHING", Value::Integer(3)).build();
        assert!(syms
            .get_mut(&VarRef::new("SOME_THIN", Some(ExprType::Integer)))
            .unwrap()
            .is_none());
    }

    #[test]
    fn test_symbols_get_auto() {
        // If modifying this test, update the identical test for get() and get_mut().
        let syms = SymbolsBuilder::default()
            .add_array("BOOL_ARRAY", ExprType::Boolean)
            .add_callable(OutCommand::new(Rc::from(RefCell::from(vec![]))))
            .add_callable(SumFunction::new())
            .add_var("STRING_VAR", Value::Text("".to_owned()))
            .build();

        match syms.get_auto("bool_array").unwrap() {
            Symbol::Array(array) => assert_eq!(ExprType::Boolean, array.subtype()),
            _ => panic!("Got something that is not the array we asked for"),
        }

        match syms.get_auto("out").unwrap() {
            Symbol::Callable(c) => assert_eq!(None, c.metadata().return_type()),
            _ => panic!("Got something that is not the command we asked for"),
        }

        match syms.get_auto("sum").unwrap() {
            Symbol::Callable(f) => assert_eq!(Some(ExprType::Integer), f.metadata().return_type()),
            _ => panic!("Got something that is not the function we asked for"),
        }

        match syms.get_auto("string_var").unwrap() {
            Symbol::Variable(value) => assert_eq!(ExprType::Text, value.as_exprtype()),
            _ => panic!("Got something that is not the variable we asked for"),
        }
    }

    #[test]
    fn test_symbols_get_auto_case_insensitivity() {
        // If modifying this test, update the identical test for get() and get_mut().
        let syms = SymbolsBuilder::default()
            .add_array("SOMEARRAY", ExprType::Integer)
            .add_callable(OutCommand::new(Rc::from(RefCell::from(vec![]))))
            .add_callable(SumFunction::new())
            .add_var("SOMEVAR", Value::Boolean(true))
            .build();

        assert!(syms.get_auto("somearray").is_some());
        assert!(syms.get_auto("SomeArray").is_some());

        assert!(syms.get_auto("out").is_some());
        assert!(syms.get_auto("Out").is_some());

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
        let syms = SymbolsBuilder::default().add_array("V", ExprType::Boolean).build();

        assert_eq!(
            VarRef::new("v", Some(ExprType::Boolean)),
            syms.qualify_varref(&VarRef::new("v", None)).unwrap(),
        );
        assert_eq!(
            VarRef::new("v", Some(ExprType::Boolean)),
            syms.qualify_varref(&VarRef::new("v", Some(ExprType::Boolean))).unwrap(),
        );
        assert_eq!(
            "Incompatible types in v% reference",
            format!(
                "{}",
                syms.qualify_varref(&VarRef::new("v", Some(ExprType::Integer))).unwrap_err()
            ),
        );

        assert_eq!(
            VarRef::new("undefined", None),
            syms.qualify_varref(&VarRef::new("undefined", None)).unwrap(),
        );
        assert_eq!(
            VarRef::new("undefined", Some(ExprType::Text)),
            syms.qualify_varref(&VarRef::new("undefined", Some(ExprType::Text))).unwrap(),
        );
    }

    /// Checks that the variable `name` in `syms` has the value in `exp_value`.
    fn check_var(syms: &Symbols, name: &str, exp_value: Value) {
        match syms.get(&VarRef::new(name, None)).unwrap().unwrap() {
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
            syms.set_var(&VarRef::new("a", None), value.clone()).unwrap();
            check_var(&syms, "a", value.clone());
            syms.set_var(&VarRef::new("v", Some(value.as_exprtype())), value.clone()).unwrap();
            check_var(&syms, "v", value);
        }
    }

    #[test]
    fn test_symbols_apply_new() {
        let mut syms = Symbols::default();
        syms.assign(&SymbolKey::from("a"), Value::Integer(5));
        check_var(&syms, "a", Value::Integer(5));
    }

    #[test]
    fn test_symbols_apply_existing() {
        let mut syms = SymbolsBuilder::default().add_var("A", Value::Double(1.0)).build();
        syms.assign(&SymbolKey::from("a"), Value::Double(2.0));
        check_var(&syms, "a", Value::Double(2.0));
    }

    #[test]
    fn test_symbols_get_var_apply_case_insensitivity() {
        let mut syms = Symbols::default();
        syms.assign(&SymbolKey::from("SomeName"), Value::Integer(6));
        assert_eq!(Value::Integer(6), *syms.get_var(&VarRef::new("somename", None)).unwrap());
    }

    #[test]
    fn test_symbols_get_var_apply_replace_value() {
        let mut syms = Symbols::default();
        syms.assign(&SymbolKey::from("the_var"), Value::Integer(100));
        assert_eq!(Value::Integer(100), *syms.get_var(&VarRef::new("the_var", None)).unwrap());
        syms.assign(&SymbolKey::from("the_var"), Value::Integer(200));
        assert_eq!(Value::Integer(200), *syms.get_var(&VarRef::new("the_var", None)).unwrap());
    }

    #[test]
    fn test_symbols_set_var_new_check_types_incompatible() {
        let mut syms = Symbols::default();
        assert_eq!(
            "Cannot assign value of type BOOLEAN to variable of type INTEGER",
            format!(
                "{}",
                syms.set_var(&VarRef::new("v", Some(ExprType::Integer)), Value::Boolean(false))
                    .unwrap_err()
            )
        );
    }

    #[test]
    fn test_symbols_set_var_new_integer_to_double() {
        let mut syms = Symbols::default();
        syms.set_var(&VarRef::new("v", Some(ExprType::Double)), Value::Integer(3)).unwrap();
        check_var(&syms, "v", Value::Double(3.0));
    }

    #[test]
    fn test_symbols_set_var_new_double_to_integer() {
        for (expected, actual) in [(4, 4.4), (5, 4.5), (5, 4.6)] {
            let mut syms = Symbols::default();
            syms.set_var(&VarRef::new("v", Some(ExprType::Integer)), Value::Double(actual))
                .unwrap();
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
            syms.set_var(&VarRef::new("a", None), value.clone()).unwrap();
            check_var(&syms, "a", value.clone());
            syms.set_var(&VarRef::new("v", Some(value.as_exprtype())), value.clone()).unwrap();
            check_var(&syms, "v", value);
        }
    }

    #[test]
    fn test_symbols_set_var_existing_check_types_incompatible() {
        let mut syms = SymbolsBuilder::default().add_var("V", Value::Double(10.0)).build();
        assert_eq!(
            "Cannot assign value of type BOOLEAN to variable of type DOUBLE",
            format!("{}", syms.set_var(&VarRef::new("v", None), Value::Boolean(true)).unwrap_err())
        );
    }

    #[test]
    fn test_symbols_set_existing_integer_to_double() {
        let mut syms = SymbolsBuilder::default()
            .add_var("A", Value::Double(1.0))
            .add_var("V", Value::Double(1.0))
            .build();
        syms.set_var(&VarRef::new("a", None), Value::Integer(3)).unwrap();
        syms.set_var(&VarRef::new("v", Some(ExprType::Double)), Value::Integer(3)).unwrap();
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
            syms.set_var(&VarRef::new("a", None), Value::Double(actual)).unwrap();
            syms.set_var(&VarRef::new("v", Some(ExprType::Integer)), Value::Double(actual))
                .unwrap();
            check_var(&syms, "a", Value::Integer(expected));
            check_var(&syms, "v", Value::Integer(expected));
        }
    }

    #[test]
    fn test_symbols_set_var_name_overlap() {
        let mut syms = SymbolsBuilder::default()
            .add_array("SOMEARRAY", ExprType::Integer)
            .add_callable(OutCommand::new(Rc::from(RefCell::from(vec![]))))
            .add_callable(SumFunction::new())
            .add_var("SOMEVAR", Value::Boolean(true))
            .build();

        assert_eq!(
            "Cannot redefine Out as a variable",
            format!("{}", syms.set_var(&VarRef::new("Out", None), Value::Integer(1)).unwrap_err())
        );

        assert_eq!(
            "Cannot redefine Sum% as a variable",
            format!(
                "{}",
                syms.set_var(&VarRef::new("Sum", Some(ExprType::Integer)), Value::Integer(1))
                    .unwrap_err()
            )
        );

        assert_eq!(
            "Cannot redefine SomeArray% as a variable",
            format!(
                "{}",
                syms.set_var(&VarRef::new("SomeArray", Some(ExprType::Integer)), Value::Integer(1))
                    .unwrap_err()
            )
        );

        assert_eq!(
            "Incompatible types in SomeArray$ reference",
            format!(
                "{}",
                syms.set_var(&VarRef::new("SomeArray", Some(ExprType::Text)), Value::Integer(1))
                    .unwrap_err()
            )
        );
    }

    #[test]
    fn test_symbols_get_var_set_var_case_insensitivity() {
        let mut syms = Symbols::default();
        syms.set_var(&VarRef::new("SomeName", None), Value::Integer(6)).unwrap();
        assert_eq!(Value::Integer(6), *syms.get_var(&VarRef::new("somename", None)).unwrap());
    }

    #[test]
    fn test_symbols_get_var_set_var_replace_value() {
        let mut syms = Symbols::default();
        syms.set_var(&VarRef::new("the_var", None), Value::Integer(100)).unwrap();
        assert_eq!(Value::Integer(100), *syms.get_var(&VarRef::new("the_var", None)).unwrap());
        syms.set_var(&VarRef::new("the_var", None), Value::Integer(200)).unwrap();
        assert_eq!(Value::Integer(200), *syms.get_var(&VarRef::new("the_var", None)).unwrap());
    }

    #[test]
    fn test_symbols_get_var_undefined_error() {
        let syms = SymbolsBuilder::default().add_var("SOMETHING", Value::Integer(3)).build();
        assert_eq!(
            "Undefined variable SOME_THIN",
            format!(
                "{}",
                syms.get_var(&VarRef::new("SOME_THIN", Some(ExprType::Integer))).unwrap_err()
            )
        );
    }

    #[test]
    fn test_symbols_unset_ok() {
        let mut syms = SymbolsBuilder::default()
            .add_array("SOMEARRAY", ExprType::Integer)
            .add_callable(OutCommand::new(Rc::from(RefCell::from(vec![]))))
            .add_callable(SumFunction::new())
            .add_var("SOMEVAR", Value::Boolean(true))
            .build();

        let mut count = 4;
        for name in ["SomeArray", "Out", "Sum", "SomeVar"] {
            syms.unset(&SymbolKey::from(name)).unwrap();
            count -= 1;
            assert_eq!(count, syms.as_hashmap().len());
        }
        assert_eq!(0, count);
    }

    #[test]
    fn test_symbols_unset_undefined() {
        let mut syms = SymbolsBuilder::default().add_var("SOMETHING", Value::Integer(3)).build();
        syms.unset(&SymbolKey::from("FOO")).unwrap_err();
        assert_eq!(1, syms.as_hashmap().len());
    }
}
