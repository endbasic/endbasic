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

//! Abstract Syntax Tree (AST) for the EndBASIC language.

use crate::parser::{Error, Result};
use std::fmt;

/// Represents an expression and provides mechanisms to evaluate it.
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    /// A literal boolean value.
    Boolean(bool),
    /// A literal double-precision floating point value.
    Double(f64),
    /// A literal integer value.
    Integer(i32),
    /// A reference to a variable.
    Symbol(VarRef),
    /// A literal string value.
    Text(String),

    /// Arithmetic addition of two expressions.
    Add(Box<Expr>, Box<Expr>),
    /// Arithmetic subtraction of two expressions.
    Subtract(Box<Expr>, Box<Expr>),
    /// Arithmetic multiplication of two expressions.
    Multiply(Box<Expr>, Box<Expr>),
    /// Arithmetic division of two expressions.
    Divide(Box<Expr>, Box<Expr>),
    /// Arithmetic modulo operation of two expressions.
    Modulo(Box<Expr>, Box<Expr>),
    /// Arithmetic sign flip of an expression.
    Negate(Box<Expr>),

    /// Relational equality comparison of two expressions.
    Equal(Box<Expr>, Box<Expr>),
    /// Relational inequality comparison of two expressions.
    NotEqual(Box<Expr>, Box<Expr>),
    /// Relational less-than comparison of two expressions.
    Less(Box<Expr>, Box<Expr>),
    /// Relational less-than or equal-to comparison of two expressions.
    LessEqual(Box<Expr>, Box<Expr>),
    /// Relational greater-than comparison of two expressions.
    Greater(Box<Expr>, Box<Expr>),
    /// Relational greater-than or equal-to comparison of two expressions.
    GreaterEqual(Box<Expr>, Box<Expr>),

    /// Logical and of two expressions.
    And(Box<Expr>, Box<Expr>),
    /// Logical not of an expression.
    Not(Box<Expr>),
    /// Logical or of two expressions.
    Or(Box<Expr>, Box<Expr>),
    /// Logical xor of two expressions.
    Xor(Box<Expr>, Box<Expr>),

    /// A function call or an array reference.
    Call(VarRef, Vec<Expr>),
}

/// Collection of types for a variable.
// TODO(jmmv): Consider combining with `Value` and using `Discriminant<Value>` for the variable
// types.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VarType {
    /// Unspecified type identifier.  The type is determined by the value of the variable.
    Auto,

    /// A boolean variable.
    Boolean,

    /// A double-precision floating point variable.
    Double,

    /// An integer variable.
    Integer,

    /// A string variable.  This should really be called `String` but it would get confusing with
    /// the built-in Rust type.
    Text,

    /// The nothingness type.  Used to represent the return value of commands.
    Void,
}

impl VarType {
    /// Returns the type annotation for this type.
    pub fn annotation(&self) -> &'static str {
        match self {
            VarType::Auto => "",
            VarType::Boolean => "?",
            VarType::Double => "#",
            VarType::Integer => "%",
            VarType::Text => "$",
            VarType::Void => "",
        }
    }

    /// Returns the default value to assign to this type.
    pub fn default_value(&self) -> Value {
        match self {
            VarType::Auto => Value::Integer(0),
            VarType::Boolean => Value::Boolean(false),
            VarType::Double => Value::Double(0.0),
            VarType::Integer => Value::Integer(0),
            VarType::Text => Value::Text("".to_owned()),
            VarType::Void => panic!("Cannot represent a default value for void"),
        }
    }
}

/// Represents a reference to a variable (which doesn't have to exist).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VarRef {
    /// Name of the variable this points to.
    name: String,

    /// Type of the variable this points to, if explicitly specified.  If `Auto`, the type of the
    /// variable is only known at runtime based on the values assigned to it.
    ref_type: VarType,
}

// TODO(jmmv): This is the only `impl` in the AST.  Something seems wrong with this.
impl VarRef {
    /// Creates a new reference to the variable with `name` and the optional `vtype` type.
    #[allow(clippy::redundant_field_names)]
    pub fn new<T: Into<String>>(name: T, ref_type: VarType) -> Self {
        Self { name: name.into(), ref_type: ref_type }
    }

    /// Transforms this reference into an unannotated name.
    ///
    /// This is only valid for references that have no annotations in them.
    pub fn into_unannotated_string(self) -> Result<String> {
        if self.ref_type != VarType::Auto {
            return Err(Error::Bad(format!("Type annotation not allowed in {}", self)));
        }
        Ok(self.name)
    }

    /// Returns the name of this reference, without any type annotations.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Adds the type annotation `ref_type` to this reference.
    ///
    /// Assumes that the current annotation for this reference is `Auto` and that the given
    /// annotation is not.
    pub fn qualify(self, ref_type: VarType) -> Self {
        assert!(ref_type != VarType::Auto, "Cannot qualify with auto");
        assert!(self.ref_type == VarType::Auto, "Reference already qualified");
        Self { name: self.name, ref_type }
    }

    /// Returns the type of this reference.
    pub fn ref_type(&self) -> VarType {
        self.ref_type
    }

    /// Returns true if this reference is compatible with the given type.
    pub fn accepts(&self, other: VarType) -> bool {
        self.ref_type == VarType::Auto || self.ref_type == other
    }
}

impl fmt::Display for VarRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.name, self.ref_type().annotation())
    }
}

/// Represents an evaluated value.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    /// A boolean value.
    Boolean(bool),

    /// A double-precision floating point value.
    Double(f64),

    /// An integer value.
    Integer(i32),

    /// A string value.
    Text(String), // Should be `String` but would get confusing with the built-in Rust type.
}

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Value::Boolean(b)
    }
}

impl From<f64> for Value {
    fn from(d: f64) -> Self {
        Value::Double(d)
    }
}

impl From<i32> for Value {
    fn from(i: i32) -> Self {
        Value::Integer(i)
    }
}

impl From<&str> for Value {
    fn from(s: &str) -> Self {
        Value::Text(s.to_owned())
    }
}

impl Value {
    /// Returns the type of the value as a `VarType`.
    pub fn as_vartype(&self) -> VarType {
        match self {
            Value::Boolean(_) => VarType::Boolean,
            Value::Double(_) => VarType::Double,
            Value::Integer(_) => VarType::Integer,
            Value::Text(_) => VarType::Text,
        }
    }
}

/// Types of separators between arguments to a `BuiltinCall`.
#[derive(Debug, Eq, PartialEq)]
pub enum ArgSep {
    /// Filler for the separator in the last argument.
    End,

    /// Short separator (`;`).
    Short,

    /// Long separator (`,`).
    Long,
}

/// Represents a statement in the program along all data to execute it.
#[derive(Debug, PartialEq)]
pub enum Statement {
    /// Represents an assignment to an element of an array.
    ///
    /// The first parameter is the reference to the array to modify.  The second parameter is the
    /// expressions to compute the subscripts to index the array.  the third parameter is the
    /// expression to compute the value of the modified element.
    ArrayAssignment(VarRef, Vec<Expr>, Expr),

    /// Represents a variable assignment.
    ///
    /// The first parameter is the reference to the variable to set.  The second parameter is the
    /// expression to compute the value for the variable.
    Assignment(VarRef, Expr),

    /// Represents a call to a builtin command such as `PRINT`.
    ///
    /// The first parameter is the name of the builtin.  The second parameter is the sequence of
    /// arguments to pass to the builtin.
    ///
    /// Each argument is represented as an optional expression to evaluate and the separator that
    /// was to separate it from the *next* argument.  Because of this, the last argument always
    /// carries `ArgSep::End` as the separator.  The reason the expression is optional is to support
    /// calls of the form `PRINT a, , b`.
    BuiltinCall(String, Vec<(Option<Expr>, ArgSep)>),

    /// Represents a variable declaration.
    ///
    /// The first parameter is the name of the variable to set; type annotations are not allowed.
    /// The second parameter is the type of the variable to be defined.
    ///
    /// Given that a declaration causes the variable to be initialized to a default value, it is
    /// tempting to model this statement as a simple assignment.  However, we must be able to
    /// detect variable redeclarations at runtime, so we must treat this statement as a separate
    /// type from assignments.
    Dim(String, VarType),

    /// Represents an array declaration.
    ///
    /// The first parameter is the name of the array to set; type annotations are not allowed.
    /// The second parameter is the expressions to compute the dimensions of the array.  The third
    /// parameter is the type of the elements in the array.
    DimArray(String, Vec<Expr>, VarType),

    /// Represents an `IF` statement.
    ///
    /// The first and only parameter is a sequence containing all the branches of the statement.
    /// Each element is a pair of the conditional guard for the branch and the collection of
    /// statements in that branch.  The final `ELSE` branch, if present, is also included here
    /// and its guard clause is always a true expression.
    If(Vec<(Expr, Vec<Statement>)>),

    /// Represents a `FOR` statement.
    ///
    /// The first parameter is the loop's iterator name, which is expressed a variable reference
    /// that must be either automatic or an integer.  The second parameter is the expression to
    /// compute the iterator's initial value, which must evaluate to an integer.  The third
    /// parameter is the condition to test after each body execution, which if false terminates the
    /// loop.  The fourth parameter is the expression to compute the iterator's next value.  The
    /// fifth parameter is the collection of statements within the loop.
    ///
    /// Note that we do not store the original end and step values, and instead use expressions to
    /// represent the loop condition and the computation of the next iterator value.  We do this
    /// for run-time efficiency.  The reason this is possible is because we force the step to be an
    /// integer literal at parse time and do not allow it to be an expression.
    For(VarRef, Expr, Expr, Expr, Vec<Statement>),

    /// Represents a `WHILE` statement.
    ///
    /// The first parameter is the loop's condition.  The second parameter is the collection of
    /// statements within the loop.
    While(Expr, Vec<Statement>),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_varref_display() {
        assert_eq!("name", format!("{}", VarRef::new("name", VarType::Auto)));
        assert_eq!("abc?", format!("{}", VarRef::new("abc", VarType::Boolean)));
        assert_eq!("cba#", format!("{}", VarRef::new("cba", VarType::Double)));
        assert_eq!("def%", format!("{}", VarRef::new("def", VarType::Integer)));
        assert_eq!("ghi$", format!("{}", VarRef::new("ghi", VarType::Text)));
    }

    #[test]
    fn test_varref_into_unannotated_string() {
        assert_eq!(
            "print",
            &VarRef::new("print", VarType::Auto).into_unannotated_string().unwrap()
        );

        assert_eq!(
            "Type annotation not allowed in print$",
            format!(
                "{}",
                &VarRef::new("print", VarType::Text).into_unannotated_string().unwrap_err()
            )
        );
    }

    #[test]
    fn test_varref_accepts() {
        assert!(VarRef::new("a", VarType::Auto).accepts(VarType::Boolean));
        assert!(VarRef::new("a", VarType::Auto).accepts(VarType::Double));
        assert!(VarRef::new("a", VarType::Auto).accepts(VarType::Integer));
        assert!(VarRef::new("a", VarType::Auto).accepts(VarType::Text));

        assert!(VarRef::new("a", VarType::Boolean).accepts(VarType::Boolean));
        assert!(!VarRef::new("a", VarType::Boolean).accepts(VarType::Double));
        assert!(!VarRef::new("a", VarType::Boolean).accepts(VarType::Integer));
        assert!(!VarRef::new("a", VarType::Boolean).accepts(VarType::Text));

        assert!(!VarRef::new("a", VarType::Double).accepts(VarType::Boolean));
        assert!(VarRef::new("a", VarType::Double).accepts(VarType::Double));
        assert!(!VarRef::new("a", VarType::Double).accepts(VarType::Integer));
        assert!(!VarRef::new("a", VarType::Double).accepts(VarType::Text));

        assert!(!VarRef::new("a", VarType::Integer).accepts(VarType::Boolean));
        assert!(!VarRef::new("a", VarType::Integer).accepts(VarType::Double));
        assert!(VarRef::new("a", VarType::Integer).accepts(VarType::Integer));
        assert!(!VarRef::new("a", VarType::Integer).accepts(VarType::Text));

        assert!(!VarRef::new("a", VarType::Text).accepts(VarType::Boolean));
        assert!(!VarRef::new("a", VarType::Text).accepts(VarType::Double));
        assert!(!VarRef::new("a", VarType::Text).accepts(VarType::Integer));
        assert!(VarRef::new("a", VarType::Text).accepts(VarType::Text));
    }
}
