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
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Expr {
    /// A literal boolean value.
    Boolean(bool),
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

    /// A function call.
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
            VarType::Integer => "%",
            VarType::Text => "$",
            VarType::Void => "",
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

    /// Returns the type of this reference.
    pub fn ref_type(&self) -> VarType {
        self.ref_type
    }

    /// Returns true if this reference is compatible with the given `value`'s type.
    pub fn accepts(&self, value: &Value) -> bool {
        match (self.ref_type, value) {
            (VarType::Auto, _) => true,
            (VarType::Boolean, Value::Boolean(_)) => true,
            (VarType::Integer, Value::Integer(_)) => true,
            (VarType::Text, Value::Text(_)) => true,
            (_, _) => false,
        }
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

    /// An integer value.
    Integer(i32),

    /// A string value.
    Text(String), // Should be `String` but would get confusing with the built-in Rust type.
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
#[derive(Debug, Eq, PartialEq)]
pub enum Statement {
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
