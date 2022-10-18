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

    /// Returns the name of this reference, without any type annotations.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the name of this reference, without any type annotations, and consumes the
    /// reference.
    pub(crate) fn take_name(self) -> String {
        self.name
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

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Boolean(true) => write!(f, "TRUE"),
            Value::Boolean(false) => write!(f, "FALSE"),
            Value::Double(d) => {
                let mut s = format!("{}", d);
                if !s.contains('.') {
                    s += ".0";
                }
                write!(f, "{}", s)
            }
            Value::Integer(i) => write!(f, "{}", i),
            Value::Text(s) => write!(f, "\"{}\"", s),
        }
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

    /// Consumes the value and generates a string to be used as the output of `PRINT`.  This is
    /// slightly different from the `Display` implementation because strings aren't double-quoted.
    pub fn to_output(self) -> String {
        match self {
            Value::Boolean(true) => "TRUE".to_owned(),
            Value::Boolean(false) => "FALSE".to_owned(),
            Value::Double(d) => format!("{}", d),
            Value::Integer(i) => format!("{}", i),
            Value::Text(s) => s,
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

/// Components of an array assignment statement.
#[derive(Debug, PartialEq)]
pub struct ArrayAssignmentSpan {
    /// Reference to the array to modify.
    pub vref: VarRef,

    /// Expressions to compute the subscripts to index the array.
    pub subscripts: Vec<Expr>,

    /// Expression to compute the value of the modified element.
    pub expr: Expr,
}

/// Components of an assignment statement.
#[derive(Debug, PartialEq)]
pub struct AssignmentSpan {
    /// Reference to the variable to set.
    pub vref: VarRef,

    /// Expression to compute the value of the modified variable.
    pub expr: Expr,
}

/// Components of an builtin call statement.
#[derive(Debug, PartialEq)]
pub struct BuiltinCallSpan {
    /// Name of the builtin to call.
    pub name: String,

    /// Sequence of arguments to pass to the builtin.
    ///
    /// Each argument is represented as an optional expression to evaluate and the separator that
    /// was to separate it from the *next* argument.  Because of this, the last argument always
    /// carries `ArgSep::End` as the separator.  The reason the expression is optional is to support
    /// calls of the form `PRINT a, , b`.
    //
    // TODO(jmmv): Each element within this vector should be represented as a `BuiltinCallArgSpan`
    // but this has implications throughout the codebase because this is directly consumed by every
    // builtin command implementation.
    pub args: Vec<(Option<Expr>, ArgSep)>,
}

/// Components of a variable definition.
///
/// Given that a definition causes the variable to be initialized to a default value, it is
/// tempting to model this statement as a simple assignment.  However, we must be able to
/// detect variable redeclarations at runtime, so we must treat this statement as a separate
/// type from assignments.
#[derive(Debug, Eq, PartialEq)]
pub struct DimSpan {
    /// Name of the variable to be defined.  Type annotations are not allowed, hence why this is
    /// not a `VarRef`.
    pub name: String,

    /// Type of the variable to be defined.
    pub vtype: VarType,
}

/// Components of an array definition.
#[derive(Debug, PartialEq)]
pub struct DimArraySpan {
    /// Name of the array to define.  Type annotations are not allowed, hence why this is not a
    /// `VarRef`.
    pub name: String,

    /// Expressions to compute the dimensions of the array.
    pub dimensions: Vec<Expr>,

    /// Type of the array to be defined.
    pub subtype: VarType,
}

/// Components of a branch of an `IF` statement.
#[derive(Debug, PartialEq)]
pub struct IfBranchSpan {
    /// Expression that guards execution of this branch.
    pub guard: Expr,

    /// Statements within the branch.
    pub body: Vec<Statement>,
}

/// Components of an `IF` statement.
#[derive(Debug, PartialEq)]
pub struct IfSpan {
    /// Sequence of the branches in the conditional.
    ///
    /// Representation of the conditional branches.  The final `ELSE` branch, if present, is also
    /// included here and its guard clause is always a true expression.
    pub branches: Vec<IfBranchSpan>,
}

/// Components of a `FOR` statement.
///
/// Note that we do not store the original end and step values, and instead use expressions to
/// represent the loop condition and the computation of the next iterator value.  We do this
/// for run-time efficiency.  The reason this is possible is because we force the step to be an
/// integer literal at parse time and do not allow it to be an expression.
#[derive(Debug, PartialEq)]
pub struct ForSpan {
    /// Iterator name, expressed as a variable reference that must be either automatic or an
    /// integer.
    pub iter: VarRef,

    /// Expression to compute the iterator's initial value.
    pub start: Expr,

    /// Condition to test after each iteration.
    pub end: Expr,

    /// Expression to compute the iterator's next value.
    pub next: Expr,

    /// Statements within the loop's body.
    pub body: Vec<Statement>,
}

/// Components of a `GOTO` statement.
#[derive(Debug, Eq, PartialEq)]
pub struct GotoSpan {
    /// Name of the label to jump to.
    pub target: String,
}

/// Components of a label "statement".
///
/// In principle, labels should be just a property of a statement but, for simplicity in the
/// current model, it's easiest to represent them as their own statement.
#[derive(Debug, Eq, PartialEq)]
pub struct LabelSpan {
    /// Name of the label being defined.
    pub name: String,
}

/// Components of a `WHILE` statement.
#[derive(Debug, PartialEq)]
pub struct WhileSpan {
    /// Expression to compute whether to execute the loop's body or not.
    pub expr: Expr,

    /// Statements within the loop's body.
    pub body: Vec<Statement>,
}

/// Represents a statement in the program along all data to execute it.
#[derive(Debug, PartialEq)]
pub enum Statement {
    /// Represents an assignment to an element of an array.
    ArrayAssignment(ArrayAssignmentSpan),

    /// Represents a variable assignment.
    Assignment(AssignmentSpan),

    /// Represents a call to a builtin command such as `PRINT`.
    BuiltinCall(BuiltinCallSpan),

    /// Represents a variable definition.
    Dim(DimSpan),

    /// Represents an array definition.
    DimArray(DimArraySpan),

    /// Represents a `FOR` statement.
    For(ForSpan),

    /// Represents a `GOTO` statement.
    Goto(GotoSpan),

    /// Represents an `IF` statement.
    If(IfSpan),

    /// Represents a label "statement".
    Label(LabelSpan),

    /// Represents a `WHILE` statement.
    While(WhileSpan),
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

    #[test]
    fn test_value_display() {
        assert_eq!("TRUE", format!("{}", Value::Boolean(true)));
        assert_eq!("FALSE", format!("{}", Value::Boolean(false)));
        assert_eq!("3.0", format!("{}", Value::Double(3.0)));
        assert_eq!("3.1", format!("{}", Value::Double(3.1)));
        assert_eq!("0.51", format!("{}", Value::Double(0.51)));
        assert_eq!("-56", format!("{}", Value::Integer(-56)));
        assert_eq!("\"some words\"", format!("{}", Value::Text("some words".to_owned())));
    }
}
