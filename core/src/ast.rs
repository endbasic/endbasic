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

use crate::{reader::LineCol, syms::SymbolKey};
use std::fmt;

/// Components of a boolean literal expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BooleanSpan {
    /// The boolean literal.
    pub value: bool,

    /// Starting position of the literal.
    pub pos: LineCol,
}

/// Components of a double literal expression.
#[derive(Clone, Debug, PartialEq)]
pub struct DoubleSpan {
    /// The double literal.
    pub value: f64,

    /// Starting position of the literal.
    pub pos: LineCol,
}

/// Components of an integer literal expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IntegerSpan {
    /// The integer literal.
    pub value: i32,

    /// Starting position of the literal.
    pub pos: LineCol,
}

/// Components of a string literal expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TextSpan {
    /// The string literal.
    pub value: String,

    /// Starting position of the literal.
    pub pos: LineCol,
}

/// Components of a symbol reference expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolSpan {
    /// The symbol reference.
    pub vref: VarRef,

    /// Starting position of the symbol reference.
    pub pos: LineCol,
}

/// Components of a unary operation expression.
#[derive(Clone, Debug, PartialEq)]
pub struct UnaryOpSpan {
    /// Expression affected by the operator.
    pub expr: Expr,

    /// Starting position of the operator.
    pub pos: LineCol,
}

/// Components of a binary operation expression.
#[derive(Clone, Debug, PartialEq)]
pub struct BinaryOpSpan {
    /// Expression on the left side of the operator.
    pub lhs: Expr,

    /// Expression on the right side of the operator.
    pub rhs: Expr,

    /// Starting position of the operator.
    pub pos: LineCol,
}

/// Represents an expression and provides mechanisms to evaluate it.
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    /// A literal boolean value.
    Boolean(BooleanSpan),
    /// A literal double-precision floating point value.
    Double(DoubleSpan),
    /// A literal integer value.
    Integer(IntegerSpan),
    /// A literal string value.
    Text(TextSpan),

    /// A reference to a variable.
    Symbol(SymbolSpan),

    /// Arithmetic addition of two expressions.
    Add(Box<BinaryOpSpan>),
    /// Arithmetic subtraction of two expressions.
    Subtract(Box<BinaryOpSpan>),
    /// Arithmetic multiplication of two expressions.
    Multiply(Box<BinaryOpSpan>),
    /// Arithmetic division of two expressions.
    Divide(Box<BinaryOpSpan>),
    /// Arithmetic modulo operation of two expressions.
    Modulo(Box<BinaryOpSpan>),
    /// Arithmetic power operation of two expressions.
    Power(Box<BinaryOpSpan>),
    /// Arithmetic sign flip of an expression.
    Negate(Box<UnaryOpSpan>),

    /// Relational equality comparison of two expressions.
    Equal(Box<BinaryOpSpan>),
    /// Relational inequality comparison of two expressions.
    NotEqual(Box<BinaryOpSpan>),
    /// Relational less-than comparison of two expressions.
    Less(Box<BinaryOpSpan>),
    /// Relational less-than or equal-to comparison of two expressions.
    LessEqual(Box<BinaryOpSpan>),
    /// Relational greater-than comparison of two expressions.
    Greater(Box<BinaryOpSpan>),
    /// Relational greater-than or equal-to comparison of two expressions.
    GreaterEqual(Box<BinaryOpSpan>),

    /// Logical and of two expressions.
    And(Box<BinaryOpSpan>),
    /// Logical not of an expression.
    Not(Box<UnaryOpSpan>),
    /// Logical or of two expressions.
    Or(Box<BinaryOpSpan>),
    /// Logical xor of two expressions.
    Xor(Box<BinaryOpSpan>),

    /// Shift left of a signed integer by a number of bits without rotation.
    ShiftLeft(Box<BinaryOpSpan>),
    /// Shift right of a signed integer by a number of bits without rotation.
    ShiftRight(Box<BinaryOpSpan>),

    /// A function call or an array reference.
    Call(CallSpan),
}

impl Expr {
    /// Returns the start position of the expression.
    pub fn start_pos(&self) -> LineCol {
        match self {
            Expr::Boolean(span) => span.pos,
            Expr::Double(span) => span.pos,
            Expr::Integer(span) => span.pos,
            Expr::Text(span) => span.pos,

            Expr::Symbol(span) => span.pos,

            Expr::And(span) => span.lhs.start_pos(),
            Expr::Or(span) => span.lhs.start_pos(),
            Expr::Xor(span) => span.lhs.start_pos(),
            Expr::Not(span) => span.pos,

            Expr::ShiftLeft(span) => span.lhs.start_pos(),
            Expr::ShiftRight(span) => span.lhs.start_pos(),

            Expr::Equal(span) => span.lhs.start_pos(),
            Expr::NotEqual(span) => span.lhs.start_pos(),
            Expr::Less(span) => span.lhs.start_pos(),
            Expr::LessEqual(span) => span.lhs.start_pos(),
            Expr::Greater(span) => span.lhs.start_pos(),
            Expr::GreaterEqual(span) => span.lhs.start_pos(),

            Expr::Add(span) => span.lhs.start_pos(),
            Expr::Subtract(span) => span.lhs.start_pos(),
            Expr::Multiply(span) => span.lhs.start_pos(),
            Expr::Divide(span) => span.lhs.start_pos(),
            Expr::Modulo(span) => span.lhs.start_pos(),
            Expr::Power(span) => span.lhs.start_pos(),
            Expr::Negate(span) => span.pos,

            Expr::Call(span) => span.vref_pos,
        }
    }
}

/// Represents type of an expression.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExprType {
    /// Type for an expression that evaluates to a boolean.
    Boolean,

    /// Type for an expression that evaluates to a double.
    Double,

    /// Type for an expression that evaluates to an integer.
    Integer,

    /// Type for an expression that evaluates to a string.
    Text,
}

impl ExprType {
    /// Returns true if this expression type is numerical.
    pub(crate) fn is_numerical(self) -> bool {
        self == Self::Double || self == Self::Integer
    }

    /// Returns the textual representation of the annotation for this type.
    pub fn annotation(&self) -> char {
        match self {
            ExprType::Boolean => '?',
            ExprType::Double => '#',
            ExprType::Integer => '%',
            ExprType::Text => '$',
        }
    }

    /// Returns the default value to assign to this type.
    pub(crate) fn default_value(&self) -> Value {
        match self {
            ExprType::Boolean => Value::Boolean(false),
            ExprType::Double => Value::Double(0.0),
            ExprType::Integer => Value::Integer(0),
            ExprType::Text => Value::Text("".to_owned()),
        }
    }
}

impl fmt::Display for ExprType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExprType::Boolean => write!(f, "BOOLEAN"),
            ExprType::Double => write!(f, "DOUBLE"),
            ExprType::Integer => write!(f, "INTEGER"),
            ExprType::Text => write!(f, "STRING"),
        }
    }
}

/// Represents a reference to a variable (which doesn't have to exist).
///
/// Variable references are different from `SymbolKey`s because they maintain the case of the
/// reference (for error display purposes) and because they carry an optional type annotation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VarRef {
    /// Name of the variable this points to.
    name: String,

    /// Type of the variable this points to, if explicitly specified.
    ///
    /// If `None`, the type of the variable is subject to type inference.
    ref_type: Option<ExprType>,
}

impl VarRef {
    /// Creates a new reference to the variable with `name` and the optional `ref_type` type.
    pub fn new<T: Into<String>>(name: T, ref_type: Option<ExprType>) -> Self {
        Self { name: name.into(), ref_type }
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

    /// Returns the type of this reference.
    pub fn ref_type(&self) -> Option<ExprType> {
        self.ref_type
    }

    /// Returns true if this reference is compatible with the given type.
    pub fn accepts(&self, other: ExprType) -> bool {
        match self.ref_type {
            None => true,
            Some(vtype) => vtype == other,
        }
    }

    /// Returns true if this reference is compatible with the return type of a callable.
    pub fn accepts_callable(&self, other: Option<ExprType>) -> bool {
        match self.ref_type {
            None => true,
            Some(vtype) => match other {
                Some(other) => vtype == other,
                None => false,
            },
        }
    }

    /// Converts this variable reference to a symbol key.
    pub(crate) fn as_symbol_key(&self) -> SymbolKey {
        SymbolKey::from(&self.name)
    }
}

impl fmt::Display for VarRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.ref_type {
            None => self.name.fmt(f),
            Some(vtype) => write!(f, "{}{}", self.name, vtype.annotation()),
        }
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

    /// A reference to a variable.
    VarRef(SymbolKey, ExprType),
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
                if d.is_finite() && !d.is_nan() && !s.contains('.') {
                    s += ".0";
                }
                write!(f, "{}", s)
            }
            Value::Integer(i) => write!(f, "{}", i),
            Value::Text(s) => write!(f, "\"{}\"", s),
            Value::VarRef(key, etype) => write!(f, "{}{}", key, etype),
        }
    }
}

impl Value {
    /// Returns the type of the value as an `ExprType`.
    pub fn as_exprtype(&self) -> ExprType {
        match self {
            Value::Boolean(_) => ExprType::Boolean,
            Value::Double(_) => ExprType::Double,
            Value::Integer(_) => ExprType::Integer,
            Value::Text(_) => ExprType::Text,
            Value::VarRef(_key, etype) => *etype,
        }
    }
}

/// Types of separators between arguments to a `BuiltinCall`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArgSep {
    /// Filler for the separator in the last argument.
    End = 0,

    /// Short separator (`;`).
    Short = 1,

    /// Long separator (`,`).
    Long = 2,

    /// `AS` separator.
    As = 3,
}

impl fmt::Display for ArgSep {
    // TODO(jmmv): Can this be removed in favor of describe()?
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ArgSep::End => write!(f, "<END OF STATEMENT>"),
            ArgSep::Short => write!(f, ";"),
            ArgSep::Long => write!(f, ","),
            ArgSep::As => write!(f, "AS"),
        }
    }
}

impl ArgSep {
    /// Formats the separator for a syntax specification.
    ///
    /// The return value contains the textual representation of the separator and a boolean that
    /// indicates whether the separator requires a leading space.
    pub(crate) fn describe(&self) -> (&str, bool) {
        match self {
            ArgSep::End => ("", false),
            ArgSep::Short => (";", false),
            ArgSep::Long => (",", false),
            ArgSep::As => ("AS", true),
        }
    }
}

/// Components of an array assignment statement.
#[derive(Debug, PartialEq)]
#[cfg_attr(test, derive(Clone))]
pub struct ArrayAssignmentSpan {
    /// Reference to the array to modify.
    pub vref: VarRef,

    /// Position of the `vref`.
    pub vref_pos: LineCol,

    /// Expressions to compute the subscripts to index the array.
    pub subscripts: Vec<Expr>,

    /// Expression to compute the value of the modified element.
    pub expr: Expr,
}

/// Components of an assignment statement.
#[derive(Debug, PartialEq)]
#[cfg_attr(test, derive(Clone))]
pub struct AssignmentSpan {
    /// Reference to the variable to set.
    pub vref: VarRef,

    /// Position of the `vref`.
    pub vref_pos: LineCol,

    /// Expression to compute the value of the modified variable.
    pub expr: Expr,
}

/// Single argument to a builtin call statement.
#[derive(Clone, Debug, PartialEq)]
pub struct ArgSpan {
    /// Expression to compute the argument's value.  This expression is optional to support calls
    /// of the form `PRINT a, , b` where some arguments are empty.
    pub expr: Option<Expr>,

    /// Separator between this argument and the *next*.  The last instance of this type in a call
    /// always carries a value of `ArgSep::End`.
    pub sep: ArgSep,

    /// Position of the `sep`.
    pub sep_pos: LineCol,
}

/// Components of a call statement or expression.
#[derive(Clone, Debug, PartialEq)]
pub struct CallSpan {
    /// Reference to the callable (a command or a function), or the array to index.
    pub vref: VarRef,

    /// Position of the reference.
    pub vref_pos: LineCol,

    /// Sequence of arguments to pass to the callable.
    pub args: Vec<ArgSpan>,
}

/// Components of a data statement.
#[derive(Debug, PartialEq)]
pub struct DataSpan {
    /// Collection of optional literal values.
    pub values: Vec<Option<Value>>,
}

/// Components of a variable definition.
///
/// Given that a definition causes the variable to be initialized to a default value, it is
/// tempting to model this statement as a simple assignment.  However, we must be able to
/// detect variable redeclarations at runtime, so we must treat this statement as a separate
/// type from assignments.
#[derive(Debug, Eq, PartialEq)]
#[cfg_attr(test, derive(Clone))]
pub struct DimSpan {
    /// Name of the variable to be defined.  Type annotations are not allowed, hence why this is
    /// not a `VarRef`.
    pub name: String,

    /// Position of the name.
    pub name_pos: LineCol,

    /// Type of the variable to be defined.
    pub vtype: ExprType,

    /// Position of the type.
    pub vtype_pos: LineCol,
}

/// Components of an array definition.
#[derive(Debug, PartialEq)]
#[cfg_attr(test, derive(Clone))]
pub struct DimArraySpan {
    /// Name of the array to define.  Type annotations are not allowed, hence why this is not a
    /// `VarRef`.
    pub name: String,

    /// Position of the name.
    pub name_pos: LineCol,

    /// Expressions to compute the dimensions of the array.
    pub dimensions: Vec<Expr>,

    /// Type of the array to be defined.
    pub subtype: ExprType,

    /// Position of the subtype.
    pub subtype_pos: LineCol,
}

/// Type of the `DO` loop.
#[derive(Debug, PartialEq)]
pub enum DoGuard {
    /// Represents an infinite loop without guards.
    Infinite,

    /// Represents a loop with an `UNTIL` guard in the `DO` clause.
    PreUntil(Expr),

    /// Represents a loop with a `WHILE` guard in the `DO` clause.
    PreWhile(Expr),

    /// Represents a loop with an `UNTIL` guard in the `LOOP` clause.
    PostUntil(Expr),

    /// Represents a loop with a `WHILE` guard in the `LOOP` clause.
    PostWhile(Expr),
}

/// Components of a `DO` statement.
#[derive(Debug, PartialEq)]
pub struct DoSpan {
    /// Expression to compute whether to execute the loop's body or not and where this appears in
    /// the `DO` statement.
    pub guard: DoGuard,

    /// Statements within the loop's body.
    pub body: Vec<Statement>,
}

/// Components of an `END` statement.
#[derive(Debug, PartialEq)]
pub struct EndSpan {
    /// Integer expression to compute the return code.
    pub code: Option<Expr>,
}

/// Components of an `EXIT DO` statement.
#[derive(Debug, Eq, PartialEq)]
pub struct ExitDoSpan {
    /// Position of the statement.
    pub pos: LineCol,
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

    /// Position of the iterator.
    pub iter_pos: LineCol,

    /// If true, the iterator computation needs to be performed as a double so that, when the
    /// iterator variable is not yet defined, it gains the correct type.
    pub iter_double: bool,

    /// Expression to compute the iterator's initial value.
    pub start: Expr,

    /// Condition to test after each iteration.
    pub end: Expr,

    /// Expression to compute the iterator's next value.
    pub next: Expr,

    /// Statements within the loop's body.
    pub body: Vec<Statement>,
}

/// Components of a `GOTO` or a `GOSUB` statement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GotoSpan {
    /// Name of the label to jump to.
    pub target: String,

    /// Position of the label.
    pub target_pos: LineCol,
}

/// Components of a label "statement".
///
/// In principle, labels should be just a property of a statement but, for simplicity in the
/// current model, it's easiest to represent them as their own statement.
#[derive(Debug, Eq, PartialEq)]
pub struct LabelSpan {
    /// Name of the label being defined.
    pub name: String,

    /// Position of the label.
    pub name_pos: LineCol,
}

/// Components of an `ON ERROR` statement.
#[derive(Debug, Eq, PartialEq)]
pub enum OnErrorSpan {
    /// Components of an `ON ERROR GOTO @label` statement.
    Goto(GotoSpan),

    /// Components of an `ON ERROR GOTO 0` statement.
    Reset,

    /// Components of an `ON ERROR RESUME NEXT` statement.
    ResumeNext,
}

/// Components of a `RETURN` statement.
#[derive(Debug, Eq, PartialEq)]
pub struct ReturnSpan {
    /// Position of the statement.
    pub pos: LineCol,
}

/// Collection of relational operators that can appear in a `CASE IS` guard..
#[derive(Debug, Eq, PartialEq)]
pub enum CaseRelOp {
    /// Relational operator for `CASE IS =`.
    Equal,

    /// Relational operator for `CASE IS <>`.
    NotEqual,

    /// Relational operator for `CASE IS <`.
    Less,

    /// Relational operator for `CASE IS <=`.
    LessEqual,

    /// Relational operator for `CASE IS >`.
    Greater,

    /// Relational operator for `CASE IS >=`.
    GreaterEqual,
}

/// Components of a `CASE` guard.
#[derive(Debug, PartialEq)]
pub enum CaseGuardSpan {
    /// Represents an `IS <op> <expr>` guard or a simpler `<expr>` guard.
    Is(CaseRelOp, Expr),

    /// Represents an `<expr> TO <expr>` guard.
    To(Expr, Expr),
}

/// Components of a branch of a `SELECT` statement.
#[derive(Debug, PartialEq)]
pub struct CaseSpan {
    /// Expressions that guard execution of this case.
    pub guards: Vec<CaseGuardSpan>,

    /// Statements within the case block.
    pub body: Vec<Statement>,
}

/// Components of a `SELECT` statement.
#[derive(Debug, PartialEq)]
pub struct SelectSpan {
    /// Expression to test for.
    pub expr: Expr,

    /// Representation of the cases to select from.  The final `CASE ELSE`, if present, is also
    /// included here without any guards.
    pub cases: Vec<CaseSpan>,

    /// Position of the `END SELECT` statement.
    pub end_pos: LineCol,
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
    Call(CallSpan),

    /// Represents a `DATA` statement.
    Data(DataSpan),

    /// Represents a variable definition.
    Dim(DimSpan),

    /// Represents an array definition.
    DimArray(DimArraySpan),

    /// Represents a `DO` statement.
    Do(DoSpan),

    /// Represents an `END` statement.
    End(EndSpan),

    /// Represents an `EXIT DO` statement.
    ExitDo(ExitDoSpan),

    /// Represents a `FOR` statement.
    For(ForSpan),

    /// Represents a `GOSUB` statement.
    Gosub(GotoSpan),

    /// Represents a `GOTO` statement.
    Goto(GotoSpan),

    /// Represents an `IF` statement.
    If(IfSpan),

    /// Represents a label "statement".
    Label(LabelSpan),

    /// Represents an `ON ERROR` statement.
    OnError(OnErrorSpan),

    /// Represents a `RETURN` statement.
    Return(ReturnSpan),

    /// Represents a `SELECT` statement.
    Select(SelectSpan),

    /// Represents a `WHILE` statement.
    While(WhileSpan),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_varref_display() {
        assert_eq!("name", format!("{}", VarRef::new("name", None)));
        assert_eq!("abc?", format!("{}", VarRef::new("abc", Some(ExprType::Boolean))));
        assert_eq!("cba#", format!("{}", VarRef::new("cba", Some(ExprType::Double))));
        assert_eq!("def%", format!("{}", VarRef::new("def", Some(ExprType::Integer))));
        assert_eq!("ghi$", format!("{}", VarRef::new("ghi", Some(ExprType::Text))));
    }

    #[test]
    fn test_varref_accepts() {
        assert!(VarRef::new("a", None).accepts(ExprType::Boolean));
        assert!(VarRef::new("a", None).accepts(ExprType::Double));
        assert!(VarRef::new("a", None).accepts(ExprType::Integer));
        assert!(VarRef::new("a", None).accepts(ExprType::Text));

        assert!(VarRef::new("a", Some(ExprType::Boolean)).accepts(ExprType::Boolean));
        assert!(!VarRef::new("a", Some(ExprType::Boolean)).accepts(ExprType::Double));
        assert!(!VarRef::new("a", Some(ExprType::Boolean)).accepts(ExprType::Integer));
        assert!(!VarRef::new("a", Some(ExprType::Boolean)).accepts(ExprType::Text));

        assert!(!VarRef::new("a", Some(ExprType::Double)).accepts(ExprType::Boolean));
        assert!(VarRef::new("a", Some(ExprType::Double)).accepts(ExprType::Double));
        assert!(!VarRef::new("a", Some(ExprType::Double)).accepts(ExprType::Integer));
        assert!(!VarRef::new("a", Some(ExprType::Double)).accepts(ExprType::Text));

        assert!(!VarRef::new("a", Some(ExprType::Integer)).accepts(ExprType::Boolean));
        assert!(!VarRef::new("a", Some(ExprType::Integer)).accepts(ExprType::Double));
        assert!(VarRef::new("a", Some(ExprType::Integer)).accepts(ExprType::Integer));
        assert!(!VarRef::new("a", Some(ExprType::Integer)).accepts(ExprType::Text));

        assert!(!VarRef::new("a", Some(ExprType::Text)).accepts(ExprType::Boolean));
        assert!(!VarRef::new("a", Some(ExprType::Text)).accepts(ExprType::Double));
        assert!(!VarRef::new("a", Some(ExprType::Text)).accepts(ExprType::Integer));
        assert!(VarRef::new("a", Some(ExprType::Text)).accepts(ExprType::Text));
    }

    #[test]
    fn test_value_display() {
        assert_eq!("TRUE", format!("{}", Value::Boolean(true)));
        assert_eq!("FALSE", format!("{}", Value::Boolean(false)));
        assert_eq!("3.0", format!("{}", Value::Double(3.0)));
        assert_eq!("3.1", format!("{}", Value::Double(3.1)));
        assert_eq!("0.51", format!("{}", Value::Double(0.51)));
        assert_eq!("inf", format!("{}", Value::Double(f64::INFINITY)));
        assert_eq!("-inf", format!("{}", Value::Double(f64::NEG_INFINITY)));
        assert_eq!("NaN", format!("{}", Value::Double(f64::NAN)));
        assert_eq!("NaN", format!("{}", Value::Double(-f64::NAN)));
        assert_eq!("-56", format!("{}", Value::Integer(-56)));
        assert_eq!("\"some words\"", format!("{}", Value::Text("some words".to_owned())));
    }
}
