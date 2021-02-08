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

//! Evaluator for EndBASIC expressions.

use crate::ast::{Expr, Value, VarRef, VarType};
use crate::syms::{Array, CallError, CallableMetadata, Function, Symbol, Symbols};
use std::rc::Rc;

/// Evaluation errors.
#[derive(Debug, thiserror::Error)]
#[error("{message}")]
pub struct Error {
    message: String,
}

impl Error {
    /// Constructs a new evaluation error from a textual `message`.
    pub(crate) fn new<S: Into<String>>(message: S) -> Self {
        Self { message: message.into() }
    }

    /// Annotates a call evaluation error with the function's metadata.
    pub(crate) fn from_call_error(md: &CallableMetadata, e: CallError) -> Self {
        let message = match e {
            CallError::ArgumentError(e) => {
                format!("Syntax error in call to {}: {}", md.name(), e)
            }
            CallError::EvalError(e) => format!("Error in call to {}: {}", md.name(), e),
            CallError::InternalError(e) => format!("Error in call to {}: {}", md.name(), e),
            CallError::IoError(e) => format!("Error in call to {}: {}", md.name(), e),
            CallError::SyntaxError => {
                format!("Syntax error in call to {}: expected {}", md.name(), md.syntax())
            }
        };
        Self { message }
    }
}

/// Result for evaluation return values.
pub type Result<T> = std::result::Result<T, Error>;

impl Value {
    /// Parses a string `s` and constructs a `Value` that matches a given `VarType`.
    pub fn parse_as<T: Into<String>>(vtype: VarType, s: T) -> Result<Value> {
        fn parse_f64(s: &str) -> Result<Value> {
            match s.parse::<f64>() {
                Ok(d) => Ok(Value::Double(d)),
                Err(_) => Err(Error::new(format!(
                    "Invalid double-precision floating point literal {}",
                    s
                ))),
            }
        }

        fn parse_i32(s: &str) -> Result<Value> {
            match s.parse::<i32>() {
                Ok(i) => Ok(Value::Integer(i)),
                Err(_) => Err(Error::new(format!("Invalid integer literal {}", s))),
            }
        }

        let s = s.into();
        match vtype {
            VarType::Auto => parse_i32(&s),
            VarType::Boolean => {
                let raw = s.to_uppercase();
                if raw == "TRUE" || raw == "YES" || raw == "Y" {
                    Ok(Value::Boolean(true))
                } else if raw == "FALSE" || raw == "NO" || raw == "N" {
                    Ok(Value::Boolean(false))
                } else {
                    Err(Error::new(format!("Invalid boolean literal {}", s)))
                }
            }
            VarType::Double => parse_f64(&s),
            VarType::Integer => parse_i32(&s),
            VarType::Text => Ok(Value::Text(s)),
            VarType::Void => panic!("Void values are not supported"),
        }
    }

    /// Performs a logical "and" operation.
    pub fn and(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(*lhs && *rhs)),
            (_, _) => Err(Error::new(format!("Cannot AND {:?} and {:?}", self, other))),
        }
    }

    /// Performs a logical "or" operation.
    pub fn or(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(*lhs || *rhs)),
            (_, _) => Err(Error::new(format!("Cannot OR {:?} and {:?}", self, other))),
        }
    }

    /// Performs a logical "xor" operation.
    pub fn xor(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(*lhs ^ *rhs)),
            (_, _) => Err(Error::new(format!("Cannot XOR {:?} and {:?}", self, other))),
        }
    }

    /// Performs a logical "not" operation.
    pub fn not(&self) -> Result<Self> {
        match self {
            Value::Boolean(b) => Ok(Value::Boolean(!b)),
            _ => Err(Error::new(format!("Cannot apply NOT to {:?}", self))),
        }
    }

    /// Performs an equality check.
    pub fn eq(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(lhs == rhs)),
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Boolean(lhs == rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs == rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs == rhs)),
            (_, _) => Err(Error::new(format!("Cannot compare {:?} and {:?} with =", self, other))),
        }
    }

    /// Performs an inequality check.
    pub fn ne(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(lhs != rhs)),
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Boolean(lhs != rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs != rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs != rhs)),
            (_, _) => Err(Error::new(format!("Cannot compare {:?} and {:?} with <>", self, other))),
        }
    }

    /// Performs a less-than check.
    pub fn lt(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Boolean(lhs < rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs < rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs < rhs)),
            (_, _) => Err(Error::new(format!("Cannot compare {:?} and {:?} with <", self, other))),
        }
    }

    /// Performs a less-than or equal-to check.
    pub fn le(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Boolean(lhs <= rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs <= rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs <= rhs)),
            (_, _) => Err(Error::new(format!("Cannot compare {:?} and {:?} with <=", self, other))),
        }
    }

    /// Performs a greater-than check.
    pub fn gt(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Boolean(lhs > rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs > rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs > rhs)),
            (_, _) => Err(Error::new(format!("Cannot compare {:?} and {:?} with >", self, other))),
        }
    }

    /// Performs a greater-than or equal to check.
    pub fn ge(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Boolean(lhs >= rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs >= rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs >= rhs)),
            (_, _) => Err(Error::new(format!("Cannot compare {:?} and {:?} with >=", self, other))),
        }
    }

    /// Performs an arithmetic addition.
    pub fn add(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Double(lhs + rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => match lhs.checked_add(*rhs) {
                Some(i) => Ok(Value::Integer(i)),
                None => Err(Error::new(format!("Overflow adding {} and {}", lhs, rhs))),
            },
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Text(lhs.to_owned() + rhs)),
            (_, _) => Err(Error::new(format!("Cannot add {:?} and {:?}", self, other))),
        }
    }

    /// Performs an arithmetic subtraction.
    pub fn sub(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Double(lhs - rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => match lhs.checked_sub(*rhs) {
                Some(i) => Ok(Value::Integer(i)),
                None => Err(Error::new(format!("Overflow subtracting {} from {}", rhs, lhs))),
            },
            (_, _) => Err(Error::new(format!("Cannot subtract {:?} from {:?}", other, self))),
        }
    }

    /// Performs a multiplication.
    pub fn mul(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Double(lhs * rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => match lhs.checked_mul(*rhs) {
                Some(i) => Ok(Value::Integer(i)),
                None => Err(Error::new(format!("Overflow multiplying {} by {}", lhs, rhs))),
            },
            (_, _) => Err(Error::new(format!("Cannot multiply {:?} by {:?}", self, other))),
        }
    }

    /// Performs an arithmetic division.
    pub fn div(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Double(lhs / rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => {
                if rhs == &0 {
                    return Err(Error::new("Division by zero"));
                }
                match lhs.checked_div(*rhs) {
                    Some(i) => Ok(Value::Integer(i)),
                    None => Err(Error::new(format!("Overflow dividing {} by {}", lhs, rhs))),
                }
            }
            (_, _) => Err(Error::new(format!("Cannot divide {:?} by {:?}", self, other))),
        }
    }

    /// Performs a modulo operation.
    pub fn modulo(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Double(lhs % rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => {
                if rhs == &0 {
                    return Err(Error::new("Modulo by zero"));
                }
                match lhs.checked_rem(*rhs) {
                    Some(i) => Ok(Value::Integer(i)),
                    None => Err(Error::new(format!("Overflow modulo {} by {}", lhs, rhs))),
                }
            }
            (_, _) => Err(Error::new(format!("Cannot modulo {:?} by {:?}", self, other))),
        }
    }

    /// Performs an arithmetic negation.
    pub fn neg(&self) -> Result<Self> {
        match self {
            Value::Double(d) => Ok(Value::Double(-d)),
            Value::Integer(i) => match i.checked_neg() {
                Some(i) => Ok(Value::Integer(i)),
                None => Err(Error::new(format!("Overflow negating {}", i))),
            },
            _ => Err(Error::new(format!("Cannot negate {:?}", self))),
        }
    }
}

impl ToString for Value {
    fn to_string(&self) -> String {
        match self {
            Value::Boolean(true) => "TRUE".to_owned(),
            Value::Boolean(false) => "FALSE".to_owned(),
            Value::Double(d) => format!("{}", d),
            Value::Integer(i) => format!("{}", i),
            Value::Text(s2) => s2.clone(),
        }
    }
}

impl Expr {
    /// Evaluates a reference to `array` with subscripts `args`.
    fn eval_array_ref(&self, syms: &Symbols, array: &Array, args: &[Expr]) -> Result<Value> {
        let mut subscripts = Vec::with_capacity(args.len());
        for a in args {
            match a.eval(syms)? {
                Value::Integer(i) => subscripts.push(i),
                _ => return Err(Error::new("Array subscripts must be integers")),
            }
        }
        array.index(&subscripts).map(|v| v.clone())
    }

    /// Evaluates a function call specified by `fref` and arguments `args` on the function `f`.
    fn eval_function_call(
        &self,
        syms: &Symbols,
        fref: &VarRef,
        args: &[Expr],
        f: &Rc<dyn Function>,
    ) -> Result<Value> {
        let metadata = f.metadata();
        if !fref.accepts(metadata.return_type()) {
            return Err(Error::new("Incompatible type annotation for function call"));
        }

        let mut values = Vec::with_capacity(args.len());
        for a in args {
            values.push(a.eval(syms)?);
        }
        let result = f.exec(values);
        match result {
            Ok(value) => {
                debug_assert!(metadata.return_type() != VarType::Auto);
                let fref = VarRef::new(fref.name(), metadata.return_type());
                // Given that we only support built-in functions at the moment, this
                // could well be an assertion.  Doing so could turn into a time bomb
                // when/if we add user-defined functions, so handle the problem as an
                // error.
                if !fref.accepts(value.as_vartype()) {
                    return Err(Error::new(format!(
                        "Value returned by {} is incompatible with its type definition",
                        fref.name(),
                    )));
                }
                Ok(value)
            }
            Err(e) => Err(Error::from_call_error(&metadata, e)),
        }
    }

    /// Evaluates the expression to a value.
    ///
    /// Symbols are resolved by querying `syms`.  Errors in the computation are returned via the
    /// special `Value::Bad` type.
    pub fn eval(&self, syms: &Symbols) -> Result<Value> {
        match self {
            Expr::Boolean(b) => Ok(Value::Boolean(*b)),
            Expr::Double(d) => Ok(Value::Double(*d)),
            Expr::Integer(i) => Ok(Value::Integer(*i)),
            Expr::Text(s) => Ok(Value::Text(s.clone())),

            Expr::And(lhs, rhs) => Value::and(&lhs.eval(syms)?, &rhs.eval(syms)?),
            Expr::Or(lhs, rhs) => Value::or(&lhs.eval(syms)?, &rhs.eval(syms)?),
            Expr::Xor(lhs, rhs) => Value::xor(&lhs.eval(syms)?, &rhs.eval(syms)?),
            Expr::Not(v) => Value::not(&v.eval(syms)?),

            Expr::Equal(lhs, rhs) => Value::eq(&lhs.eval(syms)?, &rhs.eval(syms)?),
            Expr::NotEqual(lhs, rhs) => Value::ne(&lhs.eval(syms)?, &rhs.eval(syms)?),
            Expr::Less(lhs, rhs) => Value::lt(&lhs.eval(syms)?, &rhs.eval(syms)?),
            Expr::LessEqual(lhs, rhs) => Value::le(&lhs.eval(syms)?, &rhs.eval(syms)?),
            Expr::Greater(lhs, rhs) => Value::gt(&lhs.eval(syms)?, &rhs.eval(syms)?),
            Expr::GreaterEqual(lhs, rhs) => Value::ge(&lhs.eval(syms)?, &rhs.eval(syms)?),

            Expr::Add(lhs, rhs) => Value::add(&lhs.eval(syms)?, &rhs.eval(syms)?),
            Expr::Subtract(lhs, rhs) => Value::sub(&lhs.eval(syms)?, &rhs.eval(syms)?),
            Expr::Multiply(lhs, rhs) => Value::mul(&lhs.eval(syms)?, &rhs.eval(syms)?),
            Expr::Divide(lhs, rhs) => Value::div(&lhs.eval(syms)?, &rhs.eval(syms)?),
            Expr::Modulo(lhs, rhs) => Value::modulo(&lhs.eval(syms)?, &rhs.eval(syms)?),
            Expr::Negate(e) => Value::neg(&e.eval(syms)?),

            Expr::Symbol(vref) => Ok(syms.get_var(vref)?.clone()),

            Expr::Call(fref, args) => match syms.get(fref)? {
                Some(Symbol::Array(array)) => self.eval_array_ref(syms, array, args),
                Some(Symbol::Function(f)) => self.eval_function_call(syms, fref, args, f),
                Some(_) => Err(Error::new(format!("{} is not an array or a function", fref))),
                None => Err(Error::new(format!("Unknown function or array {}", fref))),
            },
        }
    }
}

#[cfg(test)]
pub(crate) mod testutils {
    use super::*;
    use crate::syms::{CallableMetadataBuilder, FunctionResult};

    /// Returns a value provided at construction time.  Note that the return type is fixed so we use
    /// this to verify if return values are correctly type-checked.
    pub(crate) struct TypeCheckFunction {
        metadata: CallableMetadata,
        value: Value,
    }

    impl TypeCheckFunction {
        pub(crate) fn new(value: Value) -> Rc<Self> {
            Rc::from(Self {
                metadata: CallableMetadataBuilder::new("TYPE_CHECK", VarType::Boolean).test_build(),
                value,
            })
        }
    }

    impl Function for TypeCheckFunction {
        fn metadata(&self) -> &CallableMetadata {
            &self.metadata
        }

        fn exec(&self, args: Vec<Value>) -> FunctionResult {
            assert!(args.is_empty());
            Ok(self.value.clone())
        }
    }

    /// Returns the error type asked for in an argument.
    pub(crate) struct ErrorFunction {
        metadata: CallableMetadata,
    }

    impl ErrorFunction {
        pub(crate) fn new() -> Rc<Self> {
            Rc::from(Self {
                metadata: CallableMetadataBuilder::new("ERROR", VarType::Boolean)
                    .with_syntax("arg1$")
                    .test_build(),
            })
        }
    }

    impl Function for ErrorFunction {
        fn metadata(&self) -> &CallableMetadata {
            &self.metadata
        }

        fn exec(&self, args: Vec<Value>) -> FunctionResult {
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
}

#[cfg(test)]
mod tests {
    use super::testutils::*;
    use super::*;
    use crate::ast::VarRef;
    use crate::syms::testutils::*;

    #[test]
    fn test_value_parse_as_auto() {
        use super::Value::*;

        assert_eq!(Integer(5), Value::parse_as(VarType::Auto, "5").unwrap());
        assert_eq!(
            "Invalid integer literal true",
            format!("{}", Value::parse_as(VarType::Auto, "true").unwrap_err())
        );
        assert_eq!(
            "Invalid integer literal a b",
            format!("{}", Value::parse_as(VarType::Auto, "a b").unwrap_err())
        );
    }

    #[test]
    fn test_value_parse_as_boolean() {
        use super::Value::*;

        for s in &["true", "TrUe", "TRUE", "yes", "Yes", "y", "Y"] {
            assert_eq!(Boolean(true), Value::parse_as(VarType::Boolean, *s).unwrap());
        }

        for s in &["false", "FaLsE", "FALSE", "no", "No", "n", "N"] {
            assert_eq!(Boolean(false), Value::parse_as(VarType::Boolean, *s).unwrap());
        }

        for s in &["ye", "0", "1", " true"] {
            assert_eq!(
                format!("Invalid boolean literal {}", s),
                format!("{}", Value::parse_as(VarType::Boolean, *s).unwrap_err())
            );
        }
    }

    #[test]
    fn test_value_parse_as_double() {
        use super::Value::*;

        assert_eq!(Double(10.0), Value::parse_as(VarType::Double, "10").unwrap());
        assert_eq!(Double(0.0), Value::parse_as(VarType::Double, "0").unwrap());
        assert_eq!(Double(-21.0), Value::parse_as(VarType::Double, "-21").unwrap());
        assert_eq!(Double(1.0), Value::parse_as(VarType::Double, "1.0").unwrap());
        assert_eq!(Double(0.01), Value::parse_as(VarType::Double, ".01").unwrap());

        assert_eq!(
            Double(123456789012345680000000000000.0),
            Value::parse_as(VarType::Double, "123456789012345678901234567890.1").unwrap()
        );

        assert_eq!(
            Double(1.1234567890123457),
            Value::parse_as(VarType::Double, "1.123456789012345678901234567890").unwrap()
        );

        assert_eq!(
            "Invalid double-precision floating point literal ",
            format!("{}", Value::parse_as(VarType::Double, "").unwrap_err())
        );
        assert_eq!(
            "Invalid double-precision floating point literal - 3.0",
            format!("{}", Value::parse_as(VarType::Double, "- 3.0").unwrap_err())
        );
        assert_eq!(
            "Invalid double-precision floating point literal 34ab3.1",
            format!("{}", Value::parse_as(VarType::Double, "34ab3.1").unwrap_err())
        );
    }

    #[test]
    fn test_value_parse_as_integer() {
        use super::Value::*;

        assert_eq!(Integer(10), Value::parse_as(VarType::Integer, "10").unwrap());
        assert_eq!(Integer(0), Value::parse_as(VarType::Integer, "0").unwrap());
        assert_eq!(Integer(-21), Value::parse_as(VarType::Integer, "-21").unwrap());

        assert_eq!(
            "Invalid integer literal ",
            format!("{}", Value::parse_as(VarType::Integer, "").unwrap_err())
        );
        assert_eq!(
            "Invalid integer literal - 3",
            format!("{}", Value::parse_as(VarType::Integer, "- 3").unwrap_err())
        );
        assert_eq!(
            "Invalid integer literal 34ab3",
            format!("{}", Value::parse_as(VarType::Integer, "34ab3").unwrap_err())
        );
    }

    #[test]
    fn test_value_parse_as_text() {
        use super::Value::*;

        assert_eq!(Text("".to_owned()), Value::parse_as(VarType::Text, "").unwrap());
        assert_eq!(Text("true".to_owned()), Value::parse_as(VarType::Text, "true").unwrap());
        assert_eq!(Text("32".to_owned()), Value::parse_as(VarType::Text, "32").unwrap());
        assert_eq!(Text("a b".to_owned()), Value::parse_as(VarType::Text, "a b").unwrap());
    }

    #[test]
    fn test_value_to_string() {
        use super::Value::*;

        assert_eq!("TRUE", &Boolean(true).to_string());
        assert_eq!("FALSE", &Boolean(false).to_string());
        assert_eq!("3", &Double(3.0).to_string());
        assert_eq!("0.51", &Double(0.51).to_string());
        assert_eq!("-56", &Integer(-56).to_string());
        assert_eq!("some words", &Text("some words".to_owned()).to_string());
    }

    #[test]
    fn test_value_to_string_and_parse() {
        use super::Value::*;

        let v = Boolean(false);
        assert_eq!(v, Value::parse_as(VarType::Boolean, &v.to_string()).unwrap());

        let v = Double(10.1);
        assert_eq!(v, Value::parse_as(VarType::Double, &v.to_string()).unwrap());

        let v = Integer(9);
        assert_eq!(v, Value::parse_as(VarType::Integer, &v.to_string()).unwrap());

        let v = Text("Some long text".to_owned());
        assert_eq!(v, Value::parse_as(VarType::Text, &v.to_string()).unwrap());
    }

    #[test]
    fn test_value_and() {
        use super::Value::*;

        assert_eq!(Boolean(false), Boolean(false).and(&Boolean(false)).unwrap());
        assert_eq!(Boolean(false), Boolean(false).and(&Boolean(true)).unwrap());
        assert_eq!(Boolean(false), Boolean(true).and(&Boolean(false)).unwrap());
        assert_eq!(Boolean(true), Boolean(true).and(&Boolean(true)).unwrap());

        assert_eq!(
            "Cannot AND Boolean(true) and Integer(5)",
            format!("{}", Boolean(true).and(&Integer(5)).unwrap_err())
        );
    }

    #[test]
    fn test_value_or() {
        use super::Value::*;

        assert_eq!(Boolean(false), Boolean(false).or(&Boolean(false)).unwrap());
        assert_eq!(Boolean(true), Boolean(false).or(&Boolean(true)).unwrap());
        assert_eq!(Boolean(true), Boolean(true).or(&Boolean(false)).unwrap());
        assert_eq!(Boolean(true), Boolean(true).or(&Boolean(true)).unwrap());

        assert_eq!(
            "Cannot OR Boolean(true) and Integer(5)",
            format!("{}", Boolean(true).or(&Integer(5)).unwrap_err())
        );
    }

    #[test]
    fn test_value_xor() {
        use super::Value::*;

        assert_eq!(Boolean(false), Boolean(false).xor(&Boolean(false)).unwrap());
        assert_eq!(Boolean(true), Boolean(false).xor(&Boolean(true)).unwrap());
        assert_eq!(Boolean(true), Boolean(true).xor(&Boolean(false)).unwrap());
        assert_eq!(Boolean(false), Boolean(true).xor(&Boolean(true)).unwrap());

        assert_eq!(
            "Cannot XOR Boolean(true) and Integer(5)",
            format!("{}", Boolean(true).xor(&Integer(5)).unwrap_err())
        );
    }

    #[test]
    fn test_value_not() {
        use super::Value::*;

        assert_eq!(Boolean(true), Boolean(false).not().unwrap());
        assert_eq!(Boolean(false), Boolean(true).not().unwrap());

        assert_eq!("Cannot apply NOT to Integer(5)", format!("{}", Integer(5).not().unwrap_err()));
    }

    #[test]
    fn test_value_eq() {
        use super::Value::*;

        assert_eq!(Boolean(true), Boolean(false).eq(&Boolean(false)).unwrap());
        assert_eq!(Boolean(false), Boolean(true).eq(&Boolean(false)).unwrap());
        assert_eq!(
            "Cannot compare Boolean(true) and Integer(5) with =",
            format!("{}", Boolean(true).eq(&Integer(5)).unwrap_err())
        );

        assert_eq!(Boolean(true), Double(2.5).eq(&Double(2.5)).unwrap());
        assert_eq!(Boolean(false), Double(3.5).eq(&Double(3.6)).unwrap());
        assert_eq!(
            "Cannot compare Double(4.0) and Integer(1) with =",
            format!("{}", Double(4.0).eq(&Integer(1)).unwrap_err())
        );

        assert_eq!(Boolean(true), Integer(2).eq(&Integer(2)).unwrap());
        assert_eq!(Boolean(false), Integer(3).eq(&Integer(4)).unwrap());
        assert_eq!(
            "Cannot compare Integer(4) and Double(1.0) with =",
            format!("{}", Integer(4).eq(&Double(1.0)).unwrap_err())
        );

        assert_eq!(Boolean(true), Text("a".to_owned()).eq(&Text("a".to_owned())).unwrap());
        assert_eq!(Boolean(false), Text("b".to_owned()).eq(&Text("c".to_owned())).unwrap());
        assert_eq!(
            "Cannot compare Text(\"\") and Boolean(false) with =",
            format!("{}", Text("".to_owned()).eq(&Boolean(false)).unwrap_err())
        );
    }

    #[test]
    fn test_value_ne() {
        use super::Value::*;

        assert_eq!(Boolean(false), Boolean(false).ne(&Boolean(false)).unwrap());
        assert_eq!(Boolean(true), Boolean(true).ne(&Boolean(false)).unwrap());
        assert_eq!(
            "Cannot compare Boolean(true) and Integer(5) with <>",
            format!("{}", Boolean(true).ne(&Integer(5)).unwrap_err())
        );

        assert_eq!(Boolean(false), Double(2.5).ne(&Double(2.5)).unwrap());
        assert_eq!(Boolean(true), Double(3.5).ne(&Double(3.6)).unwrap());
        assert_eq!(
            "Cannot compare Double(4.0) and Integer(1) with <>",
            format!("{}", Double(4.0).ne(&Integer(1)).unwrap_err())
        );

        assert_eq!(Boolean(false), Integer(2).ne(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(3).ne(&Integer(4)).unwrap());
        assert_eq!(
            "Cannot compare Integer(4) and Double(1.0) with <>",
            format!("{}", Integer(4).ne(&Double(1.0)).unwrap_err())
        );

        assert_eq!(Boolean(false), Text("a".to_owned()).ne(&Text("a".to_owned())).unwrap());
        assert_eq!(Boolean(true), Text("b".to_owned()).ne(&Text("c".to_owned())).unwrap());
        assert_eq!(
            "Cannot compare Text(\"\") and Boolean(false) with <>",
            format!("{}", Text("".to_owned()).ne(&Boolean(false)).unwrap_err())
        );
    }

    #[test]
    fn test_value_lt() {
        use super::Value::*;

        assert_eq!(
            "Cannot compare Boolean(false) and Boolean(true) with <",
            format!("{}", Boolean(false).lt(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Boolean(false), Double(2.5).lt(&Double(2.5)).unwrap());
        assert_eq!(Boolean(true), Double(3.5).lt(&Double(3.6)).unwrap());
        assert_eq!(
            "Cannot compare Double(4.0) and Integer(1) with <",
            format!("{}", Double(4.0).lt(&Integer(1)).unwrap_err())
        );

        assert_eq!(Boolean(false), Integer(2).lt(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(3).lt(&Integer(4)).unwrap());
        assert_eq!(
            "Cannot compare Integer(4) and Double(1.0) with <",
            format!("{}", Integer(4).lt(&Double(1.0)).unwrap_err())
        );

        assert_eq!(Boolean(false), Text("a".to_owned()).lt(&Text("a".to_owned())).unwrap());
        assert_eq!(Boolean(true), Text("a".to_owned()).lt(&Text("c".to_owned())).unwrap());
        assert_eq!(
            "Cannot compare Text(\"\") and Boolean(false) with <",
            format!("{}", Text("".to_owned()).lt(&Boolean(false)).unwrap_err())
        );
    }

    #[test]
    fn test_value_le() {
        use super::Value::*;

        assert_eq!(
            "Cannot compare Boolean(false) and Boolean(true) with <=",
            format!("{}", Boolean(false).le(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Boolean(false), Double(2.1).le(&Double(2.0)).unwrap());
        assert_eq!(Boolean(true), Double(2.1).le(&Double(2.1)).unwrap());
        assert_eq!(Boolean(true), Double(2.1).le(&Double(2.2)).unwrap());
        assert_eq!(
            "Cannot compare Double(4.0) and Integer(1) with <=",
            format!("{}", Double(4.0).le(&Integer(1)).unwrap_err())
        );

        assert_eq!(Boolean(false), Integer(2).le(&Integer(1)).unwrap());
        assert_eq!(Boolean(true), Integer(2).le(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(2).le(&Integer(3)).unwrap());
        assert_eq!(
            "Cannot compare Integer(4) and Double(1.0) with <=",
            format!("{}", Integer(4).le(&Double(1.0)).unwrap_err())
        );

        assert_eq!(Boolean(false), Text("b".to_owned()).le(&Text("a".to_owned())).unwrap());
        assert_eq!(Boolean(true), Text("a".to_owned()).le(&Text("a".to_owned())).unwrap());
        assert_eq!(Boolean(true), Text("a".to_owned()).le(&Text("c".to_owned())).unwrap());
        assert_eq!(
            "Cannot compare Text(\"\") and Boolean(false) with <=",
            format!("{}", Text("".to_owned()).le(&Boolean(false)).unwrap_err())
        );
    }

    #[test]
    fn test_value_gt() {
        use super::Value::*;

        assert_eq!(
            "Cannot compare Boolean(false) and Boolean(true) with >",
            format!("{}", Boolean(false).gt(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Boolean(false), Double(2.1).gt(&Double(2.1)).unwrap());
        assert_eq!(Boolean(true), Double(4.1).gt(&Double(4.0)).unwrap());
        assert_eq!(
            "Cannot compare Double(4.0) and Integer(1) with >",
            format!("{}", Double(4.0).gt(&Integer(1)).unwrap_err())
        );

        assert_eq!(Boolean(false), Integer(2).gt(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(4).gt(&Integer(3)).unwrap());
        assert_eq!(
            "Cannot compare Integer(4) and Double(1.0) with >",
            format!("{}", Integer(4).gt(&Double(1.0)).unwrap_err())
        );

        assert_eq!(Boolean(false), Text("a".to_owned()).gt(&Text("a".to_owned())).unwrap());
        assert_eq!(Boolean(true), Text("c".to_owned()).gt(&Text("a".to_owned())).unwrap());
        assert_eq!(
            "Cannot compare Text(\"\") and Boolean(false) with >",
            format!("{}", Text("".to_owned()).gt(&Boolean(false)).unwrap_err())
        );
    }

    #[test]
    fn test_value_ge() {
        use super::Value::*;

        assert_eq!(
            "Cannot compare Boolean(false) and Boolean(true) with >=",
            format!("{}", Boolean(false).ge(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Boolean(false), Double(2.0).ge(&Double(2.1)).unwrap());
        assert_eq!(Boolean(true), Double(2.1).ge(&Double(2.1)).unwrap());
        assert_eq!(Boolean(true), Double(2.2).ge(&Double(2.1)).unwrap());
        assert_eq!(
            "Cannot compare Double(4.0) and Integer(1) with >=",
            format!("{}", Double(4.0).ge(&Integer(1)).unwrap_err())
        );

        assert_eq!(Boolean(false), Integer(1).ge(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(2).ge(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(4).ge(&Integer(3)).unwrap());
        assert_eq!(
            "Cannot compare Integer(4) and Double(1.0) with >=",
            format!("{}", Integer(4).ge(&Double(1.0)).unwrap_err())
        );

        assert_eq!(Boolean(false), Text("".to_owned()).ge(&Text("b".to_owned())).unwrap());
        assert_eq!(Boolean(true), Text("a".to_owned()).ge(&Text("a".to_owned())).unwrap());
        assert_eq!(Boolean(true), Text("c".to_owned()).ge(&Text("a".to_owned())).unwrap());
        assert_eq!(
            "Cannot compare Text(\"\") and Boolean(false) with >=",
            format!("{}", Text("".to_owned()).ge(&Boolean(false)).unwrap_err())
        );
    }

    #[test]
    fn test_value_add() {
        use super::Value::*;

        assert_eq!(
            "Cannot add Boolean(false) and Boolean(true)",
            format!("{}", Boolean(false).add(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Double(7.1), Double(2.1).add(&Double(5.0)).unwrap());
        assert_eq!(
            "Cannot add Double(4.0) and Integer(5)",
            format!("{}", Double(4.0).add(&Integer(5)).unwrap_err())
        );

        assert_eq!(Integer(5), Integer(2).add(&Integer(3)).unwrap());
        assert_eq!(Integer(i32::MAX), Integer(i32::MAX).add(&Integer(0)).unwrap());
        assert_eq!(
            format!("Overflow adding {} and 1", i32::MAX),
            format!("{}", Integer(i32::MAX).add(&Integer(1)).unwrap_err())
        );
        assert_eq!(
            "Cannot add Integer(4) and Double(5.0)",
            format!("{}", Integer(4).add(&Double(5.0)).unwrap_err())
        );

        assert_eq!(Text("ab".to_owned()), Text("a".to_owned()).add(&Text("b".to_owned())).unwrap());
        assert_eq!(
            "Cannot add Text(\"\") and Boolean(false)",
            format!("{}", Text("".to_owned()).add(&Boolean(false)).unwrap_err())
        );
    }

    #[test]
    fn test_value_sub() {
        use super::Value::*;

        assert_eq!(
            "Cannot subtract Boolean(true) from Boolean(false)",
            format!("{}", Boolean(false).sub(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Double(-1.0), Double(2.5).sub(&Double(3.5)).unwrap());
        assert_eq!(
            "Cannot subtract Integer(5) from Double(4.0)",
            format!("{}", Double(4.0).sub(&Integer(5)).unwrap_err())
        );

        assert_eq!(Integer(-1), Integer(2).sub(&Integer(3)).unwrap());
        assert_eq!(Integer(i32::MIN), Integer(i32::MIN).sub(&Integer(0)).unwrap());
        assert_eq!(
            format!("Overflow subtracting 1 from {}", i32::MIN),
            format!("{}", Integer(i32::MIN).sub(&Integer(1)).unwrap_err())
        );
        assert_eq!(
            "Cannot subtract Double(5.0) from Integer(4)",
            format!("{}", Integer(4).sub(&Double(5.0)).unwrap_err())
        );

        assert_eq!(
            "Cannot subtract Text(\"a\") from Text(\"ab\")",
            format!("{}", Text("ab".to_owned()).sub(&Text("a".to_owned())).unwrap_err())
        );
    }

    #[test]
    fn test_value_mul() {
        use super::Value::*;

        assert_eq!(
            "Cannot multiply Boolean(false) by Boolean(true)",
            format!("{}", Boolean(false).mul(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Double(40.0), Double(4.0).mul(&Double(10.0)).unwrap());
        assert_eq!(
            "Cannot multiply Double(4.0) by Integer(5)",
            format!("{}", Double(4.0).mul(&Integer(5)).unwrap_err())
        );

        assert_eq!(Integer(6), Integer(2).mul(&Integer(3)).unwrap());
        assert_eq!(Integer(i32::MAX), Integer(i32::MAX).mul(&Integer(1)).unwrap());
        assert_eq!(
            format!("Overflow multiplying {} by 2", i32::MAX),
            format!("{}", Integer(i32::MAX).mul(&Integer(2)).unwrap_err())
        );
        assert_eq!(
            "Cannot multiply Integer(4) by Double(5.0)",
            format!("{}", Integer(4).mul(&Double(5.0)).unwrap_err())
        );

        assert_eq!(
            "Cannot multiply Text(\"\") by Text(\"a\")",
            format!("{}", Text("".to_owned()).mul(&Text("a".to_owned())).unwrap_err())
        );
    }

    #[test]
    fn test_value_div() {
        use super::Value::*;

        assert_eq!(
            "Cannot divide Boolean(false) by Boolean(true)",
            format!("{}", Boolean(false).div(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Double(4.0), Double(10.0).div(&Double(2.5)).unwrap());
        assert_eq!(Double(f64::INFINITY), Double(1.0).div(&Double(0.0)).unwrap());
        assert_eq!(
            "Cannot divide Double(4.0) by Integer(5)",
            format!("{}", Double(4.0).div(&Integer(5)).unwrap_err())
        );

        assert_eq!(Integer(2), Integer(10).div(&Integer(5)).unwrap());
        assert_eq!(Integer(6), Integer(20).div(&Integer(3)).unwrap());
        assert_eq!(Integer(i32::MIN), Integer(i32::MIN).div(&Integer(1)).unwrap());
        assert_eq!("Division by zero", format!("{}", Integer(4).div(&Integer(0)).unwrap_err()));
        assert_eq!(
            format!("Overflow dividing {} by -1", i32::MIN),
            format!("{}", Integer(i32::MIN).div(&Integer(-1)).unwrap_err())
        );
        assert_eq!(
            "Cannot divide Integer(4) by Double(5.0)",
            format!("{}", Integer(4).div(&Double(5.0)).unwrap_err())
        );

        assert_eq!(
            "Cannot divide Text(\"\") by Text(\"a\")",
            format!("{}", Text("".to_owned()).div(&Text("a".to_owned())).unwrap_err())
        );
    }

    #[test]
    fn test_value_modulo() {
        use super::Value::*;

        assert_eq!(
            "Cannot modulo Boolean(false) by Boolean(true)",
            format!("{}", Boolean(false).modulo(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Double(0.0), Double(10.0).modulo(&Double(2.5)).unwrap());
        match Double(1.0).modulo(&Double(0.0)).unwrap() {
            Double(d) => assert!(d.is_nan()),
            _ => panic!("Did not get a double"),
        };
        assert_eq!(
            "Cannot modulo Double(4.0) by Integer(5)",
            format!("{}", Double(4.0).modulo(&Integer(5)).unwrap_err())
        );

        assert_eq!(Integer(0), Integer(10).modulo(&Integer(5)).unwrap());
        assert_eq!(Integer(2), Integer(20).modulo(&Integer(3)).unwrap());
        assert_eq!("Modulo by zero", format!("{}", Integer(4).modulo(&Integer(0)).unwrap_err()));
        assert_eq!(
            format!("Overflow modulo {} by -1", i32::MIN),
            format!("{}", Integer(i32::MIN).modulo(&Integer(-1)).unwrap_err())
        );
        assert_eq!(
            "Cannot modulo Integer(4) by Double(5.0)",
            format!("{}", Integer(4).modulo(&Double(5.0)).unwrap_err())
        );

        assert_eq!(
            "Cannot modulo Text(\"\") by Text(\"a\")",
            format!("{}", Text("".to_owned()).modulo(&Text("a".to_owned())).unwrap_err())
        );
    }

    #[test]
    fn test_value_neg() {
        use super::Value::*;

        assert_eq!("Cannot negate Boolean(true)", format!("{}", Boolean(true).neg().unwrap_err()));

        assert_eq!(Double(-6.12), Double(6.12).neg().unwrap());
        assert_eq!(Double(5.53), Double(-5.53).neg().unwrap());

        assert_eq!(Integer(-6), Integer(6).neg().unwrap());
        assert_eq!(Integer(5), Integer(-5).neg().unwrap());
        assert_eq!(
            format!("Overflow negating {}", i32::MIN),
            format!("{}", Integer(i32::MIN).neg().unwrap_err())
        );

        assert_eq!(
            "Cannot negate Text(\"\")",
            format!("{}", Text("".to_owned()).neg().unwrap_err())
        );
    }

    #[test]
    fn test_expr_literals() {
        let syms = Symbols::default();
        assert_eq!(Value::Boolean(true), Expr::Boolean(true).eval(&syms).unwrap());
        assert_eq!(Value::Double(0.0), Expr::Double(0.0).eval(&syms).unwrap());
        assert_eq!(Value::Integer(0), Expr::Integer(0).eval(&syms).unwrap());
        assert_eq!(Value::Text("z".to_owned()), Expr::Text("z".to_owned()).eval(&syms).unwrap());
    }

    #[test]
    fn test_expr_symbol() {
        let bool_ref = VarRef::new("a_boolean", VarType::Auto);
        let bool_val = Value::Boolean(true);
        let double_ref = VarRef::new("a_double", VarType::Auto);
        let double_val = Value::Double(0.0);
        let int_ref = VarRef::new("an_integer", VarType::Auto);
        let int_val = Value::Integer(0);
        let text_ref = VarRef::new("a_string", VarType::Auto);
        let text_val = Value::Text("x".to_owned());

        let mut syms = Symbols::default();
        syms.set_var(&bool_ref, bool_val.clone()).unwrap();
        syms.set_var(&double_ref, double_val.clone()).unwrap();
        syms.set_var(&int_ref, int_val.clone()).unwrap();
        syms.set_var(&text_ref, text_val.clone()).unwrap();

        assert_eq!(bool_val, Expr::Symbol(bool_ref).eval(&syms).unwrap());
        assert_eq!(double_val, Expr::Symbol(double_ref).eval(&syms).unwrap());
        assert_eq!(int_val, Expr::Symbol(int_ref).eval(&syms).unwrap());
        assert_eq!(text_val, Expr::Symbol(text_ref).eval(&syms).unwrap());

        assert_eq!(
            "Undefined variable x",
            format!("{}", Expr::Symbol(VarRef::new("x", VarType::Auto)).eval(&syms).unwrap_err())
        );
    }

    #[test]
    fn test_expr_logical_ops() {
        let a_bool = Box::from(Expr::Boolean(false));
        let an_int = Box::from(Expr::Integer(0));

        // These tests just make sure that we delegate to the `Value` operations for each
        // expression operator to essentially avoid duplicating all those tests.  We do this by
        // triggering errors and rely on the fact that their messages are different for every
        // operation.
        let syms = Symbols::default();
        assert_eq!(
            "Cannot AND Boolean(false) and Integer(0)",
            format!("{}", Expr::And(a_bool.clone(), an_int.clone()).eval(&syms).unwrap_err())
        );
        assert_eq!(
            "Cannot OR Boolean(false) and Integer(0)",
            format!("{}", Expr::Or(a_bool.clone(), an_int.clone()).eval(&syms).unwrap_err())
        );
        assert_eq!(
            "Cannot XOR Boolean(false) and Integer(0)",
            format!("{}", Expr::Xor(a_bool, an_int.clone()).eval(&syms).unwrap_err())
        );
        assert_eq!(
            "Cannot apply NOT to Integer(0)",
            format!("{}", Expr::Not(an_int).eval(&syms).unwrap_err())
        );
    }

    #[test]
    fn test_expr_relational_ops() {
        let a_bool = Box::from(Expr::Boolean(false));
        let an_int = Box::from(Expr::Integer(0));

        // These tests just make sure that we delegate to the `Value` operations for each
        // expression operator to essentially avoid duplicating all those tests.  We do this by
        // triggering errors and rely on the fact that their messages are different for every
        // operation.
        let syms = Symbols::default();
        assert_eq!(
            "Cannot compare Boolean(false) and Integer(0) with =",
            format!("{}", Expr::Equal(a_bool.clone(), an_int.clone()).eval(&syms).unwrap_err())
        );
        assert_eq!(
            "Cannot compare Boolean(false) and Integer(0) with <>",
            format!("{}", Expr::NotEqual(a_bool.clone(), an_int.clone()).eval(&syms).unwrap_err())
        );
        assert_eq!(
            "Cannot compare Boolean(false) and Integer(0) with <",
            format!("{}", Expr::Less(a_bool.clone(), an_int.clone()).eval(&syms).unwrap_err())
        );
        assert_eq!(
            "Cannot compare Boolean(false) and Integer(0) with <=",
            format!("{}", Expr::LessEqual(a_bool.clone(), an_int.clone()).eval(&syms).unwrap_err())
        );
        assert_eq!(
            "Cannot compare Boolean(false) and Integer(0) with >",
            format!("{}", Expr::Greater(a_bool.clone(), an_int.clone()).eval(&syms).unwrap_err())
        );
        assert_eq!(
            "Cannot compare Boolean(false) and Integer(0) with >=",
            format!("{}", Expr::GreaterEqual(a_bool, an_int).eval(&syms).unwrap_err())
        );
    }

    #[test]
    fn test_expr_arithmetic_ops() {
        let a_bool = Box::from(Expr::Boolean(false));
        let an_int = Box::from(Expr::Integer(0));

        // These tests just make sure that we delegate to the `Value` operations for each
        // expression operator to essentially avoid duplicating all those tests.  We do this by
        // triggering errors and rely on the fact that their messages are different for every
        // operation.
        let syms = Symbols::default();
        assert_eq!(
            "Cannot add Boolean(false) and Integer(0)",
            format!("{}", Expr::Add(a_bool.clone(), an_int.clone()).eval(&syms).unwrap_err())
        );
        assert_eq!(
            "Cannot subtract Integer(0) from Boolean(false)",
            format!("{}", Expr::Subtract(a_bool.clone(), an_int.clone()).eval(&syms).unwrap_err())
        );
        assert_eq!(
            "Cannot multiply Boolean(false) by Integer(0)",
            format!("{}", Expr::Multiply(a_bool.clone(), an_int.clone()).eval(&syms).unwrap_err())
        );
        assert_eq!(
            "Cannot divide Boolean(false) by Integer(0)",
            format!("{}", Expr::Divide(a_bool.clone(), an_int).eval(&syms).unwrap_err())
        );
        assert_eq!(
            "Cannot negate Boolean(false)",
            format!("{}", Expr::Negate(a_bool).eval(&syms).unwrap_err())
        );
    }

    #[test]
    fn test_expr_various_ops_and_vars() {
        let xref = VarRef::new("x", VarType::Integer);
        let yref = VarRef::new("y", VarType::Integer);

        let mut syms = Symbols::default();
        syms.set_var(&xref, Value::Integer(10)).unwrap();
        syms.set_var(&yref, Value::Integer(3)).unwrap();

        assert_eq!(
            Value::Integer(36),
            Expr::Multiply(
                Box::from(Expr::Add(
                    Box::from(Expr::Symbol(xref.clone())),
                    Box::from(Expr::Integer(2))
                )),
                Box::from(Expr::Symbol(yref.clone()))
            )
            .eval(&syms)
            .unwrap()
        );

        assert_eq!(
            Value::Boolean(true),
            Expr::Equal(
                Box::from(Expr::Symbol(xref)),
                Box::from(Expr::Add(Box::from(Expr::Integer(7)), Box::from(Expr::Symbol(yref))))
            )
            .eval(&syms)
            .unwrap()
        );

        assert_eq!(
            "Cannot add Integer(7) and Boolean(true)",
            format!(
                "{}",
                Expr::Equal(
                    Box::from(Expr::Integer(3)),
                    Box::from(Expr::Add(
                        Box::from(Expr::Integer(7)),
                        Box::from(Expr::Boolean(true))
                    ))
                )
                .eval(&syms)
                .unwrap_err()
            )
        );
    }

    #[test]
    fn test_expr_array_simple() {
        let xref = VarRef::new("x", VarType::Integer);

        let mut syms = Symbols::default();
        syms.dim_array("x", VarType::Integer, vec![2, 4]).unwrap();
        match syms.get_mut(&xref).unwrap().unwrap() {
            Symbol::Array(array) => array.assign(&[1, 3], Value::Integer(8)).unwrap(),
            _ => panic!("Got something that is not the array we asked for"),
        }

        assert_eq!(
            Value::Integer(0),
            Expr::Call(VarRef::new("X", VarType::Auto), vec![Expr::Integer(0), Expr::Integer(3)])
                .eval(&syms)
                .unwrap()
        );

        assert_eq!(
            Value::Integer(8),
            Expr::Call(VarRef::new("X", VarType::Auto), vec![Expr::Integer(1), Expr::Integer(3)])
                .eval(&syms)
                .unwrap()
        );

        assert_eq!(
            Value::Integer(8),
            Expr::Call(
                VarRef::new("X", VarType::Integer),
                vec![Expr::Integer(1), Expr::Integer(3)]
            )
            .eval(&syms)
            .unwrap()
        );

        assert_eq!(
            "Incompatible types in X# reference",
            format!(
                "{}",
                Expr::Call(
                    VarRef::new("X", VarType::Double),
                    vec![Expr::Integer(1), Expr::Integer(3)]
                )
                .eval(&syms)
                .unwrap_err()
            )
        );

        assert_eq!(
            "Cannot index array with 1 subscripts; need 2",
            format!(
                "{}",
                Expr::Call(VarRef::new("X", VarType::Integer), vec![Expr::Integer(1)])
                    .eval(&syms)
                    .unwrap_err()
            )
        );

        assert_eq!(
            "Subscript -1 cannot be negative",
            format!(
                "{}",
                Expr::Call(
                    VarRef::new("X", VarType::Integer),
                    vec![Expr::Integer(0), Expr::Integer(-1)]
                )
                .eval(&syms)
                .unwrap_err()
            )
        );

        assert_eq!(
            "Subscript 10 exceeds limit of 2",
            format!(
                "{}",
                Expr::Call(
                    VarRef::new("X", VarType::Integer),
                    vec![Expr::Integer(10), Expr::Integer(0)]
                )
                .eval(&syms)
                .unwrap_err()
            )
        );

        assert_eq!(
            "Unknown function or array y$",
            format!(
                "{}",
                Expr::Call(VarRef::new("y".to_owned(), VarType::Text), vec![])
                    .eval(&syms)
                    .unwrap_err()
            )
        );
    }

    #[test]
    fn test_expr_function_call_simple() {
        let xref = VarRef::new("x", VarType::Integer);
        let mut syms = SymbolsBuilder::default().add_function(SumFunction::new()).build();
        syms.set_var(&xref, Value::Integer(5)).unwrap();

        assert_eq!(
            Value::Integer(0),
            Expr::Call(VarRef::new("SUM".to_owned(), VarType::Auto), vec![],).eval(&syms).unwrap()
        );

        assert_eq!(
            Value::Integer(5),
            Expr::Call(VarRef::new("sum".to_owned(), VarType::Auto), vec![Expr::Integer(5)],)
                .eval(&syms)
                .unwrap()
        );

        assert_eq!(
            Value::Integer(7),
            Expr::Call(
                VarRef::new("SUM".to_owned(), VarType::Auto),
                vec![Expr::Integer(5), Expr::Integer(2)],
            )
            .eval(&syms)
            .unwrap()
        );

        assert_eq!(
            Value::Integer(23),
            Expr::Call(
                VarRef::new("SUM".to_owned(), VarType::Integer),
                vec![
                    Expr::Symbol(xref),
                    Expr::Integer(8),
                    Expr::Subtract(Box::from(Expr::Integer(100)), Box::from(Expr::Integer(90)))
                ],
            )
            .eval(&syms)
            .unwrap()
        );

        assert_eq!(
            "Incompatible types in SUM$ reference",
            format!(
                "{}",
                Expr::Call(VarRef::new("SUM".to_owned(), VarType::Text), vec![])
                    .eval(&syms)
                    .unwrap_err()
            )
        );

        assert_eq!(
            "Unknown function or array SUMA$",
            format!(
                "{}",
                Expr::Call(VarRef::new("SUMA".to_owned(), VarType::Text), vec![])
                    .eval(&syms)
                    .unwrap_err()
            )
        );
    }

    #[test]
    fn test_expr_function_call_type_check() {
        {
            let syms = SymbolsBuilder::default()
                .add_function(TypeCheckFunction::new(Value::Boolean(true)))
                .build();
            assert_eq!(
                Value::Boolean(true),
                Expr::Call(VarRef::new("TYPE_CHECK".to_owned(), VarType::Auto), vec![],)
                    .eval(&syms)
                    .unwrap()
            );
        }

        {
            let syms = SymbolsBuilder::default()
                .add_function(TypeCheckFunction::new(Value::Integer(5)))
                .build();
            assert_eq!(
                "Value returned by TYPE_CHECK is incompatible with its type definition",
                format!(
                    "{}",
                    Expr::Call(VarRef::new("TYPE_CHECK".to_owned(), VarType::Auto), vec![],)
                        .eval(&syms)
                        .unwrap_err()
                )
            );
        }
    }

    #[test]
    fn test_expr_function_error_check() {
        let syms = SymbolsBuilder::default().add_function(ErrorFunction::new()).build();

        assert_eq!(
            "Syntax error in call to ERROR: Bad argument",
            format!(
                "{}",
                Expr::Call(
                    VarRef::new("ERROR".to_owned(), VarType::Auto),
                    vec![Expr::Text("argument".to_owned())],
                )
                .eval(&syms)
                .unwrap_err()
            )
        );

        assert_eq!(
            "Error in call to ERROR: Some eval error",
            format!(
                "{}",
                Expr::Call(
                    VarRef::new("ERROR".to_owned(), VarType::Auto),
                    vec![Expr::Text("eval".to_owned())],
                )
                .eval(&syms)
                .unwrap_err()
            )
        );

        assert_eq!(
            "Error in call to ERROR: Some internal error",
            format!(
                "{}",
                Expr::Call(
                    VarRef::new("ERROR".to_owned(), VarType::Auto),
                    vec![Expr::Text("internal".to_owned())],
                )
                .eval(&syms)
                .unwrap_err()
            )
        );

        assert_eq!(
            "Syntax error in call to ERROR: expected arg1$",
            format!(
                "{}",
                Expr::Call(
                    VarRef::new("ERROR".to_owned(), VarType::Auto),
                    vec![Expr::Text("syntax".to_owned())],
                )
                .eval(&syms)
                .unwrap_err()
            )
        );
    }
}
