// EndBASIC
// Copyright 2022 Julio Merino
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

//! Operations on EndBASIC values.

use crate::ast::*;
use std::convert::TryFrom;

/// Evaluation errors.
#[derive(Debug, thiserror::Error)]
#[error("{message}")]
pub struct Error {
    pub(crate) message: String,
}

impl Error {
    /// Constructs a new evaluation error from a textual `message`.
    pub(crate) fn new<S: Into<String>>(message: S) -> Self {
        Self { message: message.into() }
    }
}

/// Result for value computation return values.
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

    /// Reinterprets this value as an `i32` and fails if the conversion is not possible.
    pub fn as_i32(&self) -> Result<i32> {
        match self {
            Value::Double(d) => {
                let d = d.round();
                if d.is_finite() && d >= (std::i32::MIN as f64) && (d <= std::i32::MAX as f64) {
                    Ok(d as i32)
                } else {
                    Err(Error::new(format!("Cannot cast {} to integer due to overflow", d)))
                }
            }
            Value::Integer(i) => Ok(*i),
            _ => Err(Error::new(format!("{} is not a number", self))),
        }
    }

    /// Reinterprets this value as an `f64` and fails if the conversion is not possible.
    pub fn as_f64(&self) -> Result<f64> {
        match self {
            Value::Double(d) => Ok(*d),
            Value::Integer(i) => Ok(*i as f64),
            _ => Err(Error::new(format!("{} is not a number", self))),
        }
    }

    /// Given a `target` variable type, tries to convert the value to that type if they are
    /// compatible or otherwise returns self.
    ///
    /// Can return an error when the conversion is feasible but it is not possible, such as trying
    /// to cast a NaN to an integer.
    pub fn maybe_cast(self, target: VarType) -> Result<Value> {
        match (target, self) {
            (VarType::Integer, d @ Value::Double(_)) => Ok(Value::Integer(d.as_i32()?)),
            (VarType::Double, i @ Value::Integer(_)) => Ok(Value::Double(i.as_f64()?)),
            (_, v) => Ok(v),
        }
    }

    /// Performs a logical or bitwise "and" operation.
    pub fn and(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(*lhs && *rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Integer(*lhs & *rhs)),
            (_, _) => Err(Error::new(format!("Cannot AND {} and {}", self, other))),
        }
    }

    /// Performs a logical or bitwise "or" operation.
    pub fn or(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(*lhs || *rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Integer(*lhs | *rhs)),
            (_, _) => Err(Error::new(format!("Cannot OR {} and {}", self, other))),
        }
    }

    /// Performs a logical or bitwise "xor" operation.
    pub fn xor(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(*lhs ^ *rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Integer(*lhs ^ *rhs)),
            (_, _) => Err(Error::new(format!("Cannot XOR {} and {}", self, other))),
        }
    }

    /// Performs a logical or bitwise "not" operation.
    pub fn not(&self) -> Result<Self> {
        match self {
            Value::Boolean(b) => Ok(Value::Boolean(!b)),
            Value::Integer(b) => Ok(Value::Integer(!b)),
            _ => Err(Error::new(format!("Cannot apply NOT to {}", self))),
        }
    }

    /// Performs an equality check.
    pub fn eq(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(lhs == rhs)),
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Boolean(lhs == rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs == rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs == rhs)),

            (Value::Double(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(*lhs == *rhs as f64)),
            (Value::Integer(lhs), Value::Double(rhs)) => Ok(Value::Boolean(*lhs as f64 == *rhs)),

            (_, _) => Err(Error::new(format!("Cannot compare {} and {} with =", self, other))),
        }
    }

    /// Performs an inequality check.
    pub fn ne(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(lhs != rhs)),
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Boolean(lhs != rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs != rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs != rhs)),

            (Value::Double(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(*lhs != *rhs as f64)),
            (Value::Integer(lhs), Value::Double(rhs)) => Ok(Value::Boolean(*lhs as f64 != *rhs)),

            (_, _) => Err(Error::new(format!("Cannot compare {} and {} with <>", self, other))),
        }
    }

    /// Performs a less-than check.
    pub fn lt(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Boolean(lhs < rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs < rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs < rhs)),

            (Value::Double(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(*lhs < *rhs as f64)),
            (Value::Integer(lhs), Value::Double(rhs)) => Ok(Value::Boolean((*lhs as f64) < *rhs)),

            (_, _) => Err(Error::new(format!("Cannot compare {} and {} with <", self, other))),
        }
    }

    /// Performs a less-than or equal-to check.
    pub fn le(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Boolean(lhs <= rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs <= rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs <= rhs)),

            (Value::Double(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(*lhs <= *rhs as f64)),
            (Value::Integer(lhs), Value::Double(rhs)) => Ok(Value::Boolean(*lhs as f64 <= *rhs)),

            (_, _) => Err(Error::new(format!("Cannot compare {} and {} with <=", self, other))),
        }
    }

    /// Performs a greater-than check.
    pub fn gt(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Boolean(lhs > rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs > rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs > rhs)),

            (Value::Double(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(*lhs > *rhs as f64)),
            (Value::Integer(lhs), Value::Double(rhs)) => Ok(Value::Boolean(*lhs as f64 > *rhs)),

            (_, _) => Err(Error::new(format!("Cannot compare {} and {} with >", self, other))),
        }
    }

    /// Performs a greater-than or equal to check.
    pub fn ge(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Boolean(lhs >= rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs >= rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs >= rhs)),

            (Value::Double(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(*lhs >= *rhs as f64)),
            (Value::Integer(lhs), Value::Double(rhs)) => Ok(Value::Boolean(*lhs as f64 >= *rhs)),

            (_, _) => Err(Error::new(format!("Cannot compare {} and {} with >=", self, other))),
        }
    }

    /// Performs an arithmetic addition.
    pub fn add(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Double(lhs + rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => match lhs.checked_add(*rhs) {
                Some(i) => Ok(Value::Integer(i)),
                None => Ok(Value::Double(*lhs as f64 + *rhs as f64)),
            },
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Text(lhs.to_owned() + rhs)),

            (Value::Double(lhs), Value::Integer(rhs)) => Ok(Value::Double(lhs + *rhs as f64)),
            (Value::Integer(lhs), Value::Double(rhs)) => Ok(Value::Double(*lhs as f64 + rhs)),

            (_, _) => Err(Error::new(format!("Cannot add {} and {}", self, other))),
        }
    }

    /// Performs an arithmetic subtraction.
    pub fn sub(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Double(lhs - rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => match lhs.checked_sub(*rhs) {
                Some(i) => Ok(Value::Integer(i)),
                None => Ok(Value::Double(*lhs as f64 - *rhs as f64)),
            },

            (Value::Double(lhs), Value::Integer(rhs)) => Ok(Value::Double(lhs - *rhs as f64)),
            (Value::Integer(lhs), Value::Double(rhs)) => Ok(Value::Double(*lhs as f64 - rhs)),

            (_, _) => Err(Error::new(format!("Cannot subtract {} from {}", other, self))),
        }
    }

    /// Performs a multiplication.
    pub fn mul(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Double(lhs * rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => match lhs.checked_mul(*rhs) {
                Some(i) => Ok(Value::Integer(i)),
                None => Ok(Value::Double(*lhs as f64 * *rhs as f64)),
            },

            (Value::Double(lhs), Value::Integer(rhs)) => Ok(Value::Double(lhs * *rhs as f64)),
            (Value::Integer(lhs), Value::Double(rhs)) => Ok(Value::Double(*lhs as f64 * rhs)),

            (_, _) => Err(Error::new(format!("Cannot multiply {} by {}", self, other))),
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
                    None => Ok(Value::Double(*lhs as f64 / *rhs as f64)),
                }
            }

            (Value::Double(lhs), Value::Integer(rhs)) => Ok(Value::Double(lhs / *rhs as f64)),
            (Value::Integer(lhs), Value::Double(rhs)) => Ok(Value::Double(*lhs as f64 / rhs)),

            (_, _) => Err(Error::new(format!("Cannot divide {} by {}", self, other))),
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
                    None => Ok(Value::Double(*lhs as f64 % *rhs as f64)),
                }
            }

            (Value::Double(lhs), Value::Integer(rhs)) => Ok(Value::Double(lhs % *rhs as f64)),
            (Value::Integer(lhs), Value::Double(rhs)) => Ok(Value::Double(*lhs as f64 % rhs)),

            (_, _) => Err(Error::new(format!("Cannot modulo {} by {}", self, other))),
        }
    }

    /// Performs a power operation.
    pub fn pow(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Double(lhs.powf(*rhs))),
            (Value::Integer(lhs), Value::Integer(rhs)) => {
                let exp = match u32::try_from(*rhs) {
                    Ok(exp) => exp,
                    Err(_) => {
                        return Ok(Value::Double((*lhs as f64).powf(*rhs as f64)));
                    }
                };
                match lhs.checked_pow(exp) {
                    Some(i) => Ok(Value::Integer(i)),
                    None => Ok(Value::Double((*lhs as f64).powf(*rhs as f64))),
                }
            }

            (Value::Double(lhs), Value::Integer(rhs)) => Ok(Value::Double(lhs.powf(*rhs as f64))),
            (Value::Integer(lhs), Value::Double(rhs)) => {
                Ok(Value::Double((*lhs as f64).powf(*rhs)))
            }

            (_, _) => Err(Error::new(format!("Cannot raise {} to the power of {}", self, other))),
        }
    }

    /// Performs an arithmetic negation.
    pub fn neg(&self) -> Result<Self> {
        match self {
            Value::Double(d) => Ok(Value::Double(-d)),
            Value::Integer(i) => match i.checked_neg() {
                Some(i) => Ok(Value::Integer(i)),
                None => Ok(Value::Double(-(*i as f64))),
            },
            _ => Err(Error::new(format!("Cannot negate {}", self))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Value::*;
    use super::*;

    #[test]
    fn test_value_parse_as_auto() {
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
        assert_eq!(Text("".to_owned()), Value::parse_as(VarType::Text, "").unwrap());
        assert_eq!(Text("true".to_owned()), Value::parse_as(VarType::Text, "true").unwrap());
        assert_eq!(Text("32".to_owned()), Value::parse_as(VarType::Text, "32").unwrap());
        assert_eq!(Text("a b".to_owned()), Value::parse_as(VarType::Text, "a b").unwrap());
    }

    #[test]
    fn test_value_as_i32() {
        assert_eq!(8, Double(8.4).as_i32().unwrap());
        assert_eq!(9, Double(8.5).as_i32().unwrap());
        assert_eq!(9, Double(8.6).as_i32().unwrap());
        assert_eq!(7, Integer(7).as_i32().unwrap());

        Double(f64::NAN).as_i32().unwrap_err();
        Double(i32::MAX as f64 + 1.0).as_i32().unwrap_err();
        Double(i32::MIN as f64 - 1.0).as_i32().unwrap_err();

        Boolean(false).as_i32().unwrap_err();
        Text("a".to_owned()).as_i32().unwrap_err();
    }

    #[test]
    fn test_value_as_f64() {
        assert_eq!(8.4, Double(8.4).as_f64().unwrap());
        assert_eq!(7.0, Integer(7).as_f64().unwrap());

        Boolean(false).as_f64().unwrap_err();
        Text("a".to_owned()).as_f64().unwrap_err();
    }

    #[test]
    fn test_value_maybe_cast() {
        use std::i32;

        let all_types = [
            VarType::Auto,
            VarType::Boolean,
            VarType::Double,
            VarType::Integer,
            VarType::Text,
            VarType::Void,
        ];
        for target in all_types {
            assert_eq!(Boolean(true), Boolean(true).maybe_cast(target).unwrap());
            if target != VarType::Integer {
                assert_eq!(Double(3.8), Double(3.8).maybe_cast(target).unwrap());
                match Double(f64::NAN).maybe_cast(target).unwrap() {
                    Double(d) => assert!(d.is_nan()),
                    _ => panic!(),
                }
            }
            if target != VarType::Double {
                assert_eq!(Integer(3), Integer(3).maybe_cast(target).unwrap());
            }
            assert_eq!(Text("a".to_owned()), Text("a".to_owned()).maybe_cast(target).unwrap());
        }

        assert_eq!(Integer(8), Double(8.4).maybe_cast(VarType::Integer).unwrap());
        assert_eq!(Integer(9), Double(8.5).maybe_cast(VarType::Integer).unwrap());
        assert_eq!(Integer(9), Double(8.6).maybe_cast(VarType::Integer).unwrap());
        assert_eq!(Double(7.0), Integer(7).maybe_cast(VarType::Double).unwrap());

        Double(f64::NAN).maybe_cast(VarType::Integer).unwrap_err();
        assert_eq!(Double(i32::MAX as f64), Integer(i32::MAX).maybe_cast(VarType::Double).unwrap());
        Double(i32::MAX as f64 + 1.0).maybe_cast(VarType::Integer).unwrap_err();
        assert_eq!(Double(i32::MIN as f64), Integer(i32::MIN).maybe_cast(VarType::Double).unwrap());
        Double(i32::MIN as f64 - 1.0).maybe_cast(VarType::Integer).unwrap_err();
    }

    #[test]
    fn test_value_to_text_and_parse() {
        let v = Boolean(false);
        assert_eq!(v.clone(), Value::parse_as(VarType::Boolean, &v.to_text()).unwrap());

        let v = Double(-10.1);
        assert_eq!(v.clone(), Value::parse_as(VarType::Double, &v.to_text()).unwrap());

        let v = Integer(-9);
        assert_eq!(v.clone(), Value::parse_as(VarType::Integer, &v.to_text()).unwrap());

        let v = Text("Some long text".to_owned());
        assert_eq!(v.clone(), Value::parse_as(VarType::Text, &v.to_text()).unwrap());
    }

    #[test]
    fn test_value_display_and_parse() {
        let v = Boolean(false);
        assert_eq!(v, Value::parse_as(VarType::Boolean, format!("{}", v)).unwrap());

        let v = Double(10.1);
        assert_eq!(v, Value::parse_as(VarType::Double, format!("{}", v)).unwrap());

        let v = Integer(9);
        assert_eq!(v, Value::parse_as(VarType::Integer, format!("{}", v)).unwrap());

        // The string parsing and printing is not symmetrical on purpose given that user input
        // does not provide strings as quoted but we want to show them as quoted for clarity.
        let v = Text("Some long text".to_owned());
        assert_eq!(
            Text("\"Some long text\"".to_owned()),
            Value::parse_as(VarType::Text, format!("{}", v)).unwrap()
        );
    }

    #[test]
    fn test_value_logical_and() {
        assert_eq!(Boolean(false), Boolean(false).and(&Boolean(false)).unwrap());
        assert_eq!(Boolean(false), Boolean(false).and(&Boolean(true)).unwrap());
        assert_eq!(Boolean(false), Boolean(true).and(&Boolean(false)).unwrap());
        assert_eq!(Boolean(true), Boolean(true).and(&Boolean(true)).unwrap());

        assert_eq!(
            "Cannot AND TRUE and 5",
            format!("{}", Boolean(true).and(&Integer(5)).unwrap_err())
        );
    }

    #[test]
    fn test_value_logical_or() {
        assert_eq!(Boolean(false), Boolean(false).or(&Boolean(false)).unwrap());
        assert_eq!(Boolean(true), Boolean(false).or(&Boolean(true)).unwrap());
        assert_eq!(Boolean(true), Boolean(true).or(&Boolean(false)).unwrap());
        assert_eq!(Boolean(true), Boolean(true).or(&Boolean(true)).unwrap());

        assert_eq!(
            "Cannot OR TRUE and 5",
            format!("{}", Boolean(true).or(&Integer(5)).unwrap_err())
        );
    }

    #[test]
    fn test_value_logical_xor() {
        assert_eq!(Boolean(false), Boolean(false).xor(&Boolean(false)).unwrap());
        assert_eq!(Boolean(true), Boolean(false).xor(&Boolean(true)).unwrap());
        assert_eq!(Boolean(true), Boolean(true).xor(&Boolean(false)).unwrap());
        assert_eq!(Boolean(false), Boolean(true).xor(&Boolean(true)).unwrap());

        assert_eq!(
            "Cannot XOR TRUE and 5",
            format!("{}", Boolean(true).xor(&Integer(5)).unwrap_err())
        );
    }

    #[test]
    fn test_value_logical_not() {
        assert_eq!(Boolean(true), Boolean(false).not().unwrap());
        assert_eq!(Boolean(false), Boolean(true).not().unwrap());
    }

    #[test]
    fn test_value_bitwise_and() {
        assert_eq!(Integer(5), Integer(7).and(&Integer(5)).unwrap());
        assert_eq!(Integer(0), Integer(2).and(&Integer(4)).unwrap());
        assert_eq!(Integer(1234), Integer(-1).and(&Integer(1234)).unwrap());

        assert_eq!(
            "Cannot AND 3.0 and 4.0",
            format!("{}", Double(3.0).and(&Double(4.0)).unwrap_err())
        );
    }

    #[test]
    fn test_value_bitwise_or() {
        assert_eq!(Integer(7), Integer(7).or(&Integer(5)).unwrap());
        assert_eq!(Integer(6), Integer(2).or(&Integer(4)).unwrap());
        assert_eq!(Integer(-1), Integer(-1).or(&Integer(1234)).unwrap());

        assert_eq!(
            "Cannot OR 3.0 and 4.0",
            format!("{}", Double(3.0).or(&Double(4.0)).unwrap_err())
        );
    }

    #[test]
    fn test_value_bitwise_xor() {
        assert_eq!(Integer(2), Integer(7).xor(&Integer(5)).unwrap());
        assert_eq!(Integer(6), Integer(2).xor(&Integer(4)).unwrap());
        assert_eq!(Integer(-1235), Integer(-1).xor(&Integer(1234)).unwrap());

        assert_eq!(
            "Cannot XOR 3.0 and 4.0",
            format!("{}", Double(3.0).xor(&Double(4.0)).unwrap_err())
        );
    }

    #[test]
    fn test_value_bitwise_not() {
        assert_eq!(Integer(-1), Integer(0).not().unwrap());

        assert_eq!("Cannot apply NOT to 3.0", format!("{}", Double(3.0).not().unwrap_err()));
    }

    #[test]
    fn test_value_eq() {
        assert_eq!(Boolean(true), Boolean(false).eq(&Boolean(false)).unwrap());
        assert_eq!(Boolean(false), Boolean(true).eq(&Boolean(false)).unwrap());
        assert_eq!(
            "Cannot compare TRUE and 5 with =",
            format!("{}", Boolean(true).eq(&Integer(5)).unwrap_err())
        );

        assert_eq!(Boolean(true), Double(2.5).eq(&Double(2.5)).unwrap());
        assert_eq!(Boolean(false), Double(3.5).eq(&Double(3.6)).unwrap());
        assert_eq!(Boolean(true), Double(4.0).eq(&Integer(4)).unwrap());
        assert_eq!(Boolean(false), Double(1.2).eq(&Integer(1)).unwrap());

        assert_eq!(Boolean(true), Integer(2).eq(&Integer(2)).unwrap());
        assert_eq!(Boolean(false), Integer(3).eq(&Integer(4)).unwrap());
        assert_eq!(Boolean(true), Integer(4).eq(&Double(4.0)).unwrap());
        assert_eq!(Boolean(false), Integer(1).eq(&Double(1.2)).unwrap());

        assert_eq!(Boolean(true), Text("a".to_owned()).eq(&Text("a".to_owned())).unwrap());
        assert_eq!(Boolean(false), Text("b".to_owned()).eq(&Text("c".to_owned())).unwrap());
        assert_eq!(
            "Cannot compare \"\" and FALSE with =",
            format!("{}", Text("".to_owned()).eq(&Boolean(false)).unwrap_err())
        );
    }

    #[test]
    fn test_value_ne() {
        assert_eq!(Boolean(false), Boolean(false).ne(&Boolean(false)).unwrap());
        assert_eq!(Boolean(true), Boolean(true).ne(&Boolean(false)).unwrap());
        assert_eq!(
            "Cannot compare TRUE and 5 with <>",
            format!("{}", Boolean(true).ne(&Integer(5)).unwrap_err())
        );

        assert_eq!(Boolean(false), Double(2.5).ne(&Double(2.5)).unwrap());
        assert_eq!(Boolean(true), Double(3.5).ne(&Double(3.6)).unwrap());
        assert_eq!(Boolean(false), Double(4.0).ne(&Integer(4)).unwrap());
        assert_eq!(Boolean(true), Double(1.2).ne(&Integer(1)).unwrap());

        assert_eq!(Boolean(false), Integer(2).ne(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(3).ne(&Integer(4)).unwrap());
        assert_eq!(Boolean(false), Integer(4).ne(&Double(4.0)).unwrap());
        assert_eq!(Boolean(true), Integer(4).ne(&Double(4.2)).unwrap());

        assert_eq!(Boolean(false), Text("a".to_owned()).ne(&Text("a".to_owned())).unwrap());
        assert_eq!(Boolean(true), Text("b".to_owned()).ne(&Text("c".to_owned())).unwrap());
        assert_eq!(
            "Cannot compare \"\" and FALSE with <>",
            format!("{}", Text("".to_owned()).ne(&Boolean(false)).unwrap_err())
        );
    }

    #[test]
    fn test_value_lt() {
        assert_eq!(
            "Cannot compare FALSE and TRUE with <",
            format!("{}", Boolean(false).lt(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Boolean(false), Double(2.5).lt(&Double(2.5)).unwrap());
        assert_eq!(Boolean(true), Double(3.5).lt(&Double(3.6)).unwrap());
        assert_eq!(Boolean(false), Double(4.0).lt(&Integer(1)).unwrap());
        assert_eq!(Boolean(false), Double(4.0).lt(&Integer(4)).unwrap());
        assert_eq!(Boolean(true), Double(4.9).lt(&Integer(5)).unwrap());

        assert_eq!(Boolean(false), Integer(2).lt(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(3).lt(&Integer(4)).unwrap());
        assert_eq!(Boolean(false), Integer(4).lt(&Double(3.9)).unwrap());
        assert_eq!(Boolean(false), Integer(4).lt(&Double(4.0)).unwrap());
        assert_eq!(Boolean(true), Integer(4).lt(&Double(4.1)).unwrap());

        assert_eq!(Boolean(false), Text("a".to_owned()).lt(&Text("a".to_owned())).unwrap());
        assert_eq!(Boolean(true), Text("a".to_owned()).lt(&Text("c".to_owned())).unwrap());
        assert_eq!(
            "Cannot compare \"\" and FALSE with <",
            format!("{}", Text("".to_owned()).lt(&Boolean(false)).unwrap_err())
        );
    }

    #[test]
    fn test_value_le() {
        assert_eq!(
            "Cannot compare FALSE and TRUE with <=",
            format!("{}", Boolean(false).le(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Boolean(false), Double(2.1).le(&Double(2.0)).unwrap());
        assert_eq!(Boolean(true), Double(2.1).le(&Double(2.1)).unwrap());
        assert_eq!(Boolean(true), Double(2.1).le(&Double(2.2)).unwrap());
        assert_eq!(Boolean(false), Double(3.1).le(&Integer(3)).unwrap());
        assert_eq!(Boolean(true), Double(3.9).le(&Integer(4)).unwrap());
        assert_eq!(Boolean(true), Double(4.0).le(&Integer(4)).unwrap());

        assert_eq!(Boolean(false), Integer(2).le(&Integer(1)).unwrap());
        assert_eq!(Boolean(true), Integer(2).le(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(2).le(&Integer(3)).unwrap());
        assert_eq!(Boolean(false), Integer(4).le(&Double(3.9)).unwrap());
        assert_eq!(Boolean(true), Integer(4).le(&Double(4.0)).unwrap());
        assert_eq!(Boolean(true), Integer(4).le(&Double(4.1)).unwrap());

        assert_eq!(Boolean(false), Text("b".to_owned()).le(&Text("a".to_owned())).unwrap());
        assert_eq!(Boolean(true), Text("a".to_owned()).le(&Text("a".to_owned())).unwrap());
        assert_eq!(Boolean(true), Text("a".to_owned()).le(&Text("c".to_owned())).unwrap());
        assert_eq!(
            "Cannot compare \"\" and FALSE with <=",
            format!("{}", Text("".to_owned()).le(&Boolean(false)).unwrap_err())
        );
    }

    #[test]
    fn test_value_gt() {
        assert_eq!(
            "Cannot compare FALSE and TRUE with >",
            format!("{}", Boolean(false).gt(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Boolean(false), Double(2.1).gt(&Double(2.1)).unwrap());
        assert_eq!(Boolean(true), Double(4.1).gt(&Double(4.0)).unwrap());
        assert_eq!(Boolean(false), Double(3.9).gt(&Integer(4)).unwrap());
        assert_eq!(Boolean(false), Double(4.0).gt(&Integer(4)).unwrap());
        assert_eq!(Boolean(true), Double(4.1).gt(&Integer(4)).unwrap());

        assert_eq!(Boolean(false), Integer(2).gt(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(4).gt(&Integer(3)).unwrap());
        assert_eq!(Boolean(false), Integer(4).gt(&Double(4.0)).unwrap());
        assert_eq!(Boolean(false), Integer(4).gt(&Double(4.1)).unwrap());
        assert_eq!(Boolean(true), Integer(4).gt(&Double(3.9)).unwrap());

        assert_eq!(Boolean(false), Text("a".to_owned()).gt(&Text("a".to_owned())).unwrap());
        assert_eq!(Boolean(true), Text("c".to_owned()).gt(&Text("a".to_owned())).unwrap());
        assert_eq!(
            "Cannot compare \"\" and FALSE with >",
            format!("{}", Text("".to_owned()).gt(&Boolean(false)).unwrap_err())
        );
    }

    #[test]
    fn test_value_ge() {
        assert_eq!(
            "Cannot compare FALSE and TRUE with >=",
            format!("{}", Boolean(false).ge(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Boolean(false), Double(2.0).ge(&Double(2.1)).unwrap());
        assert_eq!(Boolean(true), Double(2.1).ge(&Double(2.1)).unwrap());
        assert_eq!(Boolean(true), Double(2.2).ge(&Double(2.1)).unwrap());
        assert_eq!(Boolean(false), Double(3.9).ge(&Integer(4)).unwrap());
        assert_eq!(Boolean(true), Double(4.0).ge(&Integer(4)).unwrap());
        assert_eq!(Boolean(true), Double(4.1).ge(&Integer(4)).unwrap());

        assert_eq!(Boolean(false), Integer(1).ge(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(2).ge(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(4).ge(&Integer(3)).unwrap());
        assert_eq!(Boolean(false), Integer(4).ge(&Double(4.1)).unwrap());
        assert_eq!(Boolean(true), Integer(4).ge(&Double(4.0)).unwrap());
        assert_eq!(Boolean(true), Integer(4).ge(&Double(3.9)).unwrap());

        assert_eq!(Boolean(false), Text("".to_owned()).ge(&Text("b".to_owned())).unwrap());
        assert_eq!(Boolean(true), Text("a".to_owned()).ge(&Text("a".to_owned())).unwrap());
        assert_eq!(Boolean(true), Text("c".to_owned()).ge(&Text("a".to_owned())).unwrap());
        assert_eq!(
            "Cannot compare \"\" and FALSE with >=",
            format!("{}", Text("".to_owned()).ge(&Boolean(false)).unwrap_err())
        );
    }

    #[test]
    fn test_value_add() {
        assert_eq!(
            "Cannot add FALSE and TRUE",
            format!("{}", Boolean(false).add(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Double(7.1), Double(2.1).add(&Double(5.0)).unwrap());
        assert_eq!(Double(9.5), Double(4.5).add(&Integer(5)).unwrap());

        assert_eq!(Integer(5), Integer(2).add(&Integer(3)).unwrap());
        assert_eq!(Integer(std::i32::MAX), Integer(std::i32::MAX).add(&Integer(0)).unwrap());
        assert_eq!(
            Double(std::i32::MAX as f64 + 1.0),
            Integer(std::i32::MAX).add(&Integer(1)).unwrap()
        );
        assert_eq!(Double(9.3), Integer(4).add(&Double(5.3)).unwrap());

        assert_eq!(Text("ab".to_owned()), Text("a".to_owned()).add(&Text("b".to_owned())).unwrap());
        assert_eq!(
            "Cannot add \"\" and FALSE",
            format!("{}", Text("".to_owned()).add(&Boolean(false)).unwrap_err())
        );
    }

    #[test]
    fn test_value_sub() {
        assert_eq!(
            "Cannot subtract TRUE from FALSE",
            format!("{}", Boolean(false).sub(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Double(-1.0), Double(2.5).sub(&Double(3.5)).unwrap());
        assert_eq!(Double(-1.5), Double(3.5).sub(&Integer(5)).unwrap());

        assert_eq!(Integer(-1), Integer(2).sub(&Integer(3)).unwrap());
        assert_eq!(Integer(std::i32::MIN), Integer(std::i32::MIN).sub(&Integer(0)).unwrap());
        assert_eq!(
            Double(std::i32::MIN as f64 - 1.0),
            Integer(std::i32::MIN).sub(&Integer(1)).unwrap()
        );
        assert_eq!(Double(-1.5), Integer(4).sub(&Double(5.5)).unwrap());

        assert_eq!(
            "Cannot subtract \"a\" from \"ab\"",
            format!("{}", Text("ab".to_owned()).sub(&Text("a".to_owned())).unwrap_err())
        );
    }

    #[test]
    fn test_value_mul() {
        assert_eq!(
            "Cannot multiply FALSE by TRUE",
            format!("{}", Boolean(false).mul(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Double(40.0), Double(4.0).mul(&Double(10.0)).unwrap());
        assert_eq!(Double(20.5), Double(4.1).mul(&Integer(5)).unwrap());

        assert_eq!(Integer(6), Integer(2).mul(&Integer(3)).unwrap());
        assert_eq!(Integer(std::i32::MAX), Integer(std::i32::MAX).mul(&Integer(1)).unwrap());
        assert_eq!(
            Double(std::i32::MAX as f64 * 2.0),
            Integer(std::i32::MAX).mul(&Integer(2)).unwrap()
        );
        assert_eq!(Double(20.8), Integer(4).mul(&Double(5.2)).unwrap());

        assert_eq!(
            "Cannot multiply \"\" by \"a\"",
            format!("{}", Text("".to_owned()).mul(&Text("a".to_owned())).unwrap_err())
        );
    }

    #[test]
    fn test_value_div() {
        assert_eq!(
            "Cannot divide FALSE by TRUE",
            format!("{}", Boolean(false).div(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Double(4.0), Double(10.0).div(&Double(2.5)).unwrap());
        assert_eq!(Double(f64::INFINITY), Double(1.0).div(&Double(0.0)).unwrap());
        assert_eq!(Double(5.1), Double(10.2).div(&Integer(2)).unwrap());

        assert_eq!(Integer(2), Integer(10).div(&Integer(5)).unwrap());
        assert_eq!(Integer(6), Integer(20).div(&Integer(3)).unwrap());
        assert_eq!(Integer(std::i32::MIN), Integer(std::i32::MIN).div(&Integer(1)).unwrap());
        assert_eq!("Division by zero", format!("{}", Integer(4).div(&Integer(0)).unwrap_err()));
        assert_eq!(
            Double(std::i32::MIN as f64 / -1.0),
            Integer(std::i32::MIN).div(&Integer(-1)).unwrap()
        );
        assert_eq!(Double(4.0), Integer(10).div(&Double(2.5)).unwrap());

        assert_eq!(
            "Cannot divide \"\" by \"a\"",
            format!("{}", Text("".to_owned()).div(&Text("a".to_owned())).unwrap_err())
        );
    }

    #[test]
    fn test_value_modulo() {
        assert_eq!(
            "Cannot modulo FALSE by TRUE",
            format!("{}", Boolean(false).modulo(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Double(0.0), Double(10.0).modulo(&Double(2.5)).unwrap());
        match Double(1.0).modulo(&Double(0.0)).unwrap() {
            Double(d) => assert!(d.is_nan()),
            _ => panic!("Did not get a double"),
        };
        assert_eq!(Double(10.3 % 2.0), Double(10.3).modulo(&Integer(2)).unwrap());

        assert_eq!(Integer(0), Integer(10).modulo(&Integer(5)).unwrap());
        assert_eq!(Integer(2), Integer(20).modulo(&Integer(3)).unwrap());
        assert_eq!("Modulo by zero", format!("{}", Integer(4).modulo(&Integer(0)).unwrap_err()));
        assert_eq!(
            Double(std::i32::MIN as f64 % -1.0),
            Integer(std::i32::MIN).modulo(&Integer(-1)).unwrap()
        );
        assert_eq!(Double(10.0 % 3.0), Integer(10).modulo(&Double(3.0)).unwrap());

        assert_eq!(
            "Cannot modulo \"\" by \"a\"",
            format!("{}", Text("".to_owned()).modulo(&Text("a".to_owned())).unwrap_err())
        );
    }

    #[test]
    fn test_value_power() {
        assert_eq!(
            "Cannot raise FALSE to the power of TRUE",
            format!("{}", Boolean(false).pow(&Boolean(true)).unwrap_err())
        );

        assert_eq!(Double(1.0), Double(0.0).pow(&Double(0.0)).unwrap());
        assert_eq!(Double(2.0f64.powf(3.1)), Double(2.0).pow(&Double(3.1)).unwrap());
        assert_eq!(Double(1024.0), Double(4.0).pow(&Integer(5)).unwrap());

        assert_eq!(Integer(1), Integer(0).pow(&Integer(0)).unwrap());
        assert_eq!(Integer(9), Integer(3).pow(&Integer(2)).unwrap());
        assert_eq!(Integer(std::i32::MAX), Integer(std::i32::MAX).pow(&Integer(1)).unwrap());
        assert_eq!(
            Double((std::i32::MAX as f64).powf(2.0)),
            Integer(std::i32::MAX).pow(&Integer(2)).unwrap()
        );
        assert_eq!(Double(1f64.powf(-3.0)), Integer(1).pow(&Integer(-3)).unwrap());
        assert_eq!(Double(1024.0), Integer(4).pow(&Double(5.0)).unwrap());

        assert_eq!(
            "Cannot raise \"\" to the power of \"a\"",
            format!("{}", Text("".to_owned()).pow(&Text("a".to_owned())).unwrap_err())
        );
    }

    #[test]
    fn test_value_neg() {
        assert_eq!("Cannot negate TRUE", format!("{}", Boolean(true).neg().unwrap_err()));

        assert_eq!(Double(-6.12), Double(6.12).neg().unwrap());
        assert_eq!(Double(5.53), Double(-5.53).neg().unwrap());

        assert_eq!(Integer(-6), Integer(6).neg().unwrap());
        assert_eq!(Integer(5), Integer(-5).neg().unwrap());
        assert_eq!(Double(-(std::i32::MIN as f64)), Integer(std::i32::MIN).neg().unwrap());

        assert_eq!("Cannot negate \"\"", format!("{}", Text("".to_owned()).neg().unwrap_err()));
    }
}
