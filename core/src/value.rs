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
use paste::paste;
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
            Value::VarRef(_) => panic!("Should never get unevaluated varrefs"),
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
}

/// Performs a logical "and" operation.
pub(crate) fn logical_and(lhs: Value, rhs: Value) -> Value {
    match (lhs, rhs) {
        (Value::Boolean(lhs), Value::Boolean(rhs)) => Value::Boolean(lhs && rhs),
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs a logical "or" operation.
pub(crate) fn logical_or(lhs: Value, rhs: Value) -> Value {
    match (lhs, rhs) {
        (Value::Boolean(lhs), Value::Boolean(rhs)) => Value::Boolean(lhs || rhs),
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs a logical "xor" operation.
pub(crate) fn logical_xor(lhs: Value, rhs: Value) -> Value {
    match (lhs, rhs) {
        (Value::Boolean(lhs), Value::Boolean(rhs)) => Value::Boolean(lhs ^ rhs),
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs a logical "not" operation.
pub(crate) fn logical_not(value: Value) -> Value {
    match value {
        Value::Boolean(b) => Value::Boolean(!b),
        _ => unreachable!("Types validated during compilation"),
    }
}

/// Performs a bitwise "and" operation.
pub(crate) fn bitwise_and(lhs: Value, rhs: Value) -> Value {
    match (lhs, rhs) {
        (Value::Integer(lhs), Value::Integer(rhs)) => Value::Integer(lhs & rhs),
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs a bitwise "or" operation.
pub(crate) fn bitwise_or(lhs: Value, rhs: Value) -> Value {
    match (lhs, rhs) {
        (Value::Integer(lhs), Value::Integer(rhs)) => Value::Integer(lhs | rhs),
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs a bitwise "xor" operation.
pub(crate) fn bitwise_xor(lhs: Value, rhs: Value) -> Value {
    match (lhs, rhs) {
        (Value::Integer(lhs), Value::Integer(rhs)) => Value::Integer(lhs ^ rhs),
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs a bitwise "not" operation.
pub(crate) fn bitwise_not(value: Value) -> Value {
    match value {
        Value::Integer(b) => Value::Integer(!b),
        _ => unreachable!("Types validated during compilation"),
    }
}

/// Performs a left shift.
pub(crate) fn bitwise_shl(lhs: Value, rhs: Value) -> Result<Value> {
    let (lhs, rhs) = match (lhs, rhs) {
        (Value::Integer(lhs), Value::Integer(rhs)) => (lhs, rhs),
        (_, _) => unreachable!("Types validated during compilation"),
    };

    let bits = match u32::try_from(rhs) {
        Ok(n) => n,
        Err(_) => {
            return Err(Error::new(format!("Number of bits to << ({}) must be positive", rhs)))
        }
    };

    match lhs.checked_shl(bits) {
        Some(i) => Ok(Value::Integer(i)),
        None => Ok(Value::Integer(0)),
    }
}

/// Performs a right shift.
pub(crate) fn bitwise_shr(lhs: Value, rhs: Value) -> Result<Value> {
    let (lhs, rhs) = match (lhs, rhs) {
        (Value::Integer(lhs), Value::Integer(rhs)) => (lhs, rhs),
        (_, _) => unreachable!("Types validated during compilation"),
    };

    let bits = match u32::try_from(rhs) {
        Ok(n) => n,
        Err(_) => {
            return Err(Error::new(format!("Number of bits to >> ({}) must be positive", rhs)))
        }
    };

    match lhs.checked_shr(bits) {
        Some(i) => Ok(Value::Integer(i)),
        None if lhs < 0 => Ok(Value::Integer(-1)),
        None => Ok(Value::Integer(0)),
    }
}

macro_rules! equality_ops {
    ( $name:ident, $vtype:expr ) => {
        paste! {
            /// Performs an equality check.
            pub(crate) fn [< eq_ $name >](lhs: Value, rhs: Value) -> Value {
                match (lhs, rhs) {
                    ($vtype(lhs), $vtype(rhs)) => Value::Boolean(lhs == rhs),
                    (_, _) => unreachable!("Types validated during compilation"),
                }
            }

            /// Performs an inequality check.
            pub(crate) fn [< ne_ $name >](lhs: Value, rhs: Value) -> Value {
                match (lhs, rhs) {
                    ($vtype(lhs), $vtype(rhs)) => Value::Boolean(lhs != rhs),
                    (_, _) => unreachable!("Types validated during compilation"),
                }
            }
        }
    };
}

equality_ops!(boolean, Value::Boolean);
equality_ops!(double, Value::Double);
equality_ops!(integer, Value::Integer);
equality_ops!(text, Value::Text);

macro_rules! relational_ops {
    ( $name:ident, $vtype:expr ) => {
        paste! {
            /// Performs an equality check.
            pub(crate) fn [< lt_ $name >](lhs: Value, rhs: Value) -> Value {
                match (lhs, rhs) {
                    ($vtype(lhs), $vtype(rhs)) => Value::Boolean(lhs < rhs),
                    (_, _) => unreachable!("Types validated during compilation"),
                }
            }

            /// Performs an equality check.
            pub(crate) fn [< le_ $name >](lhs: Value, rhs: Value) -> Value {
                match (lhs, rhs) {
                    ($vtype(lhs), $vtype(rhs)) => Value::Boolean(lhs <= rhs),
                    (_, _) => unreachable!("Types validated during compilation"),
                }
            }

            /// Performs an equality check.
            pub(crate) fn [< gt_ $name >](lhs: Value, rhs: Value) -> Value {
                match (lhs, rhs) {
                    ($vtype(lhs), $vtype(rhs)) => Value::Boolean(lhs > rhs),
                    (_, _) => unreachable!("Types validated during compilation"),
                }
            }

            /// Performs an equality check.
            pub(crate) fn [< ge_ $name >](lhs: Value, rhs: Value) -> Value {
                match (lhs, rhs) {
                    ($vtype(lhs), $vtype(rhs)) => Value::Boolean(lhs >= rhs),
                    (_, _) => unreachable!("Types validated during compilation"),
                }
            }
        }
    };
}

relational_ops!(double, Value::Double);
relational_ops!(integer, Value::Integer);
relational_ops!(text, Value::Text);

/// Performs an arithmetic addition of doubles.
pub fn add_double(lhs: Value, rhs: Value) -> Value {
    match (lhs, rhs) {
        (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs + rhs),
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs an arithmetic subtraction of doubles.
pub fn sub_double(lhs: Value, rhs: Value) -> Value {
    match (lhs, rhs) {
        (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs - rhs),
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs a multiplication of doubles.
pub fn mul_double(lhs: Value, rhs: Value) -> Value {
    match (lhs, rhs) {
        (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs * rhs),
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs an arithmetic division of doubles.
pub fn div_double(lhs: Value, rhs: Value) -> Value {
    match (lhs, rhs) {
        (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs / rhs),
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs a modulo operation of doubles.
pub fn modulo_double(lhs: Value, rhs: Value) -> Value {
    match (lhs, rhs) {
        (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs % rhs),
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs a power operation of doubles.
pub fn pow_double(lhs: Value, rhs: Value) -> Value {
    match (lhs, rhs) {
        (Value::Double(lhs), Value::Double(rhs)) => Value::Double(lhs.powf(rhs)),
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs an arithmetic negation of a double.
pub fn neg_double(value: Value) -> Value {
    match value {
        Value::Double(d) => Value::Double(-d),
        _ => unreachable!("Types validated during compilation"),
    }
}

/// Performs an arithmetic addition of integers.
pub fn add_integer(lhs: Value, rhs: Value) -> Result<Value> {
    match (lhs, rhs) {
        (Value::Integer(lhs), Value::Integer(rhs)) => match lhs.checked_add(rhs) {
            Some(i) => Ok(Value::Integer(i)),
            None => Err(Error::new("Integer overflow".to_owned())),
        },
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs an arithmetic subtraction of integers.
pub fn sub_integer(lhs: Value, rhs: Value) -> Result<Value> {
    match (lhs, rhs) {
        (Value::Integer(lhs), Value::Integer(rhs)) => match lhs.checked_sub(rhs) {
            Some(i) => Ok(Value::Integer(i)),
            None => Err(Error::new("Integer underflow".to_owned())),
        },
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs a multiplication of integers.
pub fn mul_integer(lhs: Value, rhs: Value) -> Result<Value> {
    match (lhs, rhs) {
        (Value::Integer(lhs), Value::Integer(rhs)) => match lhs.checked_mul(rhs) {
            Some(i) => Ok(Value::Integer(i)),
            None => Err(Error::new("Integer overflow".to_owned())),
        },
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs an arithmetic division of integers.
pub fn div_integer(lhs: Value, rhs: Value) -> Result<Value> {
    match (lhs, rhs) {
        (Value::Integer(lhs), Value::Integer(rhs)) => {
            if rhs == 0 {
                return Err(Error::new("Division by zero"));
            }
            match lhs.checked_div(rhs) {
                Some(i) => Ok(Value::Integer(i)),
                None => Err(Error::new("Integer underflow".to_owned())),
            }
        }
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs a modulo operation of integers.
pub fn modulo_integer(lhs: Value, rhs: Value) -> Result<Value> {
    match (lhs, rhs) {
        (Value::Integer(lhs), Value::Integer(rhs)) => {
            if rhs == 0 {
                return Err(Error::new("Modulo by zero"));
            }
            match lhs.checked_rem(rhs) {
                Some(i) => Ok(Value::Integer(i)),
                None => Err(Error::new("Integer underflow".to_owned())),
            }
        }
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs a power operation of integers.
pub fn pow_integer(lhs: Value, rhs: Value) -> Result<Value> {
    match (lhs, rhs) {
        (Value::Integer(lhs), Value::Integer(rhs)) => {
            let exp = match u32::try_from(rhs) {
                Ok(exp) => exp,
                Err(_) => {
                    return Err(Error::new(format!("Exponent {} cannot be negative", rhs)));
                }
            };
            match lhs.checked_pow(exp) {
                Some(i) => Ok(Value::Integer(i)),
                None => Err(Error::new("Integer overflow".to_owned())),
            }
        }
        (_, _) => unreachable!("Types validated during compilation"),
    }
}

/// Performs an arithmetic negation of an integer.
pub fn neg_integer(value: Value) -> Result<Value> {
    match value {
        Value::Integer(i) => match i.checked_neg() {
            Some(i) => Ok(Value::Integer(i)),
            None => Err(Error::new("Integer underflow".to_owned())),
        },
        _ => unreachable!("Types validated during compilation"),
    }
}

/// Performs the concatenation of strings.
pub fn add_text(lhs: Value, rhs: Value) -> Value {
    match (lhs, rhs) {
        (Value::Text(lhs), Value::Text(rhs)) => Value::Text(format!("{}{}", lhs, rhs)),
        (_, _) => unreachable!("Types validated during compilation"),
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
        assert_eq!(v.clone(), Value::parse_as(VarType::Boolean, v.to_text()).unwrap());

        let v = Double(-10.1);
        assert_eq!(v.clone(), Value::parse_as(VarType::Double, v.to_text()).unwrap());

        let v = Integer(-9);
        assert_eq!(v.clone(), Value::parse_as(VarType::Integer, v.to_text()).unwrap());

        let v = Text("Some long text".to_owned());
        assert_eq!(v.clone(), Value::parse_as(VarType::Text, v.to_text()).unwrap());
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
        assert_eq!(Boolean(false), logical_and(Boolean(false), Boolean(false)));
        assert_eq!(Boolean(false), logical_and(Boolean(false), Boolean(true)));
        assert_eq!(Boolean(false), logical_and(Boolean(true), Boolean(false)));
        assert_eq!(Boolean(true), logical_and(Boolean(true), Boolean(true)));
    }

    #[test]
    fn test_value_logical_or() {
        assert_eq!(Boolean(false), logical_or(Boolean(false), Boolean(false)));
        assert_eq!(Boolean(true), logical_or(Boolean(false), Boolean(true)));
        assert_eq!(Boolean(true), logical_or(Boolean(true), Boolean(false)));
        assert_eq!(Boolean(true), logical_or(Boolean(true), Boolean(true)));
    }

    #[test]
    fn test_value_logical_xor() {
        assert_eq!(Boolean(false), logical_xor(Boolean(false), Boolean(false)));
        assert_eq!(Boolean(true), logical_xor(Boolean(false), Boolean(true)));
        assert_eq!(Boolean(true), logical_xor(Boolean(true), Boolean(false)));
        assert_eq!(Boolean(false), logical_xor(Boolean(true), Boolean(true)));
    }

    #[test]
    fn test_value_logical_not() {
        assert_eq!(Boolean(true), logical_not(Boolean(false)));
        assert_eq!(Boolean(false), logical_not(Boolean(true)));
    }

    #[test]
    fn test_value_bitwise_and() {
        assert_eq!(Integer(5), bitwise_and(Integer(7), Integer(5)));
        assert_eq!(Integer(0), bitwise_and(Integer(2), Integer(4)));
        assert_eq!(Integer(1234), bitwise_and(Integer(-1), Integer(1234)));
    }

    #[test]
    fn test_value_bitwise_or() {
        assert_eq!(Integer(7), bitwise_or(Integer(7), Integer(5)));
        assert_eq!(Integer(6), bitwise_or(Integer(2), Integer(4)));
        assert_eq!(Integer(-1), bitwise_or(Integer(-1), Integer(1234)));
    }

    #[test]
    fn test_value_bitwise_xor() {
        assert_eq!(Integer(2), bitwise_xor(Integer(7), Integer(5)));
        assert_eq!(Integer(6), bitwise_xor(Integer(2), Integer(4)));
        assert_eq!(Integer(-1235), bitwise_xor(Integer(-1), Integer(1234)));
    }

    #[test]
    fn test_value_bitwise_not() {
        assert_eq!(Integer(-1), bitwise_not(Integer(0)));
    }

    #[test]
    fn test_value_shl() {
        assert_eq!(Integer(12), bitwise_shl(Integer(3), Integer(2)).unwrap());
        assert_eq!(
            Integer(0xf0000000u32 as i32),
            bitwise_shl(Integer(0xf0000000u32 as i32), Integer(0)).unwrap()
        );
        assert_eq!(Integer(0x80000000u32 as i32), bitwise_shl(Integer(1), Integer(31)).unwrap());
        assert_eq!(Integer(0), bitwise_shl(Integer(0xf0000000u32 as i32), Integer(31)).unwrap());

        assert_eq!(
            Integer(0xe0000000u32 as i32),
            bitwise_shl(Integer(0xf0000000u32 as i32), Integer(1)).unwrap()
        );
        assert_eq!(Integer(0), bitwise_shl(Integer(0x80000000u32 as i32), Integer(1)).unwrap());
        assert_eq!(Integer(0), bitwise_shl(Integer(1), Integer(32)).unwrap());
        assert_eq!(Integer(0), bitwise_shl(Integer(1), Integer(64)).unwrap());

        assert_eq!(
            "Number of bits to << (-1) must be positive",
            format!("{}", bitwise_shl(Integer(3), Integer(-1)).unwrap_err())
        );
    }

    #[test]
    fn test_value_shr() {
        assert_eq!(Integer(3), bitwise_shr(Integer(12), Integer(2)).unwrap());
        assert_eq!(
            Integer(0xf0000000u32 as i32),
            bitwise_shr(Integer(0xf0000000u32 as i32), Integer(0)).unwrap()
        );
        assert_eq!(Integer(-1), bitwise_shr(Integer(0xf0000000u32 as i32), Integer(31)).unwrap());
        assert_eq!(Integer(1), bitwise_shr(Integer(0x70000000u32 as i32), Integer(30)).unwrap());
        assert_eq!(Integer(-2), bitwise_shr(Integer(-8), Integer(2)).unwrap());

        assert_eq!(
            Integer(0xf0000000u32 as i32),
            bitwise_shr(Integer(0xe0000000u32 as i32), Integer(1)).unwrap()
        );
        assert_eq!(
            Integer(0xc0000000u32 as i32),
            bitwise_shr(Integer(0x80000000u32 as i32), Integer(1)).unwrap()
        );
        assert_eq!(Integer(0x38000000), bitwise_shr(Integer(0x70000000), Integer(1)).unwrap());
        assert_eq!(Integer(0), bitwise_shr(Integer(0x70000000u32 as i32), Integer(32)).unwrap());
        assert_eq!(Integer(0), bitwise_shr(Integer(0x70000000u32 as i32), Integer(32)).unwrap());
        assert_eq!(Integer(-1), bitwise_shr(Integer(0x80000000u32 as i32), Integer(32)).unwrap());
        assert_eq!(Integer(-1), bitwise_shr(Integer(0x80000000u32 as i32), Integer(64)).unwrap());

        assert_eq!(
            "Number of bits to >> (-1) must be positive",
            format!("{}", bitwise_shr(Integer(3), Integer(-1)).unwrap_err())
        );
    }

    #[test]
    fn test_value_eq_boolean() {
        assert_eq!(Boolean(true), eq_boolean(Boolean(false), Boolean(false)));
        assert_eq!(Boolean(false), eq_boolean(Boolean(true), Boolean(false)));
    }

    #[test]
    fn test_value_eq_double() {
        assert_eq!(Boolean(true), eq_double(Double(2.5), Double(2.5)));
        assert_eq!(Boolean(false), eq_double(Double(3.5), Double(3.6)));
    }

    #[test]
    fn test_value_eq_integer() {
        assert_eq!(Boolean(true), eq_integer(Integer(2), Integer(2)));
        assert_eq!(Boolean(false), eq_integer(Integer(3), Integer(4)));
    }

    #[test]
    fn test_value_eq_text() {
        assert_eq!(Boolean(true), eq_text(Text("a".to_owned()), Text("a".to_owned())));
        assert_eq!(Boolean(false), eq_text(Text("b".to_owned()), Text("c".to_owned())));
    }

    #[test]
    fn test_value_ne_boolean() {
        assert_eq!(Boolean(false), ne_boolean(Boolean(false), Boolean(false)));
        assert_eq!(Boolean(true), ne_boolean(Boolean(true), Boolean(false)));
    }

    #[test]
    fn test_value_ne_double() {
        assert_eq!(Boolean(false), ne_double(Double(2.5), Double(2.5)));
        assert_eq!(Boolean(true), ne_double(Double(3.5), Double(3.6)));
    }

    #[test]
    fn test_value_ne_integer() {
        assert_eq!(Boolean(false), ne_integer(Integer(2), Integer(2)));
        assert_eq!(Boolean(true), ne_integer(Integer(3), Integer(4)));
    }

    #[test]
    fn test_value_ne_text() {
        assert_eq!(Boolean(false), ne_text(Text("a".to_owned()), Text("a".to_owned())));
        assert_eq!(Boolean(true), ne_text(Text("b".to_owned()), Text("c".to_owned())));
    }

    #[test]
    fn test_value_lt_double() {
        assert_eq!(Boolean(false), lt_double(Double(2.5), Double(2.5)));
        assert_eq!(Boolean(true), lt_double(Double(3.5), Double(3.6)));
    }

    #[test]
    fn test_value_lt_integer() {
        assert_eq!(Boolean(false), lt_integer(Integer(2), Integer(2)));
        assert_eq!(Boolean(true), lt_integer(Integer(3), Integer(4)));
    }

    #[test]
    fn test_value_lt_text() {
        assert_eq!(Boolean(false), lt_text(Text("a".to_owned()), Text("a".to_owned())));
        assert_eq!(Boolean(true), lt_text(Text("a".to_owned()), Text("c".to_owned())));
    }

    #[test]
    fn test_value_le_double() {
        assert_eq!(Boolean(false), le_double(Double(2.1), Double(2.0)));
        assert_eq!(Boolean(true), le_double(Double(2.1), Double(2.1)));
        assert_eq!(Boolean(true), le_double(Double(2.1), Double(2.2)));
    }

    #[test]
    fn test_value_le_integer() {
        assert_eq!(Boolean(false), le_integer(Integer(2), Integer(1)));
        assert_eq!(Boolean(true), le_integer(Integer(2), Integer(2)));
        assert_eq!(Boolean(true), le_integer(Integer(2), Integer(3)));
    }

    #[test]
    fn test_value_le_text() {
        assert_eq!(Boolean(false), le_text(Text("b".to_owned()), Text("a".to_owned())));
        assert_eq!(Boolean(true), le_text(Text("a".to_owned()), Text("a".to_owned())));
        assert_eq!(Boolean(true), le_text(Text("a".to_owned()), Text("c".to_owned())));
    }

    #[test]
    fn test_value_gt_double() {
        assert_eq!(Boolean(false), gt_double(Double(2.1), Double(2.1)));
        assert_eq!(Boolean(true), gt_double(Double(4.1), Double(4.0)));
    }

    #[test]
    fn test_value_gt_integer() {
        assert_eq!(Boolean(false), gt_integer(Integer(2), Integer(2)));
        assert_eq!(Boolean(true), gt_integer(Integer(4), Integer(3)));
    }

    #[test]
    fn test_value_gt_text() {
        assert_eq!(Boolean(false), gt_text(Text("a".to_owned()), Text("a".to_owned())));
        assert_eq!(Boolean(true), gt_text(Text("c".to_owned()), Text("a".to_owned())));
    }

    #[test]
    fn test_value_ge_double() {
        assert_eq!(Boolean(false), ge_double(Double(2.0), Double(2.1)));
        assert_eq!(Boolean(true), ge_double(Double(2.1), Double(2.1)));
        assert_eq!(Boolean(true), ge_double(Double(2.2), Double(2.1)));
    }

    #[test]
    fn test_value_ge_integer() {
        assert_eq!(Boolean(false), ge_integer(Integer(1), Integer(2)));
        assert_eq!(Boolean(true), ge_integer(Integer(2), Integer(2)));
        assert_eq!(Boolean(true), ge_integer(Integer(4), Integer(3)));
    }

    #[test]
    fn test_value_ge_text() {
        assert_eq!(Boolean(false), ge_text(Text("".to_owned()), Text("b".to_owned())));
        assert_eq!(Boolean(true), ge_text(Text("a".to_owned()), Text("a".to_owned())));
        assert_eq!(Boolean(true), ge_text(Text("c".to_owned()), Text("a".to_owned())));
    }

    #[test]
    fn test_value_add_double() {
        assert_eq!(Double(7.1), add_double(Double(2.1), Double(5.0)));
    }

    #[test]
    fn test_value_sub_double() {
        assert_eq!(Double(-1.0), sub_double(Double(2.5), Double(3.5)));
    }

    #[test]
    fn test_value_mul_double() {
        assert_eq!(Double(40.0), mul_double(Double(4.0), Double(10.0)));
    }

    #[test]
    fn test_value_div_double() {
        assert_eq!(Double(4.0), div_double(Double(10.0), Double(2.5)));
        assert_eq!(Double(f64::INFINITY), div_double(Double(1.0), Double(0.0)));
    }

    #[test]
    fn test_value_modulo_double() {
        assert_eq!(Double(0.0), modulo_double(Double(10.0), Double(2.5)));
        match modulo_double(Double(1.0), Double(0.0)) {
            Double(d) => assert!(d.is_nan()),
            _ => panic!("Did not get a double"),
        };
    }

    #[test]
    fn test_value_pow_double() {
        assert_eq!(Double(1.0), pow_double(Double(0.0), Double(0.0)));
        assert_eq!(Double(2.0f64.powf(3.1)), pow_double(Double(2.0), Double(3.1)));
    }

    #[test]
    fn test_value_neg_double() {
        assert_eq!(Double(-6.12), neg_double(Double(6.12)));
        assert_eq!(Double(5.53), neg_double(Double(-5.53)));
    }

    #[test]
    fn test_value_add_integer() {
        assert_eq!(Integer(5), add_integer(Integer(2), Integer(3)).unwrap());
        assert_eq!(
            Integer(std::i32::MAX),
            add_integer(Integer(std::i32::MAX), Integer(0)).unwrap()
        );
        assert_eq!(
            "Integer overflow",
            format!("{}", add_integer(Integer(std::i32::MAX), Integer(1)).unwrap_err())
        );
    }

    #[test]
    fn test_value_sub_integer() {
        assert_eq!(Integer(-1), sub_integer(Integer(2), Integer(3)).unwrap());
        assert_eq!(
            Integer(std::i32::MIN),
            sub_integer(Integer(std::i32::MIN), Integer(0)).unwrap()
        );
        assert_eq!(
            "Integer underflow",
            format!("{}", sub_integer(Integer(std::i32::MIN), Integer(1)).unwrap_err())
        );
    }

    #[test]
    fn test_value_mul_integer() {
        assert_eq!(Integer(6), mul_integer(Integer(2), Integer(3)).unwrap());
        assert_eq!(
            Integer(std::i32::MAX),
            mul_integer(Integer(std::i32::MAX), Integer(1)).unwrap()
        );
        assert_eq!(
            "Integer overflow",
            format!("{}", mul_integer(Integer(std::i32::MAX), Integer(2)).unwrap_err())
        );
    }

    #[test]
    fn test_value_div_integer() {
        assert_eq!(Integer(2), div_integer(Integer(10), Integer(5)).unwrap());
        assert_eq!(Integer(6), div_integer(Integer(20), Integer(3)).unwrap());
        assert_eq!(
            Integer(std::i32::MIN),
            div_integer(Integer(std::i32::MIN), Integer(1)).unwrap()
        );
        assert_eq!(
            "Division by zero",
            format!("{}", div_integer(Integer(4), Integer(0)).unwrap_err())
        );
        assert_eq!(
            "Integer underflow",
            format!("{}", div_integer(Integer(std::i32::MIN), Integer(-1)).unwrap_err())
        );
    }

    #[test]
    fn test_value_modulo_integer() {
        assert_eq!(Integer(0), modulo_integer(Integer(10), Integer(5)).unwrap());
        assert_eq!(Integer(2), modulo_integer(Integer(20), Integer(3)).unwrap());
        assert_eq!(
            "Modulo by zero",
            format!("{}", modulo_integer(Integer(4), Integer(0)).unwrap_err())
        );
        assert_eq!(
            "Integer underflow",
            format!("{}", modulo_integer(Integer(std::i32::MIN), Integer(-1)).unwrap_err())
        );
    }

    #[test]
    fn test_value_pow_integer() {
        assert_eq!(Integer(1), pow_integer(Integer(0), Integer(0)).unwrap());
        assert_eq!(Integer(9), pow_integer(Integer(3), Integer(2)).unwrap());
        assert_eq!(
            Integer(std::i32::MAX),
            pow_integer(Integer(std::i32::MAX), Integer(1)).unwrap()
        );
        assert_eq!(
            "Integer overflow",
            format!("{}", pow_integer(Integer(std::i32::MAX), Integer(2)).unwrap_err())
        );
        assert_eq!(
            "Exponent -3 cannot be negative",
            format!("{}", pow_integer(Integer(1), Integer(-3)).unwrap_err())
        );
    }

    #[test]
    fn test_value_neg_integer() {
        assert_eq!(Integer(-6), neg_integer(Integer(6)).unwrap());
        assert_eq!(Integer(5), neg_integer(Integer(-5)).unwrap());
    }

    #[test]
    fn test_value_add_text() {
        assert_eq!(
            Text("foobar".to_owned()),
            add_text(Text("foo".to_owned()), Text("bar".to_owned()))
        );
    }
}
