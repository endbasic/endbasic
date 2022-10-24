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

    /// Performs a logical "and" operation.
    pub fn and(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(*lhs && *rhs)),
            (_, _) => Err(Error::new(format!("Cannot AND {} and {}", self, other))),
        }
    }

    /// Performs a logical "or" operation.
    pub fn or(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(*lhs || *rhs)),
            (_, _) => Err(Error::new(format!("Cannot OR {} and {}", self, other))),
        }
    }

    /// Performs a logical "xor" operation.
    pub fn xor(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(*lhs ^ *rhs)),
            (_, _) => Err(Error::new(format!("Cannot XOR {} and {}", self, other))),
        }
    }

    /// Performs a logical "not" operation.
    pub fn not(&self) -> Result<Self> {
        match self {
            Value::Boolean(b) => Ok(Value::Boolean(!b)),
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
            (_, _) => Err(Error::new(format!("Cannot compare {} and {} with <>", self, other))),
        }
    }

    /// Performs a less-than check.
    pub fn lt(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Boolean(lhs < rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs < rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs < rhs)),
            (_, _) => Err(Error::new(format!("Cannot compare {} and {} with <", self, other))),
        }
    }

    /// Performs a less-than or equal-to check.
    pub fn le(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Boolean(lhs <= rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs <= rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs <= rhs)),
            (_, _) => Err(Error::new(format!("Cannot compare {} and {} with <=", self, other))),
        }
    }

    /// Performs a greater-than check.
    pub fn gt(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Boolean(lhs > rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs > rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs > rhs)),
            (_, _) => Err(Error::new(format!("Cannot compare {} and {} with >", self, other))),
        }
    }

    /// Performs a greater-than or equal to check.
    pub fn ge(&self, other: &Self) -> Result<Self> {
        match (self, other) {
            (Value::Double(lhs), Value::Double(rhs)) => Ok(Value::Boolean(lhs >= rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs >= rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs >= rhs)),
            (_, _) => Err(Error::new(format!("Cannot compare {} and {} with >=", self, other))),
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
            (_, _) => Err(Error::new(format!("Cannot add {} and {}", self, other))),
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
            (_, _) => Err(Error::new(format!("Cannot subtract {} from {}", other, self))),
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
                    None => Err(Error::new(format!("Overflow dividing {} by {}", lhs, rhs))),
                }
            }
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
                    None => Err(Error::new(format!("Overflow modulo {} by {}", lhs, rhs))),
                }
            }
            (_, _) => Err(Error::new(format!("Cannot modulo {} by {}", self, other))),
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
    fn test_value_to_output_and_parse() {
        let v = Boolean(false);
        assert_eq!(v.clone(), Value::parse_as(VarType::Boolean, &v.to_output()).unwrap());

        let v = Double(10.1);
        assert_eq!(v.clone(), Value::parse_as(VarType::Double, &v.to_output()).unwrap());

        let v = Integer(9);
        assert_eq!(v.clone(), Value::parse_as(VarType::Integer, &v.to_output()).unwrap());

        let v = Text("Some long text".to_owned());
        assert_eq!(v.clone(), Value::parse_as(VarType::Text, &v.to_output()).unwrap());
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
    fn test_value_and() {
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
    fn test_value_or() {
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
    fn test_value_xor() {
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
    fn test_value_not() {
        assert_eq!(Boolean(true), Boolean(false).not().unwrap());
        assert_eq!(Boolean(false), Boolean(true).not().unwrap());

        assert_eq!("Cannot apply NOT to 5", format!("{}", Integer(5).not().unwrap_err()));
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
        assert_eq!(
            "Cannot compare 4.0 and 1 with =",
            format!("{}", Double(4.0).eq(&Integer(1)).unwrap_err())
        );

        assert_eq!(Boolean(true), Integer(2).eq(&Integer(2)).unwrap());
        assert_eq!(Boolean(false), Integer(3).eq(&Integer(4)).unwrap());
        assert_eq!(
            "Cannot compare 4 and 1.0 with =",
            format!("{}", Integer(4).eq(&Double(1.0)).unwrap_err())
        );

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
        assert_eq!(
            "Cannot compare 4.0 and 1 with <>",
            format!("{}", Double(4.0).ne(&Integer(1)).unwrap_err())
        );

        assert_eq!(Boolean(false), Integer(2).ne(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(3).ne(&Integer(4)).unwrap());
        assert_eq!(
            "Cannot compare 4 and 1.0 with <>",
            format!("{}", Integer(4).ne(&Double(1.0)).unwrap_err())
        );

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
        assert_eq!(
            "Cannot compare 4.0 and 1 with <",
            format!("{}", Double(4.0).lt(&Integer(1)).unwrap_err())
        );

        assert_eq!(Boolean(false), Integer(2).lt(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(3).lt(&Integer(4)).unwrap());
        assert_eq!(
            "Cannot compare 4 and 1.0 with <",
            format!("{}", Integer(4).lt(&Double(1.0)).unwrap_err())
        );

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
        assert_eq!(
            "Cannot compare 4.0 and 1 with <=",
            format!("{}", Double(4.0).le(&Integer(1)).unwrap_err())
        );

        assert_eq!(Boolean(false), Integer(2).le(&Integer(1)).unwrap());
        assert_eq!(Boolean(true), Integer(2).le(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(2).le(&Integer(3)).unwrap());
        assert_eq!(
            "Cannot compare 4 and 1.0 with <=",
            format!("{}", Integer(4).le(&Double(1.0)).unwrap_err())
        );

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
        assert_eq!(
            "Cannot compare 4.0 and 1 with >",
            format!("{}", Double(4.0).gt(&Integer(1)).unwrap_err())
        );

        assert_eq!(Boolean(false), Integer(2).gt(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(4).gt(&Integer(3)).unwrap());
        assert_eq!(
            "Cannot compare 4 and 1.0 with >",
            format!("{}", Integer(4).gt(&Double(1.0)).unwrap_err())
        );

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
        assert_eq!(
            "Cannot compare 4.0 and 1 with >=",
            format!("{}", Double(4.0).ge(&Integer(1)).unwrap_err())
        );

        assert_eq!(Boolean(false), Integer(1).ge(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(2).ge(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(4).ge(&Integer(3)).unwrap());
        assert_eq!(
            "Cannot compare 4 and 1.0 with >=",
            format!("{}", Integer(4).ge(&Double(1.0)).unwrap_err())
        );

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
        assert_eq!(
            "Cannot add 4.0 and 5",
            format!("{}", Double(4.0).add(&Integer(5)).unwrap_err())
        );

        assert_eq!(Integer(5), Integer(2).add(&Integer(3)).unwrap());
        assert_eq!(Integer(std::i32::MAX), Integer(std::i32::MAX).add(&Integer(0)).unwrap());
        assert_eq!(
            format!("Overflow adding {} and 1", std::i32::MAX),
            format!("{}", Integer(std::i32::MAX).add(&Integer(1)).unwrap_err())
        );
        assert_eq!(
            "Cannot add 4 and 5.0",
            format!("{}", Integer(4).add(&Double(5.0)).unwrap_err())
        );

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
        assert_eq!(
            "Cannot subtract 5 from 4.0",
            format!("{}", Double(4.0).sub(&Integer(5)).unwrap_err())
        );

        assert_eq!(Integer(-1), Integer(2).sub(&Integer(3)).unwrap());
        assert_eq!(Integer(std::i32::MIN), Integer(std::i32::MIN).sub(&Integer(0)).unwrap());
        assert_eq!(
            format!("Overflow subtracting 1 from {}", std::i32::MIN),
            format!("{}", Integer(std::i32::MIN).sub(&Integer(1)).unwrap_err())
        );
        assert_eq!(
            "Cannot subtract 5.0 from 4",
            format!("{}", Integer(4).sub(&Double(5.0)).unwrap_err())
        );

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
        assert_eq!(
            "Cannot multiply 4.0 by 5",
            format!("{}", Double(4.0).mul(&Integer(5)).unwrap_err())
        );

        assert_eq!(Integer(6), Integer(2).mul(&Integer(3)).unwrap());
        assert_eq!(Integer(std::i32::MAX), Integer(std::i32::MAX).mul(&Integer(1)).unwrap());
        assert_eq!(
            format!("Overflow multiplying {} by 2", std::i32::MAX),
            format!("{}", Integer(std::i32::MAX).mul(&Integer(2)).unwrap_err())
        );
        assert_eq!(
            "Cannot multiply 4 by 5.0",
            format!("{}", Integer(4).mul(&Double(5.0)).unwrap_err())
        );

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
        assert_eq!(
            "Cannot divide 4.0 by 5",
            format!("{}", Double(4.0).div(&Integer(5)).unwrap_err())
        );

        assert_eq!(Integer(2), Integer(10).div(&Integer(5)).unwrap());
        assert_eq!(Integer(6), Integer(20).div(&Integer(3)).unwrap());
        assert_eq!(Integer(std::i32::MIN), Integer(std::i32::MIN).div(&Integer(1)).unwrap());
        assert_eq!("Division by zero", format!("{}", Integer(4).div(&Integer(0)).unwrap_err()));
        assert_eq!(
            format!("Overflow dividing {} by -1", std::i32::MIN),
            format!("{}", Integer(std::i32::MIN).div(&Integer(-1)).unwrap_err())
        );
        assert_eq!(
            "Cannot divide 4 by 5.0",
            format!("{}", Integer(4).div(&Double(5.0)).unwrap_err())
        );

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
        assert_eq!(
            "Cannot modulo 4.0 by 5",
            format!("{}", Double(4.0).modulo(&Integer(5)).unwrap_err())
        );

        assert_eq!(Integer(0), Integer(10).modulo(&Integer(5)).unwrap());
        assert_eq!(Integer(2), Integer(20).modulo(&Integer(3)).unwrap());
        assert_eq!("Modulo by zero", format!("{}", Integer(4).modulo(&Integer(0)).unwrap_err()));
        assert_eq!(
            format!("Overflow modulo {} by -1", std::i32::MIN),
            format!("{}", Integer(std::i32::MIN).modulo(&Integer(-1)).unwrap_err())
        );
        assert_eq!(
            "Cannot modulo 4 by 5.0",
            format!("{}", Integer(4).modulo(&Double(5.0)).unwrap_err())
        );

        assert_eq!(
            "Cannot modulo \"\" by \"a\"",
            format!("{}", Text("".to_owned()).modulo(&Text("a".to_owned())).unwrap_err())
        );
    }

    #[test]
    fn test_value_neg() {
        assert_eq!("Cannot negate TRUE", format!("{}", Boolean(true).neg().unwrap_err()));

        assert_eq!(Double(-6.12), Double(6.12).neg().unwrap());
        assert_eq!(Double(5.53), Double(-5.53).neg().unwrap());

        assert_eq!(Integer(-6), Integer(6).neg().unwrap());
        assert_eq!(Integer(5), Integer(-5).neg().unwrap());
        assert_eq!(
            format!("Overflow negating {}", std::i32::MIN),
            format!("{}", Integer(std::i32::MIN).neg().unwrap_err())
        );

        assert_eq!("Cannot negate \"\"", format!("{}", Text("".to_owned()).neg().unwrap_err()));
    }
}