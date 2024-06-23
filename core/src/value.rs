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
    /// Parses a string `s` and constructs a `Value` that matches a given `ExprType`.
    pub fn parse_as<T: Into<String>>(vtype: ExprType, s: T) -> Result<Value> {
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
            ExprType::Boolean => {
                let raw = s.to_uppercase();
                if raw == "TRUE" || raw == "YES" || raw == "Y" {
                    Ok(Value::Boolean(true))
                } else if raw == "FALSE" || raw == "NO" || raw == "N" {
                    Ok(Value::Boolean(false))
                } else {
                    Err(Error::new(format!("Invalid boolean literal {}", s)))
                }
            }
            ExprType::Double => parse_f64(&s),
            ExprType::Integer => parse_i32(&s),
            ExprType::Text => Ok(Value::Text(s)),
        }
    }

    /// Given a `target` variable type, tries to convert the value to that type if they are
    /// compatible or otherwise returns self.
    ///
    /// Can return an error when the conversion is feasible but it is not possible, such as trying
    /// to cast a NaN to an integer.
    pub(crate) fn maybe_cast(self, target: Option<ExprType>) -> Result<Value> {
        match (target, self) {
            (Some(ExprType::Integer), Value::Double(d)) => {
                Ok(Value::Integer(double_to_integer(d)?))
            }
            (Some(ExprType::Double), Value::Integer(i)) => Ok(Value::Double(integer_to_double(i))),
            (_, v) => Ok(v),
        }
    }
}

/// Converts the double `d` to an integer and fails if the conversion is not possible.
pub fn double_to_integer(d: f64) -> Result<i32> {
    let d = d.round();
    if d.is_finite() && d >= (i32::MIN as f64) && (d <= i32::MAX as f64) {
        Ok(d as i32)
    } else {
        Err(Error::new(format!("Cannot cast {} to integer due to overflow", d)))
    }
}

/// Converts the integer `i` to a double.
pub(crate) fn integer_to_double(i: i32) -> f64 {
    i as f64
}

/// Performs a left shift.
pub(crate) fn bitwise_shl(lhs: i32, rhs: i32) -> Result<i32> {
    let bits = match u32::try_from(rhs) {
        Ok(n) => n,
        Err(_) => {
            return Err(Error::new(format!("Number of bits to << ({}) must be positive", rhs)))
        }
    };

    match lhs.checked_shl(bits) {
        Some(i) => Ok(i),
        None => Ok(0),
    }
}

/// Performs a right shift.
pub(crate) fn bitwise_shr(lhs: i32, rhs: i32) -> Result<i32> {
    let bits = match u32::try_from(rhs) {
        Ok(n) => n,
        Err(_) => {
            return Err(Error::new(format!("Number of bits to >> ({}) must be positive", rhs)))
        }
    };

    match lhs.checked_shr(bits) {
        Some(i) => Ok(i),
        None if lhs < 0 => Ok(-1),
        None => Ok(0),
    }
}

/// Performs an arithmetic addition of integers.
pub fn add_integer(lhs: i32, rhs: i32) -> Result<i32> {
    match lhs.checked_add(rhs) {
        Some(i) => Ok(i),
        None => Err(Error::new("Integer overflow".to_owned())),
    }
}

/// Performs an arithmetic subtraction of integers.
pub fn sub_integer(lhs: i32, rhs: i32) -> Result<i32> {
    match lhs.checked_sub(rhs) {
        Some(i) => Ok(i),
        None => Err(Error::new("Integer underflow".to_owned())),
    }
}

/// Performs a multiplication of integers.
pub fn mul_integer(lhs: i32, rhs: i32) -> Result<i32> {
    match lhs.checked_mul(rhs) {
        Some(i) => Ok(i),
        None => Err(Error::new("Integer overflow".to_owned())),
    }
}

/// Performs an arithmetic division of integers.
pub fn div_integer(lhs: i32, rhs: i32) -> Result<i32> {
    if rhs == 0 {
        return Err(Error::new("Division by zero"));
    }
    match lhs.checked_div(rhs) {
        Some(i) => Ok(i),
        None => Err(Error::new("Integer underflow".to_owned())),
    }
}

/// Performs a modulo operation of integers.
pub fn modulo_integer(lhs: i32, rhs: i32) -> Result<i32> {
    if rhs == 0 {
        return Err(Error::new("Modulo by zero"));
    }
    match lhs.checked_rem(rhs) {
        Some(i) => Ok(i),
        None => Err(Error::new("Integer underflow".to_owned())),
    }
}

/// Performs a power operation of integers.
pub fn pow_integer(lhs: i32, rhs: i32) -> Result<i32> {
    let exp = match u32::try_from(rhs) {
        Ok(exp) => exp,
        Err(_) => {
            return Err(Error::new(format!("Exponent {} cannot be negative", rhs)));
        }
    };
    match lhs.checked_pow(exp) {
        Some(i) => Ok(i),
        None => Err(Error::new("Integer overflow".to_owned())),
    }
}

/// Performs an arithmetic negation of an integer.
pub fn neg_integer(i: i32) -> Result<i32> {
    match i.checked_neg() {
        Some(i) => Ok(i),
        None => Err(Error::new("Integer underflow".to_owned())),
    }
}

#[cfg(test)]
mod tests {
    use super::Value::*;
    use super::*;

    #[test]
    fn test_value_parse_as_boolean() {
        for s in &["true", "TrUe", "TRUE", "yes", "Yes", "y", "Y"] {
            assert_eq!(Boolean(true), Value::parse_as(ExprType::Boolean, *s).unwrap());
        }

        for s in &["false", "FaLsE", "FALSE", "no", "No", "n", "N"] {
            assert_eq!(Boolean(false), Value::parse_as(ExprType::Boolean, *s).unwrap());
        }

        for s in &["ye", "0", "1", " true"] {
            assert_eq!(
                format!("Invalid boolean literal {}", s),
                format!("{}", Value::parse_as(ExprType::Boolean, *s).unwrap_err())
            );
        }
    }

    #[test]
    fn test_value_parse_as_double() {
        assert_eq!(Double(10.0), Value::parse_as(ExprType::Double, "10").unwrap());
        assert_eq!(Double(0.0), Value::parse_as(ExprType::Double, "0").unwrap());
        assert_eq!(Double(-21.0), Value::parse_as(ExprType::Double, "-21").unwrap());
        assert_eq!(Double(1.0), Value::parse_as(ExprType::Double, "1.0").unwrap());
        assert_eq!(Double(0.01), Value::parse_as(ExprType::Double, ".01").unwrap());

        assert_eq!(
            Double(123456789012345680000000000000.0),
            Value::parse_as(ExprType::Double, "123456789012345678901234567890.1").unwrap()
        );

        assert_eq!(
            Double(1.1234567890123457),
            Value::parse_as(ExprType::Double, "1.123456789012345678901234567890").unwrap()
        );

        assert_eq!(
            "Invalid double-precision floating point literal ",
            format!("{}", Value::parse_as(ExprType::Double, "").unwrap_err())
        );
        assert_eq!(
            "Invalid double-precision floating point literal - 3.0",
            format!("{}", Value::parse_as(ExprType::Double, "- 3.0").unwrap_err())
        );
        assert_eq!(
            "Invalid double-precision floating point literal 34ab3.1",
            format!("{}", Value::parse_as(ExprType::Double, "34ab3.1").unwrap_err())
        );
    }

    #[test]
    fn test_value_parse_as_integer() {
        assert_eq!(Integer(10), Value::parse_as(ExprType::Integer, "10").unwrap());
        assert_eq!(Integer(0), Value::parse_as(ExprType::Integer, "0").unwrap());
        assert_eq!(Integer(-21), Value::parse_as(ExprType::Integer, "-21").unwrap());

        assert_eq!(
            "Invalid integer literal ",
            format!("{}", Value::parse_as(ExprType::Integer, "").unwrap_err())
        );
        assert_eq!(
            "Invalid integer literal - 3",
            format!("{}", Value::parse_as(ExprType::Integer, "- 3").unwrap_err())
        );
        assert_eq!(
            "Invalid integer literal 34ab3",
            format!("{}", Value::parse_as(ExprType::Integer, "34ab3").unwrap_err())
        );
    }

    #[test]
    fn test_value_parse_as_text() {
        assert_eq!(Text("".to_owned()), Value::parse_as(ExprType::Text, "").unwrap());
        assert_eq!(Text("true".to_owned()), Value::parse_as(ExprType::Text, "true").unwrap());
        assert_eq!(Text("32".to_owned()), Value::parse_as(ExprType::Text, "32").unwrap());
        assert_eq!(Text("a b".to_owned()), Value::parse_as(ExprType::Text, "a b").unwrap());
    }

    #[test]
    fn test_double_to_integer() {
        assert_eq!(8, double_to_integer(8.4).unwrap());
        assert_eq!(9, double_to_integer(8.5).unwrap());
        assert_eq!(9, double_to_integer(8.6).unwrap());

        double_to_integer(f64::NAN).unwrap_err();
        double_to_integer(i32::MAX as f64 + 1.0).unwrap_err();
        double_to_integer(i32::MIN as f64 - 1.0).unwrap_err();
    }

    #[test]
    fn test_integer_to_double() {
        assert_eq!(7.0, integer_to_double(7));
    }

    #[test]
    fn test_value_maybe_cast() {
        use std::i32;

        let all_types = [ExprType::Boolean, ExprType::Double, ExprType::Integer, ExprType::Text];
        for target in all_types {
            assert_eq!(Boolean(true), Boolean(true).maybe_cast(Some(target)).unwrap());
            if target != ExprType::Integer {
                assert_eq!(Double(3.8), Double(3.8).maybe_cast(Some(target)).unwrap());
                match Double(f64::NAN).maybe_cast(Some(target)).unwrap() {
                    Double(d) => assert!(d.is_nan()),
                    _ => panic!(),
                }
            }
            if target != ExprType::Double {
                assert_eq!(Integer(3), Integer(3).maybe_cast(Some(target)).unwrap());
            }
            assert_eq!(
                Text("a".to_owned()),
                Text("a".to_owned()).maybe_cast(Some(target)).unwrap()
            );
        }

        assert_eq!(Integer(8), Double(8.4).maybe_cast(Some(ExprType::Integer)).unwrap());
        assert_eq!(Integer(9), Double(8.5).maybe_cast(Some(ExprType::Integer)).unwrap());
        assert_eq!(Integer(9), Double(8.6).maybe_cast(Some(ExprType::Integer)).unwrap());
        assert_eq!(Double(7.0), Integer(7).maybe_cast(Some(ExprType::Double)).unwrap());

        Double(f64::NAN).maybe_cast(Some(ExprType::Integer)).unwrap_err();
        assert_eq!(
            Double(i32::MAX as f64),
            Integer(i32::MAX).maybe_cast(Some(ExprType::Double)).unwrap()
        );
        Double(i32::MAX as f64 + 1.0).maybe_cast(Some(ExprType::Integer)).unwrap_err();
        assert_eq!(
            Double(i32::MIN as f64),
            Integer(i32::MIN).maybe_cast(Some(ExprType::Double)).unwrap()
        );
        Double(i32::MIN as f64 - 1.0).maybe_cast(Some(ExprType::Integer)).unwrap_err();
    }

    #[test]
    fn test_value_display_and_parse() {
        let v = Boolean(false);
        assert_eq!(v, Value::parse_as(ExprType::Boolean, format!("{}", v)).unwrap());

        let v = Double(10.1);
        assert_eq!(v, Value::parse_as(ExprType::Double, format!("{}", v)).unwrap());

        let v = Integer(9);
        assert_eq!(v, Value::parse_as(ExprType::Integer, format!("{}", v)).unwrap());

        // The string parsing and printing is not symmetrical on purpose given that user input
        // does not provide strings as quoted but we want to show them as quoted for clarity.
        let v = Text("Some long text".to_owned());
        assert_eq!(
            Text("\"Some long text\"".to_owned()),
            Value::parse_as(ExprType::Text, format!("{}", v)).unwrap()
        );
    }

    #[test]
    fn test_value_shl() {
        assert_eq!(12, bitwise_shl(3, 2).unwrap());
        assert_eq!(0xf0000000u32 as i32, bitwise_shl(0xf0000000u32 as i32, 0).unwrap());
        assert_eq!(0x80000000u32 as i32, bitwise_shl(1, 31).unwrap());
        assert_eq!(0, bitwise_shl(0xf0000000u32 as i32, 31).unwrap());

        assert_eq!(0xe0000000u32 as i32, bitwise_shl(0xf0000000u32 as i32, 1).unwrap());
        assert_eq!(0, bitwise_shl(0x80000000u32 as i32, 1).unwrap());
        assert_eq!(0, bitwise_shl(1, 32).unwrap());
        assert_eq!(0, bitwise_shl(1, 64).unwrap());

        assert_eq!(
            "Number of bits to << (-1) must be positive",
            format!("{}", bitwise_shl(3, -1).unwrap_err())
        );
    }

    #[test]
    fn test_value_shr() {
        assert_eq!(3, bitwise_shr(12, 2).unwrap());
        assert_eq!(0xf0000000u32 as i32, bitwise_shr(0xf0000000u32 as i32, 0).unwrap());
        assert_eq!(-1, bitwise_shr(0xf0000000u32 as i32, 31).unwrap());
        assert_eq!(1, bitwise_shr(0x70000000u32 as i32, 30).unwrap());
        assert_eq!(-2, bitwise_shr(-8, 2).unwrap());

        assert_eq!(0xf0000000u32 as i32, bitwise_shr(0xe0000000u32 as i32, 1).unwrap());
        assert_eq!(0xc0000000u32 as i32, bitwise_shr(0x80000000u32 as i32, 1).unwrap());
        assert_eq!(0x38000000, bitwise_shr(0x70000000, 1).unwrap());
        assert_eq!(0, bitwise_shr(0x70000000u32 as i32, 32).unwrap());
        assert_eq!(0, bitwise_shr(0x70000000u32 as i32, 32).unwrap());
        assert_eq!(-1, bitwise_shr(0x80000000u32 as i32, 32).unwrap());
        assert_eq!(-1, bitwise_shr(0x80000000u32 as i32, 64).unwrap());

        assert_eq!(
            "Number of bits to >> (-1) must be positive",
            format!("{}", bitwise_shr(3, -1).unwrap_err())
        );
    }

    #[test]
    fn test_value_add_integer() {
        assert_eq!(5, add_integer(2, 3).unwrap());
        assert_eq!(std::i32::MAX, add_integer(std::i32::MAX, 0).unwrap());
        assert_eq!("Integer overflow", format!("{}", add_integer(std::i32::MAX, 1).unwrap_err()));
    }

    #[test]
    fn test_value_sub_integer() {
        assert_eq!(-1, sub_integer(2, 3).unwrap());
        assert_eq!(std::i32::MIN, sub_integer(std::i32::MIN, 0).unwrap());
        assert_eq!("Integer underflow", format!("{}", sub_integer(std::i32::MIN, 1).unwrap_err()));
    }

    #[test]
    fn test_value_mul_integer() {
        assert_eq!(6, mul_integer(2, 3).unwrap());
        assert_eq!(std::i32::MAX, mul_integer(std::i32::MAX, 1).unwrap());
        assert_eq!("Integer overflow", format!("{}", mul_integer(std::i32::MAX, 2).unwrap_err()));
    }

    #[test]
    fn test_value_div_integer() {
        assert_eq!(2, div_integer(10, 5).unwrap());
        assert_eq!(6, div_integer(20, 3).unwrap());
        assert_eq!(std::i32::MIN, div_integer(std::i32::MIN, 1).unwrap());
        assert_eq!("Division by zero", format!("{}", div_integer(4, 0).unwrap_err()));
        assert_eq!("Integer underflow", format!("{}", div_integer(std::i32::MIN, -1).unwrap_err()));
    }

    #[test]
    fn test_value_modulo_integer() {
        assert_eq!(0, modulo_integer(10, 5).unwrap());
        assert_eq!(2, modulo_integer(20, 3).unwrap());
        assert_eq!("Modulo by zero", format!("{}", modulo_integer(4, 0).unwrap_err()));
        assert_eq!(
            "Integer underflow",
            format!("{}", modulo_integer(std::i32::MIN, -1).unwrap_err())
        );
    }

    #[test]
    fn test_value_pow_integer() {
        assert_eq!(1, pow_integer(0, 0).unwrap());
        assert_eq!(9, pow_integer(3, 2).unwrap());
        assert_eq!(std::i32::MAX, pow_integer(std::i32::MAX, 1).unwrap());
        assert_eq!("Integer overflow", format!("{}", pow_integer(std::i32::MAX, 2).unwrap_err()));
        assert_eq!(
            "Exponent -3 cannot be negative",
            format!("{}", pow_integer(1, -3).unwrap_err())
        );
    }

    #[test]
    fn test_value_neg_integer() {
        assert_eq!(-6, neg_integer(6).unwrap());
        assert_eq!(5, neg_integer(-5).unwrap());
    }
}
