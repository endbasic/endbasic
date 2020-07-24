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

use crate::ast::{Expr, Value, VarType};
use crate::exec::Vars;
use failure::Fallible;

impl Value {
    /// Parses a string `s` and constructs a `Value` that matches a given `VarType`.
    pub fn parse_as<T: Into<String>>(vtype: VarType, s: T) -> Fallible<Value> {
        fn parse_i32(s: &str) -> Fallible<Value> {
            match s.parse::<i32>() {
                Ok(i) => Ok(Value::Integer(i)),
                Err(_) => bail!("Invalid integer literal {}", s),
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
                    bail!("Invalid boolean literal {}", s);
                }
            }
            VarType::Integer => parse_i32(&s),
            VarType::Text => Ok(Value::Text(s)),
        }
    }

    /// Performs a logical "and" operation.
    pub fn and(&self, other: &Self) -> Fallible<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(*lhs && *rhs)),
            (_, _) => Err(format_err!("Cannot AND {:?} and {:?}", self, other)),
        }
    }

    /// Performs a logical "or" operation.
    pub fn or(&self, other: &Self) -> Fallible<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(*lhs || *rhs)),
            (_, _) => Err(format_err!("Cannot OR {:?} and {:?}", self, other)),
        }
    }

    /// Performs a logical "xor" operation.
    pub fn xor(&self, other: &Self) -> Fallible<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(*lhs ^ *rhs)),
            (_, _) => Err(format_err!("Cannot XOR {:?} and {:?}", self, other)),
        }
    }

    /// Performs a logical "not" operation.
    pub fn not(&self) -> Fallible<Self> {
        match self {
            Value::Boolean(b) => Ok(Value::Boolean(!b)),
            _ => Err(format_err!("Cannot apply NOT to {:?}", self)),
        }
    }

    /// Performs an equality check.
    pub fn eq(&self, other: &Self) -> Fallible<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(lhs == rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs == rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs == rhs)),
            (_, _) => Err(format_err!("Cannot compare {:?} and {:?} with =", self, other)),
        }
    }

    /// Performs an inequality check.
    pub fn ne(&self, other: &Self) -> Fallible<Self> {
        match (self, other) {
            (Value::Boolean(lhs), Value::Boolean(rhs)) => Ok(Value::Boolean(lhs != rhs)),
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs != rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs != rhs)),
            (_, _) => Err(format_err!("Cannot compare {:?} and {:?} with <>", self, other)),
        }
    }

    /// Performs a less-than check.
    pub fn lt(&self, other: &Self) -> Fallible<Self> {
        match (self, other) {
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs < rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs < rhs)),
            (_, _) => Err(format_err!("Cannot compare {:?} and {:?} with <", self, other)),
        }
    }

    /// Performs a less-than or equal-to check.
    pub fn le(&self, other: &Self) -> Fallible<Self> {
        match (self, other) {
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs <= rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs <= rhs)),
            (_, _) => Err(format_err!("Cannot compare {:?} and {:?} with <=", self, other)),
        }
    }

    /// Performs a greater-than check.
    pub fn gt(&self, other: &Self) -> Fallible<Self> {
        match (self, other) {
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs > rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs > rhs)),
            (_, _) => Err(format_err!("Cannot compare {:?} and {:?} with >", self, other)),
        }
    }

    /// Performs a greater-than or equal to check.
    pub fn ge(&self, other: &Self) -> Fallible<Self> {
        match (self, other) {
            (Value::Integer(lhs), Value::Integer(rhs)) => Ok(Value::Boolean(lhs >= rhs)),
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Boolean(lhs >= rhs)),
            (_, _) => Err(format_err!("Cannot compare {:?} and {:?} with >=", self, other)),
        }
    }

    /// Performs an addition operation.
    pub fn add(&self, other: &Self) -> Fallible<Self> {
        match (self, other) {
            (Value::Integer(lhs), Value::Integer(rhs)) => match lhs.checked_add(*rhs) {
                Some(i) => Ok(Value::Integer(i)),
                None => Err(format_err!("Overflow adding {} and {}", lhs, rhs)),
            },
            (Value::Text(lhs), Value::Text(rhs)) => Ok(Value::Text(lhs.to_owned() + rhs)),
            (_, _) => Err(format_err!("Cannot add {:?} and {:?}", self, other)),
        }
    }

    /// Performs a subtraction operation.
    pub fn sub(&self, other: &Self) -> Fallible<Self> {
        match (self, other) {
            (Value::Integer(lhs), Value::Integer(rhs)) => match lhs.checked_sub(*rhs) {
                Some(i) => Ok(Value::Integer(i)),
                None => Err(format_err!("Overflow subtracting {} from {}", rhs, lhs)),
            },
            (_, _) => Err(format_err!("Cannot subtract {:?} from {:?}", other, self)),
        }
    }

    /// Performs a multiplication.
    pub fn mul(&self, other: &Self) -> Fallible<Self> {
        match (self, other) {
            (Value::Integer(lhs), Value::Integer(rhs)) => match lhs.checked_mul(*rhs) {
                Some(i) => Ok(Value::Integer(i)),
                None => Err(format_err!("Overflow multiplying {} by {}", lhs, rhs)),
            },
            (_, _) => Err(format_err!("Cannot multiply {:?} by {:?}", self, other)),
        }
    }

    /// Performs an integer division.
    pub fn div(&self, other: &Self) -> Fallible<Self> {
        match (self, other) {
            (Value::Integer(_), Value::Integer(0)) => bail!("Division by zero"),
            (Value::Integer(lhs), Value::Integer(rhs)) => match lhs.checked_div(*rhs) {
                Some(i) => Ok(Value::Integer(i)),
                None => Err(format_err!("Overflow dividing {} by {}", lhs, rhs)),
            },
            (_, _) => Err(format_err!("Cannot divide {:?} by {:?}", self, other)),
        }
    }

    /// Performs a modulo operation.
    pub fn modulo(&self, other: &Self) -> Fallible<Self> {
        match (self, other) {
            (Value::Integer(_), Value::Integer(0)) => bail!("Modulo by zero"),
            (Value::Integer(lhs), Value::Integer(rhs)) => match lhs.checked_rem(*rhs) {
                Some(i) => Ok(Value::Integer(i)),
                None => Err(format_err!("Overflow modulo {} by {}", lhs, rhs)),
            },
            (_, _) => Err(format_err!("Cannot modulo {:?} by {:?}", self, other)),
        }
    }

    /// Performs an integer negation.
    pub fn neg(&self) -> Fallible<Self> {
        match self {
            Value::Integer(i) => match i.checked_neg() {
                Some(i) => Ok(Value::Integer(i)),
                None => Err(format_err!("Overflow negating {}", i)),
            },
            _ => Err(format_err!("Cannot negate {:?}", self)),
        }
    }
}

impl ToString for Value {
    fn to_string(&self) -> String {
        match self {
            Value::Boolean(true) => "TRUE".to_owned(),
            Value::Boolean(false) => "FALSE".to_owned(),
            Value::Integer(i) => format!("{}", i),
            Value::Text(s2) => s2.clone(),
        }
    }
}

impl Expr {
    /// Evaluates the expression to a value.
    ///
    /// Variable references are resolved by querying `vars`.  Errors in the computation are returned
    /// via the special `Value::Bad` type.
    pub fn eval(&self, vars: &Vars) -> Fallible<Value> {
        match self {
            Expr::Boolean(b) => Ok(Value::Boolean(*b)),
            Expr::Integer(i) => Ok(Value::Integer(*i)),
            Expr::Text(s) => Ok(Value::Text(s.clone())),

            Expr::Symbol(vref) => Ok(vars.get(vref)?.clone()),

            Expr::And(lhs, rhs) => Value::and(&lhs.eval(vars)?, &rhs.eval(vars)?),
            Expr::Or(lhs, rhs) => Value::or(&lhs.eval(vars)?, &rhs.eval(vars)?),
            Expr::Xor(lhs, rhs) => Value::xor(&lhs.eval(vars)?, &rhs.eval(vars)?),
            Expr::Not(v) => Value::not(&v.eval(vars)?),

            Expr::Equal(lhs, rhs) => Value::eq(&lhs.eval(vars)?, &rhs.eval(vars)?),
            Expr::NotEqual(lhs, rhs) => Value::ne(&lhs.eval(vars)?, &rhs.eval(vars)?),
            Expr::Less(lhs, rhs) => Value::lt(&lhs.eval(vars)?, &rhs.eval(vars)?),
            Expr::LessEqual(lhs, rhs) => Value::le(&lhs.eval(vars)?, &rhs.eval(vars)?),
            Expr::Greater(lhs, rhs) => Value::gt(&lhs.eval(vars)?, &rhs.eval(vars)?),
            Expr::GreaterEqual(lhs, rhs) => Value::ge(&lhs.eval(vars)?, &rhs.eval(vars)?),

            Expr::Add(lhs, rhs) => Value::add(&lhs.eval(vars)?, &rhs.eval(vars)?),
            Expr::Subtract(lhs, rhs) => Value::sub(&lhs.eval(vars)?, &rhs.eval(vars)?),
            Expr::Multiply(lhs, rhs) => Value::mul(&lhs.eval(vars)?, &rhs.eval(vars)?),
            Expr::Divide(lhs, rhs) => Value::div(&lhs.eval(vars)?, &rhs.eval(vars)?),
            Expr::Modulo(lhs, rhs) => Value::modulo(&lhs.eval(vars)?, &rhs.eval(vars)?),
            Expr::Negate(e) => Value::neg(&e.eval(vars)?),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::VarRef;

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
        assert_eq!("-56", &Integer(-56).to_string());
        assert_eq!("some words", &Text("some words".to_owned()).to_string());
    }

    #[test]
    fn test_value_to_string_and_parse() {
        use super::Value::*;

        let v = Boolean(false);
        assert_eq!(v, Value::parse_as(VarType::Boolean, &v.to_string()).unwrap());

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

        assert_eq!(Boolean(true), Integer(2).eq(&Integer(2)).unwrap());
        assert_eq!(Boolean(false), Integer(3).eq(&Integer(4)).unwrap());
        assert_eq!(
            "Cannot compare Integer(4) and Text(\"5\") with =",
            format!("{}", Integer(4).eq(&Text("5".to_owned())).unwrap_err())
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

        assert_eq!(Boolean(false), Integer(2).ne(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(3).ne(&Integer(4)).unwrap());
        assert_eq!(
            "Cannot compare Integer(4) and Text(\"5\") with <>",
            format!("{}", Integer(4).ne(&Text("5".to_owned())).unwrap_err())
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

        assert_eq!(Boolean(false), Integer(2).lt(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(3).lt(&Integer(4)).unwrap());
        assert_eq!(
            "Cannot compare Integer(4) and Text(\"5\") with <",
            format!("{}", Integer(4).lt(&Text("5".to_owned())).unwrap_err())
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

        assert_eq!(Boolean(false), Integer(2).le(&Integer(1)).unwrap());
        assert_eq!(Boolean(true), Integer(2).le(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(2).le(&Integer(3)).unwrap());
        assert_eq!(
            "Cannot compare Integer(4) and Text(\"5\") with <=",
            format!("{}", Integer(4).le(&Text("5".to_owned())).unwrap_err())
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

        assert_eq!(Boolean(false), Integer(2).gt(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(4).gt(&Integer(3)).unwrap());
        assert_eq!(
            "Cannot compare Integer(4) and Text(\"5\") with >",
            format!("{}", Integer(4).gt(&Text("5".to_owned())).unwrap_err())
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

        assert_eq!(Boolean(false), Integer(1).ge(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(2).ge(&Integer(2)).unwrap());
        assert_eq!(Boolean(true), Integer(4).ge(&Integer(3)).unwrap());
        assert_eq!(
            "Cannot compare Integer(4) and Text(\"5\") with >=",
            format!("{}", Integer(4).ge(&Text("5".to_owned())).unwrap_err())
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

        assert_eq!(Integer(5), Integer(2).add(&Integer(3)).unwrap());
        assert_eq!(Integer(i32::MAX), Integer(i32::MAX).add(&Integer(0)).unwrap());
        assert_eq!(
            format!("Overflow adding {} and 1", i32::MAX),
            format!("{}", Integer(i32::MAX).add(&Integer(1)).unwrap_err())
        );
        assert_eq!(
            "Cannot add Integer(4) and Text(\"5\")",
            format!("{}", Integer(4).add(&Text("5".to_owned())).unwrap_err())
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

        assert_eq!(Integer(-1), Integer(2).sub(&Integer(3)).unwrap());
        assert_eq!(Integer(i32::MIN), Integer(i32::MIN).sub(&Integer(0)).unwrap());
        assert_eq!(
            format!("Overflow subtracting 1 from {}", i32::MIN),
            format!("{}", Integer(i32::MIN).sub(&Integer(1)).unwrap_err())
        );
        assert_eq!(
            "Cannot subtract Text(\"5\") from Integer(4)",
            format!("{}", Integer(4).sub(&Text("5".to_owned())).unwrap_err())
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

        assert_eq!(Integer(6), Integer(2).mul(&Integer(3)).unwrap());
        assert_eq!(Integer(i32::MAX), Integer(i32::MAX).mul(&Integer(1)).unwrap());
        assert_eq!(
            format!("Overflow multiplying {} by 2", i32::MAX),
            format!("{}", Integer(i32::MAX).mul(&Integer(2)).unwrap_err())
        );
        assert_eq!(
            "Cannot multiply Integer(4) by Text(\"5\")",
            format!("{}", Integer(4).mul(&Text("5".to_owned())).unwrap_err())
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

        assert_eq!(Integer(2), Integer(10).div(&Integer(5)).unwrap());
        assert_eq!(Integer(6), Integer(20).div(&Integer(3)).unwrap());
        assert_eq!(Integer(i32::MIN), Integer(i32::MIN).div(&Integer(1)).unwrap());
        assert_eq!("Division by zero", format!("{}", Integer(4).div(&Integer(0)).unwrap_err()));
        assert_eq!(
            format!("Overflow dividing {} by -1", i32::MIN),
            format!("{}", Integer(i32::MIN).div(&Integer(-1)).unwrap_err())
        );
        assert_eq!(
            "Cannot divide Integer(4) by Text(\"5\")",
            format!("{}", Integer(4).div(&Text("5".to_owned())).unwrap_err())
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

        assert_eq!(Integer(0), Integer(10).modulo(&Integer(5)).unwrap());
        assert_eq!(Integer(2), Integer(20).modulo(&Integer(3)).unwrap());
        assert_eq!("Modulo by zero", format!("{}", Integer(4).modulo(&Integer(0)).unwrap_err()));
        assert_eq!(
            format!("Overflow modulo {} by -1", i32::MIN),
            format!("{}", Integer(i32::MIN).modulo(&Integer(-1)).unwrap_err())
        );
        assert_eq!(
            "Cannot modulo Integer(4) by Text(\"5\")",
            format!("{}", Integer(4).modulo(&Text("5".to_owned())).unwrap_err())
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
    fn test_varref_display() {
        assert_eq!("name", format!("{}", VarRef::new("name", VarType::Auto)));
        assert_eq!("abc?", format!("{}", VarRef::new("abc", VarType::Boolean)));
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
        let bool_val = Value::Boolean(true);
        let int_val = Value::Integer(0);
        let text_val = Value::Text("x".to_owned());

        assert!(VarRef::new("a", VarType::Auto).accepts(&bool_val));
        assert!(VarRef::new("a", VarType::Auto).accepts(&int_val));
        assert!(VarRef::new("a", VarType::Auto).accepts(&text_val));

        assert!(VarRef::new("a", VarType::Boolean).accepts(&bool_val));
        assert!(!VarRef::new("a", VarType::Boolean).accepts(&int_val));
        assert!(!VarRef::new("a", VarType::Boolean).accepts(&text_val));

        assert!(!VarRef::new("a", VarType::Integer).accepts(&bool_val));
        assert!(VarRef::new("a", VarType::Integer).accepts(&int_val));
        assert!(!VarRef::new("a", VarType::Integer).accepts(&text_val));

        assert!(!VarRef::new("a", VarType::Text).accepts(&bool_val));
        assert!(!VarRef::new("a", VarType::Text).accepts(&int_val));
        assert!(VarRef::new("a", VarType::Text).accepts(&text_val));
    }

    #[test]
    fn test_expr_literals() {
        let vars = Vars::default();
        assert_eq!(Value::Boolean(true), Expr::Boolean(true).eval(&vars).unwrap());
        assert_eq!(Value::Integer(0), Expr::Integer(0).eval(&vars).unwrap());
        assert_eq!(Value::Text("z".to_owned()), Expr::Text("z".to_owned()).eval(&vars).unwrap());
    }

    #[test]
    fn test_expr_symbol() {
        let bool_ref = VarRef::new("a_boolean", VarType::Auto);
        let bool_val = Value::Boolean(true);
        let int_ref = VarRef::new("an_integer", VarType::Auto);
        let int_val = Value::Integer(0);
        let text_ref = VarRef::new("a_string", VarType::Auto);
        let text_val = Value::Text("x".to_owned());

        let mut vars = Vars::default();
        vars.set(&bool_ref, bool_val.clone()).unwrap();
        vars.set(&int_ref, int_val.clone()).unwrap();
        vars.set(&text_ref, text_val.clone()).unwrap();

        assert_eq!(bool_val, Expr::Symbol(bool_ref).eval(&vars).unwrap());
        assert_eq!(int_val, Expr::Symbol(int_ref).eval(&vars).unwrap());
        assert_eq!(text_val, Expr::Symbol(text_ref).eval(&vars).unwrap());

        assert_eq!(
            "Undefined variable x",
            format!("{}", Expr::Symbol(VarRef::new("x", VarType::Auto)).eval(&vars).unwrap_err())
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
        let vars = Vars::default();
        assert_eq!(
            "Cannot AND Boolean(false) and Integer(0)",
            format!("{}", Expr::And(a_bool.clone(), an_int.clone()).eval(&vars).unwrap_err())
        );
        assert_eq!(
            "Cannot OR Boolean(false) and Integer(0)",
            format!("{}", Expr::Or(a_bool.clone(), an_int.clone()).eval(&vars).unwrap_err())
        );
        assert_eq!(
            "Cannot XOR Boolean(false) and Integer(0)",
            format!("{}", Expr::Xor(a_bool, an_int.clone()).eval(&vars).unwrap_err())
        );
        assert_eq!(
            "Cannot apply NOT to Integer(0)",
            format!("{}", Expr::Not(an_int).eval(&vars).unwrap_err())
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
        let vars = Vars::default();
        assert_eq!(
            "Cannot compare Boolean(false) and Integer(0) with =",
            format!("{}", Expr::Equal(a_bool.clone(), an_int.clone()).eval(&vars).unwrap_err())
        );
        assert_eq!(
            "Cannot compare Boolean(false) and Integer(0) with <>",
            format!("{}", Expr::NotEqual(a_bool.clone(), an_int.clone()).eval(&vars).unwrap_err())
        );
        assert_eq!(
            "Cannot compare Boolean(false) and Integer(0) with <",
            format!("{}", Expr::Less(a_bool.clone(), an_int.clone()).eval(&vars).unwrap_err())
        );
        assert_eq!(
            "Cannot compare Boolean(false) and Integer(0) with <=",
            format!("{}", Expr::LessEqual(a_bool.clone(), an_int.clone()).eval(&vars).unwrap_err())
        );
        assert_eq!(
            "Cannot compare Boolean(false) and Integer(0) with >",
            format!("{}", Expr::Greater(a_bool.clone(), an_int.clone()).eval(&vars).unwrap_err())
        );
        assert_eq!(
            "Cannot compare Boolean(false) and Integer(0) with >=",
            format!("{}", Expr::GreaterEqual(a_bool, an_int).eval(&vars).unwrap_err())
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
        let vars = Vars::default();
        assert_eq!(
            "Cannot add Boolean(false) and Integer(0)",
            format!("{}", Expr::Add(a_bool.clone(), an_int.clone()).eval(&vars).unwrap_err())
        );
        assert_eq!(
            "Cannot subtract Integer(0) from Boolean(false)",
            format!("{}", Expr::Subtract(a_bool.clone(), an_int.clone()).eval(&vars).unwrap_err())
        );
        assert_eq!(
            "Cannot multiply Boolean(false) by Integer(0)",
            format!("{}", Expr::Multiply(a_bool.clone(), an_int.clone()).eval(&vars).unwrap_err())
        );
        assert_eq!(
            "Cannot divide Boolean(false) by Integer(0)",
            format!("{}", Expr::Divide(a_bool.clone(), an_int).eval(&vars).unwrap_err())
        );
        assert_eq!(
            "Cannot negate Boolean(false)",
            format!("{}", Expr::Negate(a_bool).eval(&vars).unwrap_err())
        );
    }

    #[test]
    fn test_expr_various_ops_and_vars() {
        let xref = VarRef::new("x", VarType::Integer);
        let yref = VarRef::new("y", VarType::Integer);

        let mut vars = Vars::default();
        vars.set(&xref, Value::Integer(10)).unwrap();
        vars.set(&yref, Value::Integer(3)).unwrap();

        assert_eq!(
            Value::Integer(36),
            Expr::Multiply(
                Box::from(Expr::Add(
                    Box::from(Expr::Symbol(xref.clone())),
                    Box::from(Expr::Integer(2))
                )),
                Box::from(Expr::Symbol(yref.clone()))
            )
            .eval(&vars)
            .unwrap()
        );

        assert_eq!(
            Value::Boolean(true),
            Expr::Equal(
                Box::from(Expr::Symbol(xref)),
                Box::from(Expr::Add(Box::from(Expr::Integer(7)), Box::from(Expr::Symbol(yref))))
            )
            .eval(&vars)
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
                .eval(&vars)
                .unwrap_err()
            )
        );
    }
}
