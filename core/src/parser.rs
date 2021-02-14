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

//! Statement and expression parser for the EndBASIC language.

use crate::ast::{ArgSep, Expr, Statement, VarRef, VarType};
use crate::lexer::{Lexer, PeekableLexer, Token};
use std::cmp::Ordering;
use std::io;

/// Parser errors.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Bad syntax in the input program.
    #[error("{0}")]
    Bad(String),

    /// I/O error while parsing the input program.
    #[error("read error")]
    Io(#[from] io::Error),
}

/// Result for parser return values.
pub type Result<T> = std::result::Result<T, Error>;

/// Operators that can appear within an expression.
///
/// The main difference between this and `lexer::Token` is that, in here, we differentiate the
/// meaning of a minus sign and separate it in its two variants: the 2-operand `Minus` and the
/// 1-operand `Negate`.
///
/// That said, this type also is the right place to abstract away operator-related logic to
/// implement the expression parsing algorithm, so it's not completely useless.
#[derive(Debug, Eq, PartialEq)]
enum ExprOp {
    LeftParen,

    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    Negate,

    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,

    And,
    Not,
    Or,
    Xor,
}

impl ExprOp {
    /// Constructs a new operator based on a token, which must have a valid correspondence.
    fn from(t: Token) -> Self {
        match t {
            Token::Equal => ExprOp::Equal,
            Token::NotEqual => ExprOp::NotEqual,
            Token::Less => ExprOp::Less,
            Token::LessEqual => ExprOp::LessEqual,
            Token::Greater => ExprOp::Greater,
            Token::GreaterEqual => ExprOp::GreaterEqual,
            Token::Plus => ExprOp::Add,
            Token::Multiply => ExprOp::Multiply,
            Token::Divide => ExprOp::Divide,
            Token::Modulo => ExprOp::Modulo,
            Token::And => ExprOp::And,
            Token::Or => ExprOp::Or,
            Token::Xor => ExprOp::Xor,
            Token::Minus => panic!("Ambiguous token; cannot derive ExprOp"),
            _ => panic!("Called on an non-operator"),
        }
    }

    /// Returns the priority of this operator.  The specific number's meaning is only valid when
    /// comparing it against other calls to this function.  Higher number imply higher priority.
    fn priority(&self) -> i8 {
        match self {
            ExprOp::LeftParen => 5,

            ExprOp::Negate => 4,
            ExprOp::Not => 4,

            ExprOp::Multiply => 3,
            ExprOp::Divide => 3,
            ExprOp::Modulo => 3,

            ExprOp::Add => 2,
            ExprOp::Subtract => 2,

            ExprOp::Equal => 1,
            ExprOp::NotEqual => 1,
            ExprOp::Less => 1,
            ExprOp::LessEqual => 1,
            ExprOp::Greater => 1,
            ExprOp::GreaterEqual => 1,

            ExprOp::And => 0,
            ExprOp::Or => 0,
            ExprOp::Xor => 0,
        }
    }

    /// Pops operands from the `expr` stack, applies this operation, and pushes the result back.
    fn apply(&self, exprs: &mut Vec<Expr>) -> Result<()> {
        fn apply1(exprs: &mut Vec<Expr>, f: fn(Box<Expr>) -> Expr) -> Result<()> {
            if exprs.is_empty() {
                return Err(Error::Bad("Not enough values to apply operator".to_owned()));
            }
            let v1 = Box::from(exprs.pop().unwrap());
            exprs.push(f(v1));
            Ok(())
        }

        fn apply2(exprs: &mut Vec<Expr>, f: fn(Box<Expr>, Box<Expr>) -> Expr) -> Result<()> {
            if exprs.len() < 2 {
                return Err(Error::Bad("Not enough values to apply operator".to_owned()));
            }
            let v2 = Box::from(exprs.pop().unwrap());
            let v1 = Box::from(exprs.pop().unwrap());
            exprs.push(f(v1, v2));
            Ok(())
        }

        match self {
            ExprOp::Add => apply2(exprs, Expr::Add),
            ExprOp::Subtract => apply2(exprs, Expr::Subtract),
            ExprOp::Multiply => apply2(exprs, Expr::Multiply),
            ExprOp::Divide => apply2(exprs, Expr::Divide),
            ExprOp::Modulo => apply2(exprs, Expr::Modulo),
            ExprOp::Equal => apply2(exprs, Expr::Equal),
            ExprOp::NotEqual => apply2(exprs, Expr::NotEqual),
            ExprOp::Less => apply2(exprs, Expr::Less),
            ExprOp::LessEqual => apply2(exprs, Expr::LessEqual),
            ExprOp::Greater => apply2(exprs, Expr::Greater),
            ExprOp::GreaterEqual => apply2(exprs, Expr::GreaterEqual),
            ExprOp::And => apply2(exprs, Expr::And),
            ExprOp::Or => apply2(exprs, Expr::Or),
            ExprOp::Xor => apply2(exprs, Expr::Xor),

            ExprOp::Negate => apply1(exprs, Expr::Negate),
            ExprOp::Not => apply1(exprs, Expr::Not),

            ExprOp::LeftParen => Ok(()),
        }
    }
}

/// Iterator over the statements of the language.
pub struct Parser<'a> {
    lexer: PeekableLexer<'a>,
}

impl<'a> Parser<'a> {
    /// Creates a new parser from the given readable.
    pub fn from(input: &'a mut dyn io::Read) -> Self {
        Self { lexer: Lexer::from(input).peekable() }
    }

    /// Expects the peeked token to be `t` and consumes it.  Otherwise, leaves the token in the
    /// stream and fails with error `err`.
    fn expect_and_consume(&mut self, t: Token, err: &'static str) -> Result<()> {
        let peeked = self.lexer.peek()?;
        if *peeked != t {
            return Err(Error::Bad(err.to_owned()));
        }
        self.lexer.consume_peeked();
        Ok(())
    }

    /// Reads statements until one of the `delims` keywords is found.  The delimiter is not
    /// consumed.
    fn parse_until(&mut self, delims: &[Token]) -> Result<Vec<Statement>> {
        let mut stmts = vec![];
        loop {
            let peeked = self.lexer.peek()?;
            if delims.contains(peeked) {
                break;
            } else if *peeked == Token::Eol {
                self.lexer.consume_peeked();
                continue;
            }
            match self.parse()? {
                Some(stmt) => stmts.push(stmt),
                None => break,
            }
        }
        Ok(stmts)
    }

    /// Parses an assignment for the variable reference `varref` already read.
    fn parse_assignment(&mut self, vref: VarRef) -> Result<Statement> {
        let expr = match self.parse_expr(None)? {
            Some(expr) => expr,
            None => return Err(Error::Bad("Missing expression in assignment".to_owned())),
        };

        let next = self.lexer.peek()?;
        match next {
            Token::Eof | Token::Eol => (),
            _ => return Err(Error::Bad("Unexpected token in assignment".to_owned())),
        }
        Ok(Statement::Assignment(vref, expr))
    }

    /// Parses an assignment to the array `varref` with `subscripts`, both of which have already
    /// been read.
    fn parse_array_assignment(&mut self, vref: VarRef, subscripts: Vec<Expr>) -> Result<Statement> {
        let expr = match self.parse_expr(None)? {
            Some(expr) => expr,
            None => return Err(Error::Bad("Missing expression in array assignment".to_owned())),
        };

        let next = self.lexer.peek()?;
        match next {
            Token::Eof | Token::Eol => (),
            _ => return Err(Error::Bad("Unexpected token in array assignment".to_owned())),
        }
        Ok(Statement::ArrayAssignment(vref, subscripts, expr))
    }

    /// Parses a builtin call (things of the form `INPUT a`).
    fn parse_builtin_call(&mut self, vref: VarRef, mut first: Option<Expr>) -> Result<Statement> {
        let mut name = match vref.into_unannotated_string() {
            Ok(name) => name,
            Err(e) => return Err(Error::Bad(format!("{}", e))),
        };
        name.make_ascii_uppercase();

        let mut args = vec![];
        loop {
            let expr = self.parse_expr(first.take())?;

            let peeked = self.lexer.peek()?;
            match peeked {
                Token::Eof | Token::Eol => {
                    if expr.is_some() || !args.is_empty() {
                        args.push((expr, ArgSep::End));
                    }
                    break;
                }
                Token::Semicolon => {
                    self.lexer.consume_peeked();
                    args.push((expr, ArgSep::Short));
                }
                Token::Comma => {
                    self.lexer.consume_peeked();
                    args.push((expr, ArgSep::Long));
                }
                _ => {
                    return Err(Error::Bad(
                        "Expected comma, semicolon, or end of statement".to_owned(),
                    ))
                }
            }
        }
        Ok(Statement::BuiltinCall(name, args))
    }

    /// Starts processing either an array reference or a builtin call and disambiguates between the
    /// two.
    fn parse_array_or_builtin_call(&mut self, vref: VarRef) -> Result<Statement> {
        match self.lexer.peek()? {
            Token::LeftParen => {
                self.lexer.consume_peeked();
                let mut exprs = self.parse_comma_separated_exprs()?;
                match self.lexer.peek()? {
                    Token::Equal => {
                        self.lexer.consume_peeked();
                        self.parse_array_assignment(vref, exprs)
                    }
                    _ => {
                        if exprs.len() != 1 {
                            return Err(Error::Bad("Expected expression".to_owned()));
                        }
                        self.parse_builtin_call(vref, Some(exprs.remove(0)))
                    }
                }
            }
            _ => self.parse_builtin_call(vref, None),
        }
    }

    /// Parses the `AS typename` clause of a `DIM` statement.  The caller has already consumed the
    /// `AS` token.
    fn parse_dim_as(&mut self) -> Result<VarType> {
        let peeked = self.lexer.peek()?;
        let vartype = match peeked {
            Token::Eof | Token::Eol => VarType::Integer,
            Token::As => {
                self.lexer.consume_peeked();
                match self.lexer.read()? {
                    Token::BooleanName => VarType::Boolean,
                    Token::DoubleName => VarType::Double,
                    Token::IntegerName => VarType::Integer,
                    Token::TextName => VarType::Text,
                    t => {
                        return Err(Error::Bad(format!(
                            "Invalid type name {:?} in DIM AS statement",
                            t
                        )))
                    }
                }
            }
            _ => return Err(Error::Bad("Expected AS or end of statement".to_owned())),
        };

        let next = self.lexer.peek()?;
        match next {
            Token::Eof | Token::Eol => (),
            _ => return Err(Error::Bad("Unexpected token in DIM statement".to_owned())),
        }

        Ok(vartype)
    }

    /// Parses a `DIM` statement.
    fn parse_dim(&mut self) -> Result<Statement> {
        let vref = match self.lexer.read()? {
            Token::Symbol(vref) => vref,
            _ => return Err(Error::Bad("Expected variable name after DIM".to_owned())),
        };
        let name = vref.into_unannotated_string()?;

        let peeked = self.lexer.peek()?;
        match peeked {
            Token::LeftParen => {
                self.lexer.consume_peeked();
                let subscripts = self.parse_comma_separated_exprs()?;
                if subscripts.is_empty() {
                    return Err(Error::Bad("Arrays require at least one dimension".to_owned()));
                }
                let vartype = self.parse_dim_as()?;
                Ok(Statement::DimArray(name, subscripts, vartype))
            }
            _ => {
                let vartype = self.parse_dim_as()?;
                Ok(Statement::Dim(name, vartype))
            }
        }
    }

    /// Parses a variable list of comma-separated expressions.  The caller must have consumed the
    /// open parenthesis and we stop processing when we encounter the terminating parenthesis (and
    /// consume it).  We expect at least one expression.
    fn parse_comma_separated_exprs(&mut self) -> Result<Vec<Expr>> {
        let mut exprs = vec![];
        if let Some(expr) = self.parse_expr(None)? {
            // The first expression is optional to support calls to functions without arguments.
            exprs.push(expr);
        }

        loop {
            let peeked = self.lexer.peek()?;
            match peeked {
                Token::RightParen => {
                    self.lexer.consume_peeked();
                    break;
                }
                Token::Comma => {
                    self.lexer.consume_peeked();
                    if exprs.is_empty() {
                        // The first expression (parsed outside the loop) cannot be empty if we
                        // encounter more than one expression.
                        return Err(Error::Bad("Missing expression".to_owned()));
                    }
                    match self.parse_expr(None)? {
                        Some(expr) => exprs.push(expr),
                        None => return Err(Error::Bad("Missing expression".to_owned())),
                    }
                }
                _ => return Err(Error::Bad("Unexpected token".to_owned())),
            }
        }

        Ok(exprs)
    }

    /// Parses an expression.
    ///
    /// Returns `None` if no expression was found.  This is necessary to treat the case of empty
    /// arguments to statements, as is the case in `PRINT a , , b`.
    ///
    /// If the caller has already processed a parenthesized term of an expression like
    /// `(first) + second`, then that term must be provided in `first`.
    ///
    /// This is an implementation of the Shunting Yard Algorithm by Edgar Dijkstra.
    fn parse_expr(&mut self, first: Option<Expr>) -> Result<Option<Expr>> {
        let mut exprs: Vec<Expr> = vec![];
        let mut ops: Vec<ExprOp> = vec![];

        let mut need_operand = true; // Also tracks whether an upcoming minus is unary.
        if let Some(e) = first {
            exprs.push(e);
            need_operand = false;
        }

        loop {
            let mut handle_operand = |e| {
                if !need_operand {
                    return Err(Error::Bad("Unexpected value in expression".to_owned()));
                }
                need_operand = false;
                exprs.push(e);
                Ok(())
            };

            // Stop processing if we encounter an expression separator, but don't consume it because
            // the caller needs to have access to it.
            match self.lexer.peek()? {
                Token::Eof
                | Token::Eol
                | Token::Comma
                | Token::Semicolon
                | Token::Then
                | Token::To
                | Token::Step => break,
                Token::RightParen => {
                    if !ops.contains(&ExprOp::LeftParen) {
                        // We encountered an unbalanced parenthesis but we don't know if this is
                        // because we were called from within an argument list (in which case the
                        // caller consumed the opening parenthesis and is expecting to consume the
                        // closing parenthesis) or because we really found an invalid expression.
                        // Only the caller can know, so avoid consuming the token and exit.
                        break;
                    }
                }
                _ => (),
            };

            let token = self.lexer.consume_peeked();
            match token {
                Token::Boolean(b) => handle_operand(Expr::Boolean(b))?,
                Token::Double(d) => handle_operand(Expr::Double(d))?,
                Token::Integer(i) => handle_operand(Expr::Integer(i))?,
                Token::Text(t) => handle_operand(Expr::Text(t))?,
                Token::Symbol(vref) => handle_operand(Expr::Symbol(vref))?,

                Token::LeftParen => {
                    // If the last operand we encountered was a symbol, collapse it and the left
                    // parenthesis into the beginning of a function call.
                    match exprs.pop() {
                        Some(Expr::Symbol(vref)) => {
                            if !need_operand {
                                exprs.push(Expr::Call(vref, self.parse_comma_separated_exprs()?));
                                need_operand = false;
                            } else {
                                // We popped out the last expression to see if it this left
                                // parenthesis started a function call... but it did not (it is a
                                // symbol following a parenthesis) so put both the expression and
                                // the token back.
                                ops.push(ExprOp::LeftParen);
                                exprs.push(Expr::Symbol(vref));
                                need_operand = true;
                            }
                        }
                        e => {
                            if let Some(e) = e {
                                // We popped out the last expression to see if it this left
                                // parenthesis started a function call... but if it didn't, we have
                                // to put the expression back.
                                exprs.push(e);
                            }
                            if !need_operand {
                                return Err(Error::Bad(
                                    "Unexpected value in expression".to_owned(),
                                ));
                            }
                            ops.push(ExprOp::LeftParen);
                            need_operand = true;
                        }
                    };
                }
                Token::RightParen => {
                    let mut found = false;
                    while let Some(op) = ops.pop() {
                        op.apply(&mut exprs)?;
                        if op == ExprOp::LeftParen {
                            found = true;
                            break;
                        }
                    }
                    assert!(found, "Unbalanced parenthesis should have been handled above");
                    need_operand = false;
                }

                Token::Not => {
                    ops.push(ExprOp::Not);
                    need_operand = true;
                }
                Token::Minus => {
                    let op;
                    if need_operand {
                        op = ExprOp::Negate;
                    } else {
                        op = ExprOp::Subtract;
                        while let Some(op2) = ops.last() {
                            if *op2 == ExprOp::LeftParen || op2.priority() < op.priority() {
                                break;
                            }
                            let op2 = ops.pop().unwrap();
                            op2.apply(&mut exprs)?;
                        }
                    }
                    ops.push(op);
                    need_operand = true;
                }

                Token::Equal
                | Token::NotEqual
                | Token::Less
                | Token::LessEqual
                | Token::Greater
                | Token::GreaterEqual
                | Token::Plus
                | Token::Multiply
                | Token::Divide
                | Token::Modulo
                | Token::And
                | Token::Or
                | Token::Xor => {
                    let op = ExprOp::from(token);
                    while let Some(op2) = ops.last() {
                        if *op2 == ExprOp::LeftParen || op2.priority() < op.priority() {
                            break;
                        }
                        let op2 = ops.pop().unwrap();
                        op2.apply(&mut exprs)?;
                    }
                    ops.push(op);
                    need_operand = true;
                }

                Token::Bad(e) => return Err(Error::Bad(e)),

                Token::Eof
                | Token::Eol
                | Token::Comma
                | Token::Semicolon
                | Token::Then
                | Token::To
                | Token::Step => {
                    panic!("Field separators handled above")
                }

                Token::As
                | Token::BooleanName
                | Token::Dim
                | Token::DoubleName
                | Token::Else
                | Token::Elseif
                | Token::End
                | Token::For
                | Token::If
                | Token::IntegerName
                | Token::Next
                | Token::TextName
                | Token::Wend
                | Token::While => {
                    return Err(Error::Bad("Unexpected keyword in expression".to_owned()));
                }
            };
        }

        while let Some(op) = ops.pop() {
            match op {
                ExprOp::LeftParen => return Err(Error::Bad("Unbalanced parenthesis".to_owned())),
                _ => op.apply(&mut exprs)?,
            }
        }

        if let Some(expr) = exprs.pop() {
            Ok(Some(expr))
        } else {
            Ok(None)
        }
    }

    /// Parses an `IF` statement.
    fn parse_if(&mut self) -> Result<Statement> {
        let expr = match self.parse_expr(None)? {
            Some(expr) => expr,
            None => return Err(Error::Bad("No expression in IF statement".to_owned())),
        };
        self.expect_and_consume(Token::Then, "No THEN in IF statement")?;
        self.expect_and_consume(Token::Eol, "Expecting newline after THEN")?;

        let mut branches = vec![];
        branches.push((expr, self.parse_until(&[Token::Elseif, Token::Else, Token::End])?));
        loop {
            let peeked = self.lexer.peek()?;
            match peeked {
                Token::Elseif => {
                    self.lexer.consume_peeked();
                    let expr = match self.parse_expr(None)? {
                        Some(expr) => expr,
                        None => {
                            return Err(Error::Bad("No expression in ELSEIF statement".to_owned()))
                        }
                    };
                    self.expect_and_consume(Token::Then, "No THEN in ELSEIF statement")?;
                    self.expect_and_consume(Token::Eol, "Expecting newline after THEN")?;
                    let stmts2 = self.parse_until(&[Token::Elseif, Token::Else, Token::End])?;
                    branches.push((expr, stmts2));
                }
                _ => break,
            }
        }

        let peeked = self.lexer.peek()?;
        if *peeked == Token::Else {
            self.lexer.consume_peeked();
            self.expect_and_consume(Token::Eol, "Expecting newline after ELSE")?;
            let stmts2 = self.parse_until(&[Token::Elseif, Token::Else, Token::End])?;
            let peeked = self.lexer.peek()?;
            match *peeked {
                Token::Elseif => return Err(Error::Bad("Unexpected ELSEIF after ELSE".to_owned())),
                Token::Else => return Err(Error::Bad("Duplicate ELSE after ELSE".to_owned())),
                _ => (),
            }
            branches.push((Expr::Boolean(true), stmts2));
        }

        self.expect_and_consume(Token::End, "IF without END IF")?;
        self.expect_and_consume(Token::If, "IF without END IF")?;

        Ok(Statement::If(branches))
    }

    /// Advances until the next statement after failing to parse an `IF` statement.
    fn reset_if(&mut self) -> Result<()> {
        loop {
            match self.lexer.peek()? {
                Token::Eof => break,
                Token::End => {
                    self.lexer.consume_peeked();
                    self.expect_and_consume(Token::If, "IF without END IF")?;
                    break;
                }
                _ => {
                    self.lexer.consume_peeked();
                }
            }
        }
        self.reset()
    }

    /// Extracts the optional `STEP` part of a `FOR` statement, with a default of 1.
    fn parse_step(&mut self) -> Result<i32> {
        match self.lexer.peek()? {
            Token::Step => self.lexer.consume_peeked(),
            _ => return Ok(1),
        };

        match self.lexer.peek()? {
            Token::Integer(i) => {
                let i = *i;
                self.lexer.consume_peeked();
                Ok(i)
            }
            Token::Minus => {
                self.lexer.consume_peeked();
                match self.lexer.peek()? {
                    Token::Integer(i) => {
                        let i = *i;
                        self.lexer.consume_peeked();
                        Ok(-i)
                    }
                    _ => Err(Error::Bad("STEP needs an integer".to_owned())),
                }
            }
            _ => Err(Error::Bad("STEP needs an integer".to_owned())),
        }
    }

    /// Parses a `FOR` statement.
    fn parse_for(&mut self) -> Result<Statement> {
        let iterator = match self.lexer.read()? {
            Token::Symbol(iterator) => match iterator.ref_type() {
                // TODO(jmmv): Should we support doubles in for loops?
                VarType::Auto | VarType::Integer => iterator,
                _ => {
                    return Err(Error::Bad(
                        "Iterator name in FOR statement must be an integer reference".to_owned(),
                    ))
                }
            },
            _ => return Err(Error::Bad("No iterator name in FOR statement".to_owned())),
        };

        self.expect_and_consume(Token::Equal, "No equal sign in FOR statement")?;
        let start = match self.parse_expr(None)? {
            Some(expr) => expr,
            None => return Err(Error::Bad("No start expression in FOR statement".to_owned())),
        };

        self.expect_and_consume(Token::To, "No TO in FOR statement")?;
        let end = match self.parse_expr(None)? {
            Some(expr) => expr,
            None => return Err(Error::Bad("No end expression in FOR statement".to_owned())),
        };

        let step = self.parse_step()?;
        let end_condition = match step.cmp(&0) {
            Ordering::Greater => {
                Expr::LessEqual(Box::from(Expr::Symbol(iterator.clone())), Box::from(end))
            }
            Ordering::Less => {
                Expr::GreaterEqual(Box::from(Expr::Symbol(iterator.clone())), Box::from(end))
            }
            Ordering::Equal => {
                return Err(Error::Bad("Infinite FOR loop; STEP cannot be 0".to_owned()))
            }
        };

        let next_value =
            Expr::Add(Box::from(Expr::Symbol(iterator.clone())), Box::from(Expr::Integer(step)));

        self.expect_and_consume(Token::Eol, "Expecting newline after FOR")?;

        let stmts = self.parse_until(&[Token::Next])?;
        self.expect_and_consume(Token::Next, "FOR without NEXT")?;

        Ok(Statement::For(iterator, start, end_condition, next_value, stmts))
    }

    /// Advances until the next statement after failing to parse a `FOR` statement.
    fn reset_for(&mut self) -> Result<()> {
        loop {
            match self.lexer.peek()? {
                Token::Eof => break,
                Token::Next => {
                    self.lexer.consume_peeked();
                    break;
                }
                _ => {
                    self.lexer.consume_peeked();
                }
            }
        }
        self.reset()
    }

    /// Parses a `WHILE` statement.
    fn parse_while(&mut self) -> Result<Statement> {
        let expr = match self.parse_expr(None)? {
            Some(expr) => expr,
            None => return Err(Error::Bad("No expression in WHILE statement".to_owned())),
        };
        self.expect_and_consume(Token::Eol, "Expecting newline after WHILE")?;

        let stmts = self.parse_until(&[Token::Wend])?;
        self.expect_and_consume(Token::Wend, "WHILE without WEND")?;

        Ok(Statement::While(expr, stmts))
    }

    /// Advances until the next statement after failing to parse a `WHILE` statement.
    fn reset_while(&mut self) -> Result<()> {
        loop {
            match self.lexer.peek()? {
                Token::Eof => break,
                Token::End => {
                    self.lexer.consume_peeked();
                    self.expect_and_consume(Token::While, "WHILE without WEND")?;
                    break;
                }
                _ => {
                    self.lexer.consume_peeked();
                }
            }
        }
        self.reset()
    }

    /// Extracts the next available statement from the input stream, or `None` if none is available.
    ///
    /// On success, the stream is left in a position where the next statement can be extracted.
    /// On failure, the caller must advance the stream to the next statement by calling `reset`.
    fn parse_one(&mut self) -> Result<Option<Statement>> {
        loop {
            match self.lexer.peek()? {
                Token::Eol => {
                    self.lexer.consume_peeked();
                }
                Token::Eof => return Ok(None),
                _ => break,
            }
        }
        let res = match self.lexer.read()? {
            Token::Eof => return Ok(None),
            Token::Eol => Ok(None),
            Token::Dim => Ok(Some(self.parse_dim()?)),
            Token::If => {
                let result = self.parse_if();
                if result.is_err() {
                    self.reset_if()?;
                }
                Ok(Some(result?))
            }
            Token::For => {
                let result = self.parse_for();
                if result.is_err() {
                    self.reset_for()?;
                }
                Ok(Some(result?))
            }
            Token::Symbol(vref) => {
                let peeked = self.lexer.peek()?;
                if *peeked == Token::Equal {
                    self.lexer.consume_peeked();
                    Ok(Some(self.parse_assignment(vref)?))
                } else {
                    Ok(Some(self.parse_array_or_builtin_call(vref)?))
                }
            }
            Token::While => {
                let result = self.parse_while();
                if result.is_err() {
                    self.reset_while()?;
                }
                Ok(Some(result?))
            }
            t => return Err(Error::Bad(format!("Unexpected token {:?} in statement", t))),
        };

        match self.lexer.peek()? {
            Token::Eof => (),
            Token::Eol => {
                self.lexer.consume_peeked();
            }
            _ => return Err(Error::Bad("Expected newline".to_owned())),
        };

        res
    }

    /// Advances until the next statement after failing to parse a single statement.
    fn reset(&mut self) -> Result<()> {
        loop {
            match self.lexer.peek()? {
                Token::Eof => break,
                Token::Eol => {
                    self.lexer.consume_peeked();
                    break;
                }
                _ => {
                    self.lexer.consume_peeked();
                }
            }
        }
        Ok(())
    }

    /// Extracts the next available statement from the input stream, or `None` if none is available.
    ///
    /// The stream is always left in a position where the next statement extraction can be tried.
    pub fn parse(&mut self) -> Result<Option<Statement>> {
        let result = self.parse_one();
        if result.is_err() {
            self.reset()?;
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::VarType;

    /// Runs the parser on the given `input` and expects the returned statements to match
    /// `exp_statements`.
    fn do_ok_test(input: &str, exp_statements: &[Statement]) {
        let mut input = input.as_bytes();
        let mut parser = Parser::from(&mut input);

        let mut statements = vec![];
        loop {
            let statement = parser.parse().expect("Parsing failed");
            if statement.is_none() {
                break;
            }
            statements.push(statement.unwrap());
        }

        assert_eq!(exp_statements, statements.as_slice());
    }

    /// Runs the parser on the given `input` and expects the `err` error message.
    fn do_error_test(input: &str, expected_err: &str) {
        let mut input = input.as_bytes();
        let mut parser = Parser::from(&mut input);
        assert_eq!(expected_err, format!("{}", parser.parse().expect_err("Parsing did not fail")));
        assert!(parser.parse().unwrap().is_none());
    }

    /// Runs the parser on the given `input` and expects the `err` error message.
    ///
    /// Does not expect the parser to be reset to the next (EOF) statement.
    // TODO(jmmv): Need better testing to ensure the parser is reset to something that can be
    // parsed next.
    fn do_error_test_no_reset(input: &str, expected_err: &str) {
        let mut input = input.as_bytes();
        let mut parser = Parser::from(&mut input);
        assert_eq!(expected_err, format!("{}", parser.parse().expect_err("Parsing did not fail")));
    }

    #[test]
    fn test_empty() {
        do_ok_test("", &[]);
    }

    #[test]
    fn test_statement_separators() {
        do_ok_test(
            "a=1\nb=2:c=3:' A comment: that follows\nd=4",
            &[
                Statement::Assignment(VarRef::new("a", VarType::Auto), Expr::Integer(1)),
                Statement::Assignment(VarRef::new("b", VarType::Auto), Expr::Integer(2)),
                Statement::Assignment(VarRef::new("c", VarType::Auto), Expr::Integer(3)),
                Statement::Assignment(VarRef::new("d", VarType::Auto), Expr::Integer(4)),
            ],
        );
    }

    #[test]
    fn test_array_assignments() {
        do_ok_test(
            "a(1)=100\nfoo(2, 3)=\"text\"\nabc$ (5 + z, 6) = TRUE OR FALSE",
            &[
                Statement::ArrayAssignment(
                    VarRef::new("a", VarType::Auto),
                    vec![Expr::Integer(1)],
                    Expr::Integer(100),
                ),
                Statement::ArrayAssignment(
                    VarRef::new("foo", VarType::Auto),
                    vec![Expr::Integer(2), Expr::Integer(3)],
                    Expr::Text("text".to_owned()),
                ),
                Statement::ArrayAssignment(
                    VarRef::new("abc", VarType::Text),
                    vec![
                        Expr::Add(
                            Box::from(Expr::Integer(5)),
                            Box::from(Expr::Symbol(VarRef::new("z".to_owned(), VarType::Auto))),
                        ),
                        Expr::Integer(6),
                    ],
                    Expr::Or(Box::from(Expr::Boolean(true)), Box::from(Expr::Boolean(false))),
                ),
            ],
        );
    }

    #[test]
    fn test_array_assignment_errors() {
        do_error_test("a(", "Unexpected token");
        do_error_test("a()", "Expected expression");
        do_error_test("a() =", "Missing expression in array assignment");
        do_error_test("a() IF", "Expected expression");
        do_error_test("a() = 3 4", "Unexpected value in expression");
        do_error_test("a() = 3 THEN", "Unexpected token in array assignment");
        do_error_test("a(,) = 3", "Missing expression");
        do_error_test("a(2;3) = 3", "Unexpected token");
        do_error_test("(2) = 3", "Unexpected token LeftParen in statement");
    }

    #[test]
    fn test_assignments() {
        do_ok_test(
            "a=1\nfoo$ = \"bar\"\nb$ = 3 + z",
            &[
                Statement::Assignment(VarRef::new("a", VarType::Auto), Expr::Integer(1)),
                Statement::Assignment(
                    VarRef::new("foo", VarType::Text),
                    Expr::Text("bar".to_owned()),
                ),
                Statement::Assignment(
                    VarRef::new("b", VarType::Text),
                    Expr::Add(
                        Box::from(Expr::Integer(3)),
                        Box::from(Expr::Symbol(VarRef::new("z", VarType::Auto))),
                    ),
                ),
            ],
        );
    }

    #[test]
    fn test_assignment_errors() {
        do_error_test("a =", "Missing expression in assignment");
        do_error_test("a = b 3", "Unexpected value in expression");
        do_error_test("a = b, 3", "Unexpected token in assignment");
        do_error_test("a = if 3", "Unexpected keyword in expression");
        do_error_test("true = 1", "Unexpected token Boolean(true) in statement");
        do_error_test("3 = a", "Unexpected token Integer(3) in statement");
    }

    #[test]
    fn test_builtin_calls() {
        do_ok_test(
            "PRINT a\nPRINT ; 3 , c$\nNOARGS",
            &[
                Statement::BuiltinCall(
                    "PRINT".to_owned(),
                    vec![(Some(Expr::Symbol(VarRef::new("a", VarType::Auto))), ArgSep::End)],
                ),
                Statement::BuiltinCall(
                    "PRINT".to_owned(),
                    vec![
                        (None, ArgSep::Short),
                        (Some(Expr::Integer(3)), ArgSep::Long),
                        (Some(Expr::Symbol(VarRef::new("c", VarType::Text))), ArgSep::End),
                    ],
                ),
                Statement::BuiltinCall("NOARGS".to_owned(), vec![]),
            ],
        );
    }

    #[test]
    fn test_builtin_calls_and_array_references_disambiguation() {
        use Expr::*;

        do_ok_test(
            "PRINT(1)",
            &[Statement::BuiltinCall("PRINT".to_owned(), vec![(Some(Integer(1)), ArgSep::End)])],
        );

        do_ok_test(
            "PRINT(1), 2",
            &[Statement::BuiltinCall(
                "PRINT".to_owned(),
                vec![(Some(Integer(1)), ArgSep::Long), (Some(Integer(2)), ArgSep::End)],
            )],
        );

        do_ok_test(
            "PRINT(1); 2",
            &[Statement::BuiltinCall(
                "PRINT".to_owned(),
                vec![(Some(Integer(1)), ArgSep::Short), (Some(Integer(2)), ArgSep::End)],
            )],
        );

        do_ok_test(
            "PRINT(1);",
            &[Statement::BuiltinCall(
                "PRINT".to_owned(),
                vec![(Some(Integer(1)), ArgSep::Short), (None, ArgSep::End)],
            )],
        );

        do_ok_test(
            "PRINT(1) + 2; 3",
            &[Statement::BuiltinCall(
                "PRINT".to_owned(),
                vec![
                    (Some(Add(Box::from(Integer(1)), Box::from(Integer(2)))), ArgSep::Short),
                    (Some(Integer(3)), ArgSep::End),
                ],
            )],
        );
    }

    #[test]
    fn test_builtin_calls_error() {
        do_error_test("FOO 3 5\n", "Unexpected value in expression");
        do_error_test("INPUT$ a\n", "Type annotation not allowed in INPUT$");
        do_error_test("PRINT IF 1\n", "Unexpected keyword in expression");
        do_error_test("PRINT 3, IF 1\n", "Unexpected keyword in expression");
        do_error_test("PRINT 3 THEN\n", "Expected comma, semicolon, or end of statement");
        do_error_test("PRINT ()\n", "Expected expression");
        do_error_test("PRINT (2, 3)\n", "Expected expression");
        do_error_test("PRINT (2, 3); 4\n", "Expected expression");
    }

    #[test]
    fn test_dim_default_type() {
        do_ok_test("DIM i", &[Statement::Dim("i".to_owned(), VarType::Integer)]);
    }

    #[test]
    fn test_dim_as_simple_types() {
        do_ok_test("DIM i AS BOOLEAN", &[Statement::Dim("i".to_owned(), VarType::Boolean)]);
        do_ok_test("DIM i AS DOUBLE", &[Statement::Dim("i".to_owned(), VarType::Double)]);
        do_ok_test("DIM i AS INTEGER", &[Statement::Dim("i".to_owned(), VarType::Integer)]);
        do_ok_test("DIM i AS STRING", &[Statement::Dim("i".to_owned(), VarType::Text)]);
    }

    #[test]
    fn test_dim_consecutive() {
        do_ok_test(
            "DIM i\nDIM j AS BOOLEAN\nDIM k",
            &[
                Statement::Dim("i".to_owned(), VarType::Integer),
                Statement::Dim("j".to_owned(), VarType::Boolean),
                Statement::Dim("k".to_owned(), VarType::Integer),
            ],
        );
    }

    #[test]
    fn test_dim_array() {
        use Expr::*;

        do_ok_test(
            "DIM i(10)",
            &[Statement::DimArray("i".to_owned(), vec![Integer(10)], VarType::Integer)],
        );

        do_ok_test(
            "DIM foo(-5, 0) AS STRING",
            &[Statement::DimArray(
                "foo".to_owned(),
                vec![Negate(Box::from(Integer(5))), Integer(0)],
                VarType::Text,
            )],
        );

        do_ok_test(
            "DIM foo(bar$() + 3, 8, -1)",
            &[Statement::DimArray(
                "foo".to_owned(),
                vec![
                    Add(
                        Box::from(Call(VarRef::new("bar", VarType::Text), vec![])),
                        Box::from(Integer(3)),
                    ),
                    Integer(8),
                    Negate(Box::from(Integer(1))),
                ],
                VarType::Integer,
            )],
        );
    }

    #[test]
    fn test_dim_errors() {
        do_error_test("DIM", "Expected variable name after DIM");
        do_error_test("DIM 3", "Expected variable name after DIM");
        do_error_test("DIM AS", "Expected variable name after DIM");
        do_error_test("DIM foo 3", "Expected AS or end of statement");
        do_error_test("DIM a AS", "Invalid type name Eof in DIM AS statement");
        do_error_test("DIM a$ AS", "Type annotation not allowed in a$");
        do_error_test("DIM a AS 3", "Invalid type name Integer(3) in DIM AS statement");
        do_error_test("DIM a AS INTEGER 3", "Unexpected token in DIM statement");

        do_error_test("DIM a()", "Arrays require at least one dimension");
        do_error_test("DIM a(,)", "Missing expression");
        do_error_test("DIM a(, 3)", "Missing expression");
        do_error_test("DIM a(3, )", "Missing expression");
        do_error_test("DIM a(3, , 4)", "Missing expression");
        do_error_test("DIM a(1) AS INTEGER 3", "Unexpected token in DIM statement");
    }

    /// Wrapper around `do_ok_test` to parse an expression.  Given that expressions alone are not
    /// valid statements, we have to put them in a statement to parse them.  In doing so, we can
    /// also put an extra statement after them to ensure we detect their end properly.
    fn do_expr_ok_test(input: &str, expr: Expr) {
        do_ok_test(
            &format!("PRINT {}, 1", input),
            &[Statement::BuiltinCall(
                "PRINT".to_owned(),
                vec![(Some(expr), ArgSep::Long), (Some(Expr::Integer(1)), ArgSep::End)],
            )],
        );
    }

    /// Wrapper around `do_error_test` to parse an expression.  Given that expressions alone are not
    /// valid statements, we have to put them in a statement to parse them.  In doing so, we can
    /// also put an extra statement after them to ensure we detect their end properly.
    fn do_expr_error_test(input: &str, msg: &str) {
        do_error_test(&format!("PRINT {}, 1", input), msg)
    }

    #[test]
    fn test_expr_literals() {
        use Expr::*;
        do_expr_ok_test("TRUE", Boolean(true));
        do_expr_ok_test("FALSE", Boolean(false));
        do_expr_ok_test("5", Integer(5));
        do_expr_ok_test("\"some text\"", Text("some text".to_owned()));
    }

    #[test]
    fn test_expr_symbols() {
        use Expr::*;
        do_expr_ok_test("foo", Symbol(VarRef::new("foo", VarType::Auto)));
        do_expr_ok_test("bar$", Symbol(VarRef::new("bar", VarType::Text)));
    }

    #[test]
    fn test_expr_parens() {
        use Expr::*;
        do_expr_ok_test("(1)", Integer(1));
        do_expr_ok_test("((1))", Integer(1));
        do_expr_ok_test(" ( ( 1 ) ) ", Integer(1));
        do_expr_ok_test(
            "3 * (2 + 5)",
            Multiply(
                Box::from(Integer(3)),
                Box::from(Add(Box::from(Integer(2)), Box::from(Integer(5)))),
            ),
        );
        do_expr_ok_test(
            "(7) - (1) + (-2)",
            Add(
                Box::from(Subtract(Box::from(Integer(7)), Box::from(Integer(1)))),
                Box::from(Negate(Box::from(Integer(2)))),
            ),
        );
    }

    #[test]
    fn test_expr_arith_ops() {
        use Expr::*;
        do_expr_ok_test("1 + 2", Add(Box::from(Integer(1)), Box::from(Integer(2))));
        do_expr_ok_test("1 - 2", Subtract(Box::from(Integer(1)), Box::from(Integer(2))));
        do_expr_ok_test("1 * 2", Multiply(Box::from(Integer(1)), Box::from(Integer(2))));
        do_expr_ok_test("1 / 2", Divide(Box::from(Integer(1)), Box::from(Integer(2))));
        do_expr_ok_test("1 MOD 2", Modulo(Box::from(Integer(1)), Box::from(Integer(2))));
    }

    #[test]
    fn test_expr_rel_ops() {
        use Expr::*;
        do_expr_ok_test("1 = 2", Equal(Box::from(Integer(1)), Box::from(Integer(2))));
        do_expr_ok_test("1 <> 2", NotEqual(Box::from(Integer(1)), Box::from(Integer(2))));
        do_expr_ok_test("1 < 2", Less(Box::from(Integer(1)), Box::from(Integer(2))));
        do_expr_ok_test("1 <= 2", LessEqual(Box::from(Integer(1)), Box::from(Integer(2))));
        do_expr_ok_test("1 > 2", Greater(Box::from(Integer(1)), Box::from(Integer(2))));
        do_expr_ok_test("1 >= 2", GreaterEqual(Box::from(Integer(1)), Box::from(Integer(2))));
    }

    #[test]
    fn test_expr_logical_ops() {
        use Expr::*;
        do_expr_ok_test("1 AND 2", And(Box::from(Integer(1)), Box::from(Integer(2))));
        do_expr_ok_test("1 OR 2", Or(Box::from(Integer(1)), Box::from(Integer(2))));
        do_expr_ok_test("1 XOR 2", Xor(Box::from(Integer(1)), Box::from(Integer(2))));
    }

    #[test]
    fn test_expr_logical_ops_not() {
        use Expr::*;
        do_expr_ok_test("NOT TRUE", Not(Box::from(Boolean(true))));
        do_expr_ok_test("NOT 6", Not(Box::from(Integer(6))));
        do_expr_ok_test("NOT NOT TRUE", Not(Box::from(Not(Box::from(Boolean(true))))));
        do_expr_ok_test(
            "1 - NOT 4",
            Subtract(Box::from(Integer(1)), Box::from(Not(Box::from(Integer(4))))),
        );
    }

    #[test]
    fn test_expr_op_priorities() {
        use Expr::*;
        do_expr_ok_test(
            "3 * (2 + 5) = (3 + 1 = 2 OR 1 = 3 XOR FALSE * \"a\")",
            Equal(
                Box::from(Multiply(
                    Box::from(Integer(3)),
                    Box::from(Add(Box::from(Integer(2)), Box::from(Integer(5)))),
                )),
                Box::from(Xor(
                    Box::from(Or(
                        Box::from(Equal(
                            Box::from(Add(Box::from(Integer(3)), Box::from(Integer(1)))),
                            Box::from(Integer(2)),
                        )),
                        Box::from(Equal(Box::from(Integer(1)), Box::from(Integer(3)))),
                    )),
                    Box::from(Multiply(Box::from(Boolean(false)), Box::from(Text("a".to_owned())))),
                )),
            ),
        );
    }

    #[test]
    fn test_expr_numeric_signs() {
        use Expr::*;

        do_expr_ok_test("-a", Negate(Box::from(Symbol(VarRef::new("a", VarType::Auto)))));

        do_expr_ok_test(
            "1 - -3",
            Subtract(Box::from(Integer(1)), Box::from(Negate(Box::from(Integer(3))))),
        );
        do_expr_ok_test(
            "-1 - 3",
            Subtract(Box::from(Negate(Box::from(Integer(1)))), Box::from(Integer(3))),
        );
        do_expr_ok_test(
            "5 + -1",
            Add(Box::from(Integer(5)), Box::from(Negate(Box::from(Integer(1))))),
        );
        do_expr_ok_test(
            "-5 + 1",
            Add(Box::from(Negate(Box::from(Integer(5)))), Box::from(Integer(1))),
        );
        do_expr_ok_test("NOT -3", Not(Box::from(Negate(Box::from(Integer(3))))));

        do_expr_ok_test(
            "1.0 - -3.5",
            Subtract(Box::from(Double(1.0)), Box::from(Negate(Box::from(Double(3.5))))),
        );
        do_expr_ok_test(
            "5.12 + -0.50",
            Add(Box::from(Double(5.12)), Box::from(Negate(Box::from(Double(0.50))))),
        );
        do_expr_ok_test("NOT -3", Not(Box::from(Negate(Box::from(Integer(3))))));
    }

    #[test]
    fn test_expr_functions_variadic() {
        use Expr::*;
        do_expr_ok_test("zero()", Call(VarRef::new("zero", VarType::Auto), vec![]));
        do_expr_ok_test("one%(1)", Call(VarRef::new("one", VarType::Integer), vec![Integer(1)]));
        do_expr_ok_test(
            "many$(3, \"x\", TRUE)",
            Call(
                VarRef::new("many", VarType::Text),
                vec![Integer(3), Text("x".to_owned()), Boolean(true)],
            ),
        );
    }

    #[test]
    fn test_expr_functions_nested() {
        use Expr::*;
        do_expr_ok_test(
            "consecutive(parenthesis())",
            Call(
                VarRef::new("consecutive", VarType::Auto),
                vec![Call(VarRef::new("parenthesis", VarType::Auto), vec![])],
            ),
        );
        do_expr_ok_test(
            "outer?(1, inner1(2, 3), 4, inner2(), 5)",
            Call(
                VarRef::new("outer", VarType::Boolean),
                vec![
                    Integer(1),
                    Call(VarRef::new("inner1", VarType::Auto), vec![Integer(2), Integer(3)]),
                    Integer(4),
                    Call(VarRef::new("inner2", VarType::Auto), vec![]),
                    Integer(5),
                ],
            ),
        );
    }

    #[test]
    fn test_expr_functions_and_ops() {
        use Expr::*;
        do_expr_ok_test(
            "b AND ask?(34 + 15, ask(1, FALSE), -5)",
            And(
                Box::from(Symbol(VarRef::new("b".to_owned(), VarType::Auto))),
                Box::from(Call(
                    VarRef::new("ask", VarType::Boolean),
                    vec![
                        Add(Box::from(Integer(34)), Box::from(Integer(15))),
                        Call(VarRef::new("ask", VarType::Auto), vec![Integer(1), Boolean(false)]),
                        Negate(Box::from(Integer(5))),
                    ],
                )),
            ),
        );
    }

    #[test]
    fn test_expr_functions_not_confused_with_symbols() {
        use Expr::*;
        let iref = VarRef::new("i", VarType::Auto);
        let jref = VarRef::new("j", VarType::Auto);
        do_expr_ok_test(
            "i = 0 OR i = (j - 1)",
            Or(
                Box::from(Equal(Box::from(Symbol(iref.clone())), Box::from(Integer(0)))),
                Box::from(Equal(
                    Box::from(Symbol(iref)),
                    Box::from(Subtract(Box::from(Symbol(jref)), Box::from(Integer(1)))),
                )),
            ),
        );
    }

    #[test]
    fn test_expr_errors() {
        do_expr_error_test("+3", "Not enough values to apply operator");
        do_expr_error_test("2 + * 3", "Not enough values to apply operator");
        do_expr_error_test("(2(3))", "Unexpected value in expression");
        do_expr_error_test("((3)2)", "Unexpected value in expression");
        do_expr_error_test("2 3", "Unexpected value in expression");

        do_expr_error_test("(", "Missing expression");
        do_expr_error_test(")", "Expected comma, semicolon, or end of statement");
        do_expr_error_test("(()", "Missing expression");
        do_expr_error_test("())", "Expected expression");
        do_expr_error_test("3 + (2 + 1) + (4 - 5", "Unbalanced parenthesis");
        do_expr_error_test(
            "3 + 2 + 1) + (4 - 5)",
            "Expected comma, semicolon, or end of statement",
        );

        do_expr_error_test("foo(,)", "Missing expression");
        do_expr_error_test("foo(, 3)", "Missing expression");
        do_expr_error_test("foo(3, )", "Missing expression");
        do_expr_error_test("foo(3, , 4)", "Missing expression");
        // TODO(jmmv): These are not the best error messages...
        do_expr_error_test("(,)", "Missing expression");
        do_expr_error_test("(3, 4)", "Expected expression");
        do_expr_error_test("((), ())", "Missing expression");

        // TODO(jmmv): This succeeds because `PRINT` is interned as a `Token::Symbol` so the
        // expression parser sees it as a variable reference... but this should probably fail.
        // Would need to intern builtin call names as a separate token to catch this, but that
        // also means that the lexer must be aware of builtin call names upfront.
        use Expr::*;
        do_expr_ok_test(
            "1 + PRINT",
            Add(Box::from(Integer(1)), Box::from(Symbol(VarRef::new("PRINT", VarType::Auto)))),
        );
    }

    #[test]
    fn test_expr_errors_due_to_keywords() {
        for kw in &[
            "AS", "BOOLEAN", "DIM", "DOUBLE", "ELSE", "ELSEIF", "END", "FOR", "IF", "INTEGER",
            "NEXT", "STRING", "WHILE",
        ] {
            do_expr_error_test(&format!("2 + {} - 1", kw), "Unexpected keyword in expression");
        }
    }

    #[test]
    fn test_if_empty_branches() {
        do_ok_test("IF 1 THEN\nEND IF", &[Statement::If(vec![(Expr::Integer(1), vec![])])]);
        do_ok_test(
            "IF 1 THEN\nREM Some comment to skip over\n\nEND IF",
            &[Statement::If(vec![(Expr::Integer(1), vec![])])],
        );
        do_ok_test(
            "IF 1 THEN\nELSEIF 2 THEN\nEND IF",
            &[Statement::If(vec![(Expr::Integer(1), vec![]), (Expr::Integer(2), vec![])])],
        );
        do_ok_test(
            "IF 1 THEN\nELSEIF 2 THEN\nELSE\nEND IF",
            &[Statement::If(vec![
                (Expr::Integer(1), vec![]),
                (Expr::Integer(2), vec![]),
                (Expr::Boolean(true), vec![]),
            ])],
        );
        do_ok_test(
            "IF 1 THEN\nELSE\nEND IF",
            &[Statement::If(vec![(Expr::Integer(1), vec![]), (Expr::Boolean(true), vec![])])],
        );
    }

    #[test]
    fn test_if_with_one_statement_or_empty_lines() {
        do_ok_test(
            "IF 1 THEN\nPRINT\nEND IF",
            &[Statement::If(vec![(
                Expr::Integer(1),
                vec![Statement::BuiltinCall("PRINT".to_owned(), vec![])],
            )])],
        );
        do_ok_test(
            "IF 1 THEN\nREM foo\nELSEIF 2 THEN\nPRINT\nEND IF",
            &[Statement::If(vec![
                (Expr::Integer(1), vec![]),
                (Expr::Integer(2), vec![Statement::BuiltinCall("PRINT".to_owned(), vec![])]),
            ])],
        );
        do_ok_test(
            "IF 1 THEN\nELSEIF 2 THEN\nELSE\n\nPRINT\nEND IF",
            &[Statement::If(vec![
                (Expr::Integer(1), vec![]),
                (Expr::Integer(2), vec![]),
                (Expr::Boolean(true), vec![Statement::BuiltinCall("PRINT".to_owned(), vec![])]),
            ])],
        );
        do_ok_test(
            "IF 1 THEN\n\n\nELSE\nPRINT\nEND IF",
            &[Statement::If(vec![
                (Expr::Integer(1), vec![]),
                (Expr::Boolean(true), vec![Statement::BuiltinCall("PRINT".to_owned(), vec![])]),
            ])],
        );
    }

    #[test]
    fn test_if_complex() {
        let code = r#"
            IF 1 THEN 'First branch
                A
                B
            ELSEIF 2 THEN 'Second branch
                C
                D
            ELSEIF 3 THEN 'Third branch
                E
                F
            ELSE 'Last branch
                G
                H
            END IF
        "#;
        do_ok_test(
            code,
            &[Statement::If(vec![
                (
                    Expr::Integer(1),
                    vec![
                        Statement::BuiltinCall("A".to_owned(), vec![]),
                        Statement::BuiltinCall("B".to_owned(), vec![]),
                    ],
                ),
                (
                    Expr::Integer(2),
                    vec![
                        Statement::BuiltinCall("C".to_owned(), vec![]),
                        Statement::BuiltinCall("D".to_owned(), vec![]),
                    ],
                ),
                (
                    Expr::Integer(3),
                    vec![
                        Statement::BuiltinCall("E".to_owned(), vec![]),
                        Statement::BuiltinCall("F".to_owned(), vec![]),
                    ],
                ),
                (
                    Expr::Boolean(true),
                    vec![
                        Statement::BuiltinCall("G".to_owned(), vec![]),
                        Statement::BuiltinCall("H".to_owned(), vec![]),
                    ],
                ),
            ])],
        );
    }

    #[test]
    fn test_if_nested() {
        let code = r#"
            IF 1 THEN
                A
            ELSEIF 2 THEN
                IF 3 THEN
                    B
                END IF
            END IF
        "#;
        do_ok_test(
            code,
            &[Statement::If(vec![
                (Expr::Integer(1), vec![Statement::BuiltinCall("A".to_owned(), vec![])]),
                (
                    Expr::Integer(2),
                    vec![Statement::If(vec![(
                        Expr::Integer(3),
                        vec![Statement::BuiltinCall("B".to_owned(), vec![])],
                    )])],
                ),
            ])],
        );
    }

    #[test]
    fn test_if_errors() {
        do_error_test("IF\n", "No expression in IF statement");
        do_error_test("IF 3 + 1", "No THEN in IF statement");
        do_error_test("IF 3 + 1\n", "No THEN in IF statement");
        do_error_test("IF 3 + 1 PRINT foo\n", "Unexpected value in expression");
        do_error_test("IF 3 + 1\nPRINT foo\n", "No THEN in IF statement");
        do_error_test("IF 3 + 1 THEN", "Expecting newline after THEN");

        do_error_test("IF 1 THEN\n", "IF without END IF");
        do_error_test("IF 1 THEN\nELSEIF 1 THEN\n", "IF without END IF");
        do_error_test("IF 1 THEN\nELSE\n", "IF without END IF");

        do_error_test("IF 1 THEN\nELSEIF\n", "No expression in ELSEIF statement");
        do_error_test("IF 1 THEN\nELSEIF 3 + 1", "No THEN in ELSEIF statement");
        do_error_test("IF 1 THEN\nELSEIF 3 + 1\n", "No THEN in ELSEIF statement");
        do_error_test("IF 1 THEN\nELSEIF 3 + 1 PRINT foo\n", "Unexpected value in expression");
        do_error_test("IF 1 THEN\nELSEIF 3 + 1\nPRINT foo\n", "No THEN in ELSEIF statement");
        do_error_test("IF 1 THEN\nELSEIF 3 + 1 THEN", "Expecting newline after THEN");

        do_error_test("IF 1 THEN\nELSE", "Expecting newline after ELSE");
        do_error_test("IF 1 THEN\nELSE foo", "Expecting newline after ELSE");

        do_error_test("IF 1 THEN\nEND", "IF without END IF");
        do_error_test("IF 1 THEN\nEND\n", "IF without END IF");
        do_error_test("IF 1 THEN\nEND IF foo", "Expected newline");

        do_error_test("IF 1 THEN\nELSE\nELSEIF 2 THEN\nEND IF", "Unexpected ELSEIF after ELSE");
        do_error_test("IF 1 THEN\nELSE\nELSE\nEND IF", "Duplicate ELSE after ELSE");

        do_error_test_no_reset("ELSEIF 1 THEN\nEND IF", "Unexpected token Elseif in statement");
        do_error_test_no_reset("ELSE 1\nEND IF", "Unexpected token Else in statement");
    }

    #[test]
    fn test_for_empty() {
        let auto_iter = VarRef::new("i", VarType::Auto);
        do_ok_test(
            "FOR i = 1 TO 10\nNEXT",
            &[Statement::For(
                auto_iter.clone(),
                Expr::Integer(1),
                Expr::LessEqual(
                    Box::from(Expr::Symbol(auto_iter.clone())),
                    Box::from(Expr::Integer(10)),
                ),
                Expr::Add(Box::from(Expr::Symbol(auto_iter)), Box::from(Expr::Integer(1))),
                vec![],
            )],
        );

        let typed_iter = VarRef::new("i", VarType::Integer);
        do_ok_test(
            "FOR i% = 1 TO 10\nREM Nothing to do\nNEXT",
            &[Statement::For(
                typed_iter.clone(),
                Expr::Integer(1),
                Expr::LessEqual(
                    Box::from(Expr::Symbol(typed_iter.clone())),
                    Box::from(Expr::Integer(10)),
                ),
                Expr::Add(Box::from(Expr::Symbol(typed_iter)), Box::from(Expr::Integer(1))),
                vec![],
            )],
        );
    }

    #[test]
    fn test_for_incrementing() {
        let iter = VarRef::new("i", VarType::Auto);
        do_ok_test(
            "FOR i = 0 TO 5\nA\nB\nNEXT",
            &[Statement::For(
                iter.clone(),
                Expr::Integer(0),
                Expr::LessEqual(Box::from(Expr::Symbol(iter.clone())), Box::from(Expr::Integer(5))),
                Expr::Add(Box::from(Expr::Symbol(iter)), Box::from(Expr::Integer(1))),
                vec![
                    Statement::BuiltinCall("A".to_owned(), vec![]),
                    Statement::BuiltinCall("B".to_owned(), vec![]),
                ],
            )],
        );
    }

    #[test]
    fn test_for_incrementing_with_step() {
        let iter = VarRef::new("i", VarType::Auto);
        do_ok_test(
            "FOR i = 0 TO 5 STEP 2\nA\nNEXT",
            &[Statement::For(
                iter.clone(),
                Expr::Integer(0),
                Expr::LessEqual(Box::from(Expr::Symbol(iter.clone())), Box::from(Expr::Integer(5))),
                Expr::Add(Box::from(Expr::Symbol(iter)), Box::from(Expr::Integer(2))),
                vec![Statement::BuiltinCall("A".to_owned(), vec![])],
            )],
        );
    }

    #[test]
    fn test_for_decrementing_with_step() {
        let iter = VarRef::new("i", VarType::Auto);
        do_ok_test(
            "FOR i = 5 TO 0 STEP -1\nA\nNEXT",
            &[Statement::For(
                iter.clone(),
                Expr::Integer(5),
                Expr::GreaterEqual(
                    Box::from(Expr::Symbol(iter.clone())),
                    Box::from(Expr::Integer(0)),
                ),
                Expr::Add(Box::from(Expr::Symbol(iter)), Box::from(Expr::Integer(-1))),
                vec![Statement::BuiltinCall("A".to_owned(), vec![])],
            )],
        );
    }

    #[test]
    fn test_for_errors() {
        do_error_test("FOR\n", "No iterator name in FOR statement");
        do_error_test("FOR =\n", "No iterator name in FOR statement");
        do_error_test("FOR a$\n", "Iterator name in FOR statement must be an integer reference");
        do_error_test("FOR d#\n", "Iterator name in FOR statement must be an integer reference");

        do_error_test("FOR i 3\n", "No equal sign in FOR statement");
        do_error_test("FOR i = TO\n", "No start expression in FOR statement");
        do_error_test("FOR i = NEXT\n", "Unexpected keyword in expression");

        do_error_test("FOR i = 3 STEP\n", "No TO in FOR statement");
        do_error_test("FOR i = 3 TO STEP\n", "No end expression in FOR statement");
        do_error_test("FOR i = 3 TO NEXT\n", "Unexpected keyword in expression");

        do_error_test("FOR i = 3 TO 1 STEP a\n", "STEP needs an integer");
        do_error_test("FOR i = 3 TO 1 STEP -a\n", "STEP needs an integer");
        do_error_test("FOR i = 3 TO 1 STEP NEXT\n", "STEP needs an integer");
        do_error_test("FOR i = 3 TO 1 STEP 0\n", "Infinite FOR loop; STEP cannot be 0");

        do_error_test("FOR i = 3 TO 1", "Expecting newline after FOR");
        do_error_test("FOR i = 1 TO 3 STEP 1", "Expecting newline after FOR");
        do_error_test("FOR i = 3 TO 1 STEP -1", "Expecting newline after FOR");

        do_error_test("FOR i = 0 TO 10\nPRINT i\n", "FOR without NEXT");
    }

    #[test]
    fn test_while_empty() {
        do_ok_test(
            "WHILE 2 + 3\nWEND",
            &[Statement::While(
                Expr::Add(Box::from(Expr::Integer(2)), Box::from(Expr::Integer(3))),
                vec![],
            )],
        );
        do_ok_test("WHILE 5\n\nREM foo\n\nWEND\n", &[Statement::While(Expr::Integer(5), vec![])]);
    }

    #[test]
    fn test_while_loops() {
        do_ok_test(
            "WHILE TRUE\nA\nB\nWEND",
            &[Statement::While(
                Expr::Boolean(true),
                vec![
                    Statement::BuiltinCall("A".to_owned(), vec![]),
                    Statement::BuiltinCall("B".to_owned(), vec![]),
                ],
            )],
        );
    }

    #[test]
    fn test_while_nested() {
        let code = r#"
            WHILE TRUE
                A
                WHILE FALSE
                    B
                WEND
                C
            WEND
        "#;
        do_ok_test(
            code,
            &[Statement::While(
                Expr::Boolean(true),
                vec![
                    Statement::BuiltinCall("A".to_owned(), vec![]),
                    Statement::While(
                        Expr::Boolean(false),
                        vec![Statement::BuiltinCall("B".to_owned(), vec![])],
                    ),
                    Statement::BuiltinCall("C".to_owned(), vec![]),
                ],
            )],
        );
    }

    #[test]
    fn test_while_errors() {
        do_error_test("WHILE\n", "No expression in WHILE statement");
        do_error_test("WHILE TRUE", "Expecting newline after WHILE");
        do_error_test("WHILE TRUE\n", "WHILE without WEND");
        do_error_test("WHILE TRUE\nEND", "Unexpected token End in statement");
        do_error_test("WHILE TRUE\nEND\n", "Unexpected token End in statement");
        do_error_test("WHILE TRUE\nEND WHILE\n", "Unexpected token End in statement");

        do_error_test("WHILE ,\nWEND", "No expression in WHILE statement");
    }
}
