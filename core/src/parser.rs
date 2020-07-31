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

use crate::ast::{ArgSep, Expr, Statement, VarRef};
use crate::lexer::{Lexer, PeekableLexer, Token};
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
        let expr = match self.parse_expr()? {
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

    /// Parses a builtin call (things of the form `INPUT a`).
    fn parse_builtin_call(&mut self, vref: VarRef) -> Result<Statement> {
        let mut name = match vref.into_unannotated_string() {
            Ok(name) => name,
            Err(e) => return Err(Error::Bad(format!("{}", e))),
        };
        name.make_ascii_uppercase();

        let mut args = vec![];
        loop {
            let expr = self.parse_expr()?;

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

    /// Parses an expression.
    ///
    /// It is important to single out the special `Empty` expression as a possible return value,
    /// which denotes that no expression was found.  This is necessary to treat the case of empty
    /// arguments to statements, as is the case in `PRINT a , , b`.
    ///
    /// This is an implementation of the Shunting Yard Algorithm by Edgar Dijkstra.
    fn parse_expr(&mut self) -> Result<Option<Expr>> {
        let mut exprs: Vec<Expr> = vec![];
        let mut ops: Vec<ExprOp> = vec![];

        let mut need_operand = true; // Also tracks whether an upcoming minus is unary.
        loop {
            let mut handle_operand = |e| {
                if !need_operand {
                    return Err(Error::Bad("Unexpected value in expression".to_owned()));
                }
                need_operand = false;
                exprs.push(e);
                Ok(())
            };

            match self.lexer.peek()? {
                Token::Eof | Token::Eol | Token::Comma | Token::Semicolon | Token::Then => break,
                _ => (),
            };
            let token = self.lexer.consume_peeked();
            match token {
                Token::Boolean(b) => handle_operand(Expr::Boolean(b))?,
                Token::Integer(i) => handle_operand(Expr::Integer(i))?,
                Token::Text(t) => handle_operand(Expr::Text(t))?,
                Token::Symbol(vref) => handle_operand(Expr::Symbol(vref))?,

                Token::LeftParen => {
                    if !need_operand {
                        return Err(Error::Bad("Unexpected value in expression".to_owned()));
                    }
                    ops.push(ExprOp::LeftParen);
                    need_operand = true;
                }
                Token::RightParen => {
                    while let Some(op) = ops.pop() {
                        op.apply(&mut exprs)?;
                        if op == ExprOp::LeftParen {
                            break;
                        }
                    }
                    need_operand = false;
                }

                Token::Not => {
                    ops.push(ExprOp::Not);
                    need_operand = true;
                }
                Token::Minus => {
                    if need_operand {
                        ops.push(ExprOp::Negate);
                    } else {
                        ops.push(ExprOp::Subtract);
                    }
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

                Token::Eof | Token::Eol | Token::Comma | Token::Semicolon | Token::Then => {
                    panic!("Field separators handled above")
                }

                Token::If | Token::Else | Token::Elseif | Token::End | Token::While => {
                    return Err(Error::Bad("Unexpected keyword in expression".to_owned()));
                }
            };
        }

        while let Some(op) = ops.pop() {
            op.apply(&mut exprs)?;
        }

        if let Some(expr) = exprs.pop() {
            Ok(Some(expr))
        } else {
            Ok(None)
        }
    }

    /// Parses an `IF` statement.
    fn parse_if(&mut self) -> Result<Statement> {
        let expr = match self.parse_expr()? {
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
                    let expr = match self.parse_expr()? {
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

    /// Parses a `WHILE` statement.
    fn parse_while(&mut self) -> Result<Statement> {
        let expr = match self.parse_expr()? {
            Some(expr) => expr,
            None => return Err(Error::Bad("No expression in WHILE statement".to_owned())),
        };
        self.expect_and_consume(Token::Eol, "Expecting newline after WHILE")?;

        let stmts = self.parse_until(&[Token::End])?;
        self.expect_and_consume(Token::End, "WHILE without END WHILE")?;
        self.expect_and_consume(Token::While, "WHILE without END WHILE")?;

        Ok(Statement::While(expr, stmts))
    }

    /// Advances until the next statement after failing to parse a `WHILE` statement.
    fn reset_while(&mut self) -> Result<()> {
        loop {
            match self.lexer.peek()? {
                Token::Eof => break,
                Token::End => {
                    self.lexer.consume_peeked();
                    self.expect_and_consume(Token::While, "WHILE without END WHILE")?;
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
            Token::If => {
                let result = self.parse_if();
                if result.is_err() {
                    self.reset_if()?;
                }
                Ok(Some(result?))
            }
            Token::Symbol(vref) => {
                let peeked = self.lexer.peek()?;
                if *peeked == Token::Equal {
                    self.lexer.consume_peeked();
                    Ok(Some(self.parse_assignment(vref)?))
                } else {
                    Ok(Some(self.parse_builtin_call(vref)?))
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
    fn test_builtin_calls_error() {
        do_error_test("FOO 3 5\n", "Unexpected value in expression");
        do_error_test("INPUT$ a\n", "Type annotation not allowed in INPUT$");
        do_error_test("PRINT IF 1\n", "Unexpected keyword in expression");
        do_error_test("PRINT 3, IF 1\n", "Unexpected keyword in expression");
        do_error_test("PRINT 3 THEN\n", "Expected comma, semicolon, or end of statement");
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
    fn test_expr_integer_signs() {
        use Expr::*;
        do_expr_ok_test("-a", Negate(Box::from(Symbol(VarRef::new("a", VarType::Auto)))));
        do_expr_ok_test(
            "1 - -3",
            Subtract(Box::from(Integer(1)), Box::from(Negate(Box::from(Integer(3))))),
        );
        do_expr_ok_test(
            "5 + -1",
            Add(Box::from(Integer(5)), Box::from(Negate(Box::from(Integer(1))))),
        );
        do_expr_ok_test("NOT -3", Not(Box::from(Negate(Box::from(Integer(3))))));
    }

    #[test]
    fn test_expr_errors() {
        do_expr_error_test("+3", "Not enough values to apply operator");
        do_expr_error_test("2 + * 3", "Not enough values to apply operator");
        do_expr_error_test("(2(3))", "Unexpected value in expression");
        do_expr_error_test("((3)2)", "Unexpected value in expression");
        do_expr_error_test("2 3", "Unexpected value in expression");

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
        for kw in &["IF", "ELSEIF", "ELSE", "END", "WHILE"] {
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
    fn test_while_empty() {
        do_ok_test(
            "WHILE 2 + 3\nEND WHILE",
            &[Statement::While(
                Expr::Add(Box::from(Expr::Integer(2)), Box::from(Expr::Integer(3))),
                vec![],
            )],
        );
        do_ok_test(
            "WHILE 5\n\nREM foo\n\nEND WHILE\n",
            &[Statement::While(Expr::Integer(5), vec![])],
        );
    }

    #[test]
    fn test_while_loops() {
        do_ok_test(
            "WHILE TRUE\nA\nB\nEND WHILE",
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
                END WHILE
                C
            END WHILE
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
        do_error_test("WHILE TRUE\n", "WHILE without END WHILE");
        do_error_test("WHILE TRUE\nEND", "WHILE without END WHILE");
        do_error_test("WHILE TRUE\nEND\n", "WHILE without END WHILE");

        do_error_test("WHILE ,\nEND WHILE", "No expression in WHILE statement");
    }
}
