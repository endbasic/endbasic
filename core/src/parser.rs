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

use crate::ast::*;
use crate::lexer::{Lexer, PeekableLexer, Token, TokenSpan};
use crate::reader::LineCol;
use std::cmp::Ordering;
use std::io;

/// Parser errors.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Bad syntax in the input program.
    #[error("{}: {}", .0, .1)]
    Bad(LineCol, String),

    /// I/O error while parsing the input program.
    #[error("{0}: {1}")]
    Io(LineCol, io::Error),
}

impl From<(LineCol, io::Error)> for Error {
    fn from(value: (LineCol, io::Error)) -> Self {
        Self::Io(value.0, value.1)
    }
}

/// Result for parser return values.
pub type Result<T> = std::result::Result<T, Error>;

/// Transforms a `VarRef` into an unannotated name.
///
/// This is only valid for references that have no annotations in them.
fn vref_to_unannotated_string(vref: VarRef, pos: LineCol) -> Result<String> {
    if vref.ref_type().is_some() {
        return Err(Error::Bad(pos, format!("Type annotation not allowed in {}", vref)));
    }
    Ok(vref.take_name())
}

/// Converts a collection of `ArgSpan`s passed to a function or array reference to a collection
/// of expressions with proper validation.
pub(crate) fn argspans_to_exprs(spans: Vec<ArgSpan>) -> Vec<Expr> {
    let nargs = spans.len();
    let mut exprs = Vec::with_capacity(spans.len());
    for (i, span) in spans.into_iter().enumerate() {
        debug_assert!(
            (span.sep == ArgSep::End || i < nargs - 1)
                || (span.sep != ArgSep::End || i == nargs - 1)
        );
        match span.expr {
            Some(expr) => exprs.push(expr),
            None => unreachable!(),
        }
    }
    exprs
}

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
    Power,
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

    ShiftLeft,
    ShiftRight,
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
            Token::Exponent => ExprOp::Power,
            Token::And => ExprOp::And,
            Token::Or => ExprOp::Or,
            Token::Xor => ExprOp::Xor,
            Token::ShiftLeft => ExprOp::ShiftLeft,
            Token::ShiftRight => ExprOp::ShiftRight,
            Token::Minus => panic!("Ambiguous token; cannot derive ExprOp"),
            _ => panic!("Called on an non-operator"),
        }
    }

    /// Returns the priority of this operator.  The specific number's meaning is only valid when
    /// comparing it against other calls to this function.  Higher number imply higher priority.
    fn priority(&self) -> i8 {
        match self {
            ExprOp::LeftParen => 6,
            ExprOp::Power => 6,

            ExprOp::Negate => 5,
            ExprOp::Not => 5,

            ExprOp::Multiply => 4,
            ExprOp::Divide => 4,
            ExprOp::Modulo => 4,

            ExprOp::Add => 3,
            ExprOp::Subtract => 3,

            ExprOp::ShiftLeft => 2,
            ExprOp::ShiftRight => 2,

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
}

/// Wrapper over an `ExprOp` to extend it with its position.
struct ExprOpSpan {
    /// The wrapped expression operation.
    op: ExprOp,

    /// The position where the operation appears in the input.
    pos: LineCol,
}

impl ExprOpSpan {
    /// Creates a new span from its parts.
    fn new(op: ExprOp, pos: LineCol) -> Self {
        Self { op, pos }
    }

    /// Pops operands from the `expr` stack, applies this operation, and pushes the result back.
    fn apply(&self, exprs: &mut Vec<Expr>) -> Result<()> {
        fn apply1(
            exprs: &mut Vec<Expr>,
            pos: LineCol,
            f: fn(Box<UnaryOpSpan>) -> Expr,
        ) -> Result<()> {
            if exprs.is_empty() {
                return Err(Error::Bad(pos, "Not enough values to apply operator".to_owned()));
            }
            let expr = exprs.pop().unwrap();
            exprs.push(f(Box::from(UnaryOpSpan { expr, pos })));
            Ok(())
        }

        fn apply2(
            exprs: &mut Vec<Expr>,
            pos: LineCol,
            f: fn(Box<BinaryOpSpan>) -> Expr,
        ) -> Result<()> {
            if exprs.len() < 2 {
                return Err(Error::Bad(pos, "Not enough values to apply operator".to_owned()));
            }
            let rhs = exprs.pop().unwrap();
            let lhs = exprs.pop().unwrap();
            exprs.push(f(Box::from(BinaryOpSpan { lhs, rhs, pos })));
            Ok(())
        }

        match self.op {
            ExprOp::Add => apply2(exprs, self.pos, Expr::Add),
            ExprOp::Subtract => apply2(exprs, self.pos, Expr::Subtract),
            ExprOp::Multiply => apply2(exprs, self.pos, Expr::Multiply),
            ExprOp::Divide => apply2(exprs, self.pos, Expr::Divide),
            ExprOp::Modulo => apply2(exprs, self.pos, Expr::Modulo),
            ExprOp::Power => apply2(exprs, self.pos, Expr::Power),

            ExprOp::Equal => apply2(exprs, self.pos, Expr::Equal),
            ExprOp::NotEqual => apply2(exprs, self.pos, Expr::NotEqual),
            ExprOp::Less => apply2(exprs, self.pos, Expr::Less),
            ExprOp::LessEqual => apply2(exprs, self.pos, Expr::LessEqual),
            ExprOp::Greater => apply2(exprs, self.pos, Expr::Greater),
            ExprOp::GreaterEqual => apply2(exprs, self.pos, Expr::GreaterEqual),

            ExprOp::And => apply2(exprs, self.pos, Expr::And),
            ExprOp::Or => apply2(exprs, self.pos, Expr::Or),
            ExprOp::Xor => apply2(exprs, self.pos, Expr::Xor),

            ExprOp::ShiftLeft => apply2(exprs, self.pos, Expr::ShiftLeft),
            ExprOp::ShiftRight => apply2(exprs, self.pos, Expr::ShiftRight),

            ExprOp::Negate => apply1(exprs, self.pos, Expr::Negate),
            ExprOp::Not => apply1(exprs, self.pos, Expr::Not),

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
    fn from(input: &'a mut dyn io::Read) -> Self {
        Self { lexer: Lexer::from(input).peekable() }
    }

    /// Expects the peeked token to be `t` and consumes it.  Otherwise, leaves the token in the
    /// stream and fails with error `err`.
    fn expect_and_consume<E: Into<String>>(&mut self, t: Token, err: E) -> Result<TokenSpan> {
        let peeked = self.lexer.peek()?;
        if peeked.token != t {
            return Err(Error::Bad(peeked.pos, err.into()));
        }
        Ok(self.lexer.consume_peeked())
    }

    /// Expects the peeked token to be `t` and consumes it.  Otherwise, leaves the token in the
    /// stream and fails with error `err`, pointing at `pos` as the original location of the
    /// problem.
    fn expect_and_consume_with_pos<E: Into<String>>(
        &mut self,
        t: Token,
        pos: LineCol,
        err: E,
    ) -> Result<()> {
        let peeked = self.lexer.peek()?;
        if peeked.token != t {
            return Err(Error::Bad(pos, err.into()));
        }
        self.lexer.consume_peeked();
        Ok(())
    }

    /// Reads statements until the `delim` keyword is found.  The delimiter is not consumed.
    fn parse_until(&mut self, delim: Token) -> Result<Vec<Statement>> {
        let mut stmts = vec![];
        loop {
            let peeked = self.lexer.peek()?;
            if peeked.token == delim {
                break;
            } else if peeked.token == Token::Eol {
                self.lexer.consume_peeked();
                continue;
            }
            match self.parse_one_safe()? {
                Some(stmt) => stmts.push(stmt),
                None => break,
            }
        }
        Ok(stmts)
    }

    /// Parses an assignment for the variable reference `vref` already read.
    fn parse_assignment(&mut self, vref: VarRef, vref_pos: LineCol) -> Result<Statement> {
        let expr = self.parse_required_expr("Missing expression in assignment")?;

        let next = self.lexer.peek()?;
        match &next.token {
            Token::Eof | Token::Eol | Token::Else => (),
            t => return Err(Error::Bad(next.pos, format!("Unexpected {} in assignment", t))),
        }
        Ok(Statement::Assignment(AssignmentSpan { vref, vref_pos, expr }))
    }

    /// Parses an assignment to the array `varref` with `subscripts`, both of which have already
    /// been read.
    fn parse_array_assignment(
        &mut self,
        vref: VarRef,
        vref_pos: LineCol,
        subscripts: Vec<Expr>,
    ) -> Result<Statement> {
        let expr = self.parse_required_expr("Missing expression in array assignment")?;

        let next = self.lexer.peek()?;
        match &next.token {
            Token::Eof | Token::Eol | Token::Else => (),
            t => return Err(Error::Bad(next.pos, format!("Unexpected {} in array assignment", t))),
        }
        Ok(Statement::ArrayAssignment(ArrayAssignmentSpan { vref, vref_pos, subscripts, expr }))
    }

    /// Parses a builtin call (things of the form `INPUT a`).
    fn parse_builtin_call(
        &mut self,
        vref: VarRef,
        vref_pos: LineCol,
        mut first: Option<Expr>,
    ) -> Result<Statement> {
        let mut name = vref_to_unannotated_string(vref, vref_pos)?;
        name.make_ascii_uppercase();

        let mut args = vec![];
        loop {
            let expr = self.parse_expr(first.take())?;

            let peeked = self.lexer.peek()?;
            match peeked.token {
                Token::Eof | Token::Eol | Token::Else => {
                    if expr.is_some() || !args.is_empty() {
                        args.push(ArgSpan { expr, sep: ArgSep::End, sep_pos: peeked.pos });
                    }
                    break;
                }
                Token::Semicolon => {
                    let peeked = self.lexer.consume_peeked();
                    args.push(ArgSpan { expr, sep: ArgSep::Short, sep_pos: peeked.pos });
                }
                Token::Comma => {
                    let peeked = self.lexer.consume_peeked();
                    args.push(ArgSpan { expr, sep: ArgSep::Long, sep_pos: peeked.pos });
                }
                Token::As => {
                    let peeked = self.lexer.consume_peeked();
                    args.push(ArgSpan { expr, sep: ArgSep::As, sep_pos: peeked.pos });
                }
                _ => {
                    return Err(Error::Bad(
                        peeked.pos,
                        "Expected comma, semicolon, or end of statement".to_owned(),
                    ))
                }
            }
        }
        Ok(Statement::Call(CallSpan { vref: VarRef::new(name, None), vref_pos, args }))
    }

    /// Starts processing either an array reference or a builtin call and disambiguates between the
    /// two.
    fn parse_array_or_builtin_call(
        &mut self,
        vref: VarRef,
        vref_pos: LineCol,
    ) -> Result<Statement> {
        match self.lexer.peek()?.token {
            Token::LeftParen => {
                let left_paren = self.lexer.consume_peeked();
                let spans = self.parse_comma_separated_exprs()?;
                let mut exprs = spans.into_iter().map(|span| span.expr.unwrap()).collect();
                match self.lexer.peek()?.token {
                    Token::Equal => {
                        self.lexer.consume_peeked();
                        self.parse_array_assignment(vref, vref_pos, exprs)
                    }
                    _ => {
                        if exprs.len() != 1 {
                            return Err(Error::Bad(
                                left_paren.pos,
                                "Expected expression".to_owned(),
                            ));
                        }
                        self.parse_builtin_call(vref, vref_pos, Some(exprs.remove(0)))
                    }
                }
            }
            _ => self.parse_builtin_call(vref, vref_pos, None),
        }
    }

    /// Parses the type name of an `AS` type definition.
    ///
    /// The `AS` token has already been consumed, so all this does is read a literal type name and
    /// convert it to the corresponding expression type.
    fn parse_as_type(&mut self) -> Result<(ExprType, LineCol)> {
        let token_span = self.lexer.read()?;
        match token_span.token {
            Token::BooleanName => Ok((ExprType::Boolean, token_span.pos)),
            Token::DoubleName => Ok((ExprType::Double, token_span.pos)),
            Token::IntegerName => Ok((ExprType::Integer, token_span.pos)),
            Token::TextName => Ok((ExprType::Text, token_span.pos)),
            t => Err(Error::Bad(
                token_span.pos,
                format!("Invalid type name {} in AS type definition", t),
            )),
        }
    }

    /// Parses a `DATA` statement.
    fn parse_data(&mut self) -> Result<Statement> {
        let mut values = vec![];
        loop {
            let peeked = self.lexer.peek()?;
            match peeked.token {
                Token::Eof | Token::Eol | Token::Else => {
                    values.push(None);
                    break;
                }
                _ => (),
            }

            let token_span = self.lexer.read()?;
            match token_span.token {
                Token::Boolean(b) => values.push(Some(Value::Boolean(b))),
                Token::Double(d) => values.push(Some(Value::Double(d))),
                Token::Integer(i) => values.push(Some(Value::Integer(i))),
                Token::Text(t) => values.push(Some(Value::Text(t))),

                Token::Minus => {
                    let token_span = self.lexer.read()?;
                    match token_span.token {
                        Token::Double(d) => values.push(Some(Value::Double(-d))),
                        Token::Integer(i) => values.push(Some(Value::Integer(-i))),
                        _ => {
                            return Err(Error::Bad(
                                token_span.pos,
                                "Expected number after -".to_owned(),
                            ))
                        }
                    }
                }

                Token::Eof | Token::Eol | Token::Else => {
                    panic!("Should not be consumed here; handled above")
                }

                Token::Comma => {
                    values.push(None);
                    continue;
                }

                t => {
                    return Err(Error::Bad(
                        token_span.pos,
                        format!("Unexpected {} in DATA statement", t),
                    ))
                }
            }

            let peeked = self.lexer.peek()?;
            match &peeked.token {
                Token::Eof | Token::Eol | Token::Else => {
                    break;
                }

                Token::Comma => {
                    self.lexer.consume_peeked();
                }

                t => {
                    return Err(Error::Bad(
                        peeked.pos,
                        format!("Expected comma after datum but found {}", t),
                    ))
                }
            }
        }
        Ok(Statement::Data(DataSpan { values }))
    }

    /// Parses the `AS typename` clause of a `DIM` statement.  The caller has already consumed the
    /// `AS` token.
    fn parse_dim_as(&mut self) -> Result<(ExprType, LineCol)> {
        let peeked = self.lexer.peek()?;
        let (vtype, vtype_pos) = match peeked.token {
            Token::Eof | Token::Eol => (ExprType::Integer, peeked.pos),
            Token::As => {
                self.lexer.consume_peeked();
                self.parse_as_type()?
            }
            _ => return Err(Error::Bad(peeked.pos, "Expected AS or end of statement".to_owned())),
        };

        let next = self.lexer.peek()?;
        match &next.token {
            Token::Eof | Token::Eol => (),
            t => return Err(Error::Bad(next.pos, format!("Unexpected {} in DIM statement", t))),
        }

        Ok((vtype, vtype_pos))
    }

    /// Parses a `DIM` statement.
    fn parse_dim(&mut self) -> Result<Statement> {
        let peeked = self.lexer.peek()?;
        let mut shared = false;
        if peeked.token == Token::Shared {
            self.lexer.consume_peeked();
            shared = true;
        }

        let token_span = self.lexer.read()?;
        let vref = match token_span.token {
            Token::Symbol(vref) => vref,
            _ => {
                return Err(Error::Bad(
                    token_span.pos,
                    "Expected variable name after DIM".to_owned(),
                ))
            }
        };
        let name = vref_to_unannotated_string(vref, token_span.pos)?;
        let name_pos = token_span.pos;

        match self.lexer.peek()?.token {
            Token::LeftParen => {
                let peeked = self.lexer.consume_peeked();
                let dimensions = self.parse_comma_separated_exprs()?;
                if dimensions.is_empty() {
                    return Err(Error::Bad(
                        peeked.pos,
                        "Arrays require at least one dimension".to_owned(),
                    ));
                }
                let (subtype, subtype_pos) = self.parse_dim_as()?;
                Ok(Statement::DimArray(DimArraySpan {
                    name,
                    name_pos,
                    shared,
                    dimensions: argspans_to_exprs(dimensions),
                    subtype,
                    subtype_pos,
                }))
            }
            _ => {
                let (vtype, vtype_pos) = self.parse_dim_as()?;
                Ok(Statement::Dim(DimSpan { name, name_pos, shared, vtype, vtype_pos }))
            }
        }
    }

    /// Parses the `UNTIL` or `WHILE` clause of a `DO` loop.
    ///
    /// `part` is a string indicating where the clause is expected (either after `DO` or after
    /// `LOOP`).
    ///
    /// Returns the guard expression and a boolean indicating if this is an `UNTIL` clause.
    fn parse_do_guard(&mut self, part: &str) -> Result<Option<(Expr, bool)>> {
        let peeked = self.lexer.peek()?;
        match peeked.token {
            Token::Until => {
                self.lexer.consume_peeked();
                let expr = self.parse_required_expr("No expression in UNTIL clause")?;
                Ok(Some((expr, true)))
            }
            Token::While => {
                self.lexer.consume_peeked();
                let expr = self.parse_required_expr("No expression in WHILE clause")?;
                Ok(Some((expr, false)))
            }
            Token::Eof | Token::Eol => Ok(None),
            _ => {
                let token_span = self.lexer.consume_peeked();
                Err(Error::Bad(
                    token_span.pos,
                    format!("Expecting newline, UNTIL or WHILE after {}", part),
                ))
            }
        }
    }

    /// Parses a `DO` statement.
    fn parse_do(&mut self, do_pos: LineCol) -> Result<Statement> {
        let pre_guard = self.parse_do_guard("DO")?;
        self.expect_and_consume(Token::Eol, "Expecting newline after DO")?;

        let stmts = self.parse_until(Token::Loop)?;
        self.expect_and_consume_with_pos(Token::Loop, do_pos, "DO without LOOP")?;

        let post_guard = self.parse_do_guard("LOOP")?;

        let guard = match (pre_guard, post_guard) {
            (None, None) => DoGuard::Infinite,
            (Some((guard, true)), None) => DoGuard::PreUntil(guard),
            (Some((guard, false)), None) => DoGuard::PreWhile(guard),
            (None, Some((guard, true))) => DoGuard::PostUntil(guard),
            (None, Some((guard, false))) => DoGuard::PostWhile(guard),
            (Some(_), Some(_)) => {
                return Err(Error::Bad(
                    do_pos,
                    "DO loop cannot have pre and post guards at the same time".to_owned(),
                ))
            }
        };

        Ok(Statement::Do(DoSpan { guard, body: stmts }))
    }

    /// Advances until the next statement after failing to parse a `DO` statement.
    fn reset_do(&mut self) -> Result<()> {
        loop {
            match self.lexer.peek()?.token {
                Token::Eof => break,
                Token::Loop => {
                    self.lexer.consume_peeked();
                    loop {
                        match self.lexer.peek()?.token {
                            Token::Eof | Token::Eol => break,
                            _ => {
                                self.lexer.consume_peeked();
                            }
                        }
                    }
                    break;
                }
                _ => {
                    self.lexer.consume_peeked();
                }
            }
        }
        self.reset()
    }

    /// Parses a potential `END` statement but, if this corresponds to a statement terminator such
    /// as `END IF`, returns the token that followed `END`.
    fn maybe_parse_end(&mut self) -> Result<std::result::Result<Statement, Token>> {
        match self.lexer.peek()?.token {
            Token::Function => Ok(Err(Token::Function)),
            Token::If => Ok(Err(Token::If)),
            Token::Select => Ok(Err(Token::Select)),
            Token::Sub => Ok(Err(Token::Sub)),
            _ => {
                let code = self.parse_expr(None)?;
                Ok(Ok(Statement::End(EndSpan { code })))
            }
        }
    }

    /// Parses an `END` statement.
    fn parse_end(&mut self, pos: LineCol) -> Result<Statement> {
        match self.maybe_parse_end()? {
            Ok(stmt) => Ok(stmt),
            Err(token) => Err(Error::Bad(pos, format!("END {} without {}", token, token))),
        }
    }

    /// Parses an `EXIT` statement.
    fn parse_exit(&mut self, pos: LineCol) -> Result<Statement> {
        let peeked = self.lexer.peek()?;
        let stmt = match peeked.token {
            Token::Do => Statement::ExitDo(ExitSpan { pos }),
            Token::For => Statement::ExitFor(ExitSpan { pos }),
            _ => return Err(Error::Bad(peeked.pos, "Expecting DO or FOR after EXIT".to_owned())),
        };
        self.lexer.consume_peeked();
        Ok(stmt)
    }

    /// Parses a variable list of comma-separated expressions.  The caller must have consumed the
    /// open parenthesis and we stop processing when we encounter the terminating parenthesis (and
    /// consume it).  We expect at least one expression.
    fn parse_comma_separated_exprs(&mut self) -> Result<Vec<ArgSpan>> {
        let mut spans = vec![];

        // The first expression is optional to support calls to functions without arguments.
        let mut is_first = true;
        let mut prev_expr = self.parse_expr(None)?;

        loop {
            let peeked = self.lexer.peek()?;
            let pos = peeked.pos;
            match &peeked.token {
                Token::RightParen => {
                    self.lexer.consume_peeked();

                    if let Some(expr) = prev_expr.take() {
                        spans.push(ArgSpan { expr: Some(expr), sep: ArgSep::End, sep_pos: pos });
                    } else {
                        if !is_first {
                            return Err(Error::Bad(pos, "Missing expression".to_owned()));
                        }
                    }

                    break;
                }
                Token::Comma => {
                    self.lexer.consume_peeked();

                    if let Some(expr) = prev_expr.take() {
                        // The first expression is optional to support calls to functions without
                        // arguments.
                        spans.push(ArgSpan { expr: Some(expr), sep: ArgSep::Long, sep_pos: pos });
                    } else {
                        return Err(Error::Bad(pos, "Missing expression".to_owned()));
                    }

                    prev_expr = self.parse_expr(None)?;
                }
                t => return Err(Error::Bad(pos, format!("Unexpected {}", t))),
            }

            is_first = false;
        }

        Ok(spans)
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
        let mut op_spans: Vec<ExprOpSpan> = vec![];

        let mut need_operand = true; // Also tracks whether an upcoming minus is unary.
        if let Some(e) = first {
            exprs.push(e);
            need_operand = false;
        }

        loop {
            let mut handle_operand = |e, pos| {
                if !need_operand {
                    return Err(Error::Bad(pos, "Unexpected value in expression".to_owned()));
                }
                need_operand = false;
                exprs.push(e);
                Ok(())
            };

            // Stop processing if we encounter an expression separator, but don't consume it because
            // the caller needs to have access to it.
            match self.lexer.peek()?.token {
                Token::Eof
                | Token::Eol
                | Token::As
                | Token::Comma
                | Token::Else
                | Token::Semicolon
                | Token::Then
                | Token::To
                | Token::Step => break,
                Token::RightParen => {
                    if !op_spans.iter().any(|eos| eos.op == ExprOp::LeftParen) {
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

            let ts = self.lexer.consume_peeked();
            match ts.token {
                Token::Boolean(value) => {
                    handle_operand(Expr::Boolean(BooleanSpan { value, pos: ts.pos }), ts.pos)?
                }
                Token::Double(value) => {
                    handle_operand(Expr::Double(DoubleSpan { value, pos: ts.pos }), ts.pos)?
                }
                Token::Integer(value) => {
                    handle_operand(Expr::Integer(IntegerSpan { value, pos: ts.pos }), ts.pos)?
                }
                Token::Text(value) => {
                    handle_operand(Expr::Text(TextSpan { value, pos: ts.pos }), ts.pos)?
                }
                Token::Symbol(vref) => {
                    handle_operand(Expr::Symbol(SymbolSpan { vref, pos: ts.pos }), ts.pos)?
                }

                Token::LeftParen => {
                    // If the last operand we encountered was a symbol, collapse it and the left
                    // parenthesis into the beginning of a function call.
                    match exprs.pop() {
                        Some(Expr::Symbol(span)) => {
                            if !need_operand {
                                exprs.push(Expr::Call(CallSpan {
                                    vref: span.vref,
                                    vref_pos: span.pos,
                                    args: self.parse_comma_separated_exprs()?,
                                }));
                                need_operand = false;
                            } else {
                                // We popped out the last expression to see if it this left
                                // parenthesis started a function call... but it did not (it is a
                                // symbol following a parenthesis) so put both the expression and
                                // the token back.
                                op_spans.push(ExprOpSpan::new(ExprOp::LeftParen, ts.pos));
                                exprs.push(Expr::Symbol(span));
                                need_operand = true;
                            }
                        }
                        e => {
                            if let Some(e) = e {
                                // We popped out the last expression to see if this left
                                // parenthesis started a function call... but if it didn't, we have
                                // to put the expression back.
                                exprs.push(e);
                            }
                            if !need_operand {
                                return Err(Error::Bad(
                                    ts.pos,
                                    format!("Unexpected {} in expression", ts.token),
                                ));
                            }
                            op_spans.push(ExprOpSpan::new(ExprOp::LeftParen, ts.pos));
                            need_operand = true;
                        }
                    };
                }
                Token::RightParen => {
                    let mut found = false;
                    while let Some(eos) = op_spans.pop() {
                        eos.apply(&mut exprs)?;
                        if eos.op == ExprOp::LeftParen {
                            found = true;
                            break;
                        }
                    }
                    assert!(found, "Unbalanced parenthesis should have been handled above");
                    need_operand = false;
                }

                Token::Not => {
                    op_spans.push(ExprOpSpan::new(ExprOp::Not, ts.pos));
                    need_operand = true;
                }
                Token::Minus => {
                    let op;
                    if need_operand {
                        op = ExprOp::Negate;
                    } else {
                        op = ExprOp::Subtract;
                        while let Some(eos2) = op_spans.last() {
                            if eos2.op == ExprOp::LeftParen || eos2.op.priority() < op.priority() {
                                break;
                            }
                            let eos2 = op_spans.pop().unwrap();
                            eos2.apply(&mut exprs)?;
                        }
                    }
                    op_spans.push(ExprOpSpan::new(op, ts.pos));
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
                | Token::Exponent
                | Token::And
                | Token::Or
                | Token::Xor
                | Token::ShiftLeft
                | Token::ShiftRight => {
                    let op = ExprOp::from(ts.token);
                    while let Some(eos2) = op_spans.last() {
                        if eos2.op == ExprOp::LeftParen || eos2.op.priority() < op.priority() {
                            break;
                        }
                        let eos2 = op_spans.pop().unwrap();
                        eos2.apply(&mut exprs)?;
                    }
                    op_spans.push(ExprOpSpan::new(op, ts.pos));
                    need_operand = true;
                }

                Token::Bad(e) => return Err(Error::Bad(ts.pos, e)),

                Token::Eof
                | Token::Eol
                | Token::As
                | Token::Comma
                | Token::Else
                | Token::Semicolon
                | Token::Then
                | Token::To
                | Token::Step => {
                    panic!("Field separators handled above")
                }

                Token::BooleanName
                | Token::Case
                | Token::Data
                | Token::Do
                | Token::Dim
                | Token::DoubleName
                | Token::Elseif
                | Token::End
                | Token::Error
                | Token::Exit
                | Token::For
                | Token::Function
                | Token::Gosub
                | Token::Goto
                | Token::If
                | Token::Is
                | Token::IntegerName
                | Token::Label(_)
                | Token::Loop
                | Token::Next
                | Token::On
                | Token::Resume
                | Token::Return
                | Token::Select
                | Token::Shared
                | Token::Sub
                | Token::TextName
                | Token::Until
                | Token::Wend
                | Token::While => {
                    return Err(Error::Bad(ts.pos, "Unexpected keyword in expression".to_owned()));
                }
            };
        }

        while let Some(eos) = op_spans.pop() {
            match eos.op {
                ExprOp::LeftParen => {
                    return Err(Error::Bad(eos.pos, "Unbalanced parenthesis".to_owned()))
                }
                _ => eos.apply(&mut exprs)?,
            }
        }

        if let Some(expr) = exprs.pop() {
            Ok(Some(expr))
        } else {
            Ok(None)
        }
    }

    /// Wrapper over `parse_expr` that requires an expression to be present and returns an error
    /// with `msg` otherwise.
    fn parse_required_expr(&mut self, msg: &'static str) -> Result<Expr> {
        let next_pos = self.lexer.peek()?.pos;
        match self.parse_expr(None)? {
            Some(expr) => Ok(expr),
            None => Err(Error::Bad(next_pos, msg.to_owned())),
        }
    }

    /// Parses a `GOSUB` statement.
    fn parse_gosub(&mut self) -> Result<Statement> {
        let token_span = self.lexer.read()?;
        match token_span.token {
            Token::Integer(i) => {
                let target = format!("{}", i);
                Ok(Statement::Gosub(GotoSpan { target, target_pos: token_span.pos }))
            }
            Token::Label(target) => {
                Ok(Statement::Gosub(GotoSpan { target, target_pos: token_span.pos }))
            }
            _ => Err(Error::Bad(token_span.pos, "Expected label name after GOSUB".to_owned())),
        }
    }

    /// Parses a `GOTO` statement.
    fn parse_goto(&mut self) -> Result<Statement> {
        let token_span = self.lexer.read()?;
        match token_span.token {
            Token::Integer(i) => {
                let target = format!("{}", i);
                Ok(Statement::Goto(GotoSpan { target, target_pos: token_span.pos }))
            }
            Token::Label(target) => {
                Ok(Statement::Goto(GotoSpan { target, target_pos: token_span.pos }))
            }
            _ => Err(Error::Bad(token_span.pos, "Expected label name after GOTO".to_owned())),
        }
    }

    /// Parses the branches of a uniline `IF` statement.
    fn parse_if_uniline(&mut self, branches: &mut Vec<IfBranchSpan>) -> Result<()> {
        debug_assert!(!branches.is_empty(), "Caller must populate the guard of the first branch");

        let mut has_else = false;
        let peeked = self.lexer.peek()?;
        match peeked.token {
            Token::Else => has_else = true,
            _ => {
                let stmt = self
                    .parse_uniline()?
                    .expect("The caller already checked for a non-empty token");
                branches[0].body.push(stmt);
            }
        }

        let peeked = self.lexer.peek()?;
        has_else |= peeked.token == Token::Else;

        if has_else {
            let else_span = self.lexer.consume_peeked();
            let expr = Expr::Boolean(BooleanSpan { value: true, pos: else_span.pos });
            branches.push(IfBranchSpan { guard: expr, body: vec![] });
            if let Some(stmt) = self.parse_uniline()? {
                branches[1].body.push(stmt);
            }
        }

        Ok(())
    }

    /// Parses the branches of a multiline `IF` statement.
    fn parse_if_multiline(
        &mut self,
        if_pos: LineCol,
        branches: &mut Vec<IfBranchSpan>,
    ) -> Result<()> {
        debug_assert!(!branches.is_empty(), "Caller must populate the guard of the first branch");

        let mut i = 0;
        let mut last = false;
        loop {
            let peeked = self.lexer.peek()?;
            match peeked.token {
                Token::Eol => {
                    self.lexer.consume_peeked();
                }

                Token::Elseif => {
                    if last {
                        return Err(Error::Bad(
                            peeked.pos,
                            "Unexpected ELSEIF after ELSE".to_owned(),
                        ));
                    }

                    self.lexer.consume_peeked();
                    let expr = self.parse_required_expr("No expression in ELSEIF statement")?;
                    self.expect_and_consume(Token::Then, "No THEN in ELSEIF statement")?;
                    self.expect_and_consume(Token::Eol, "Expecting newline after THEN")?;
                    branches.push(IfBranchSpan { guard: expr, body: vec![] });
                    i += 1;
                }

                Token::Else => {
                    if last {
                        return Err(Error::Bad(peeked.pos, "Duplicate ELSE after ELSE".to_owned()));
                    }

                    let else_span = self.lexer.consume_peeked();
                    self.expect_and_consume(Token::Eol, "Expecting newline after ELSE")?;

                    let expr = Expr::Boolean(BooleanSpan { value: true, pos: else_span.pos });
                    branches.push(IfBranchSpan { guard: expr, body: vec![] });
                    i += 1;

                    last = true;
                }

                Token::End => {
                    let token_span = self.lexer.consume_peeked();
                    match self.maybe_parse_end()? {
                        Ok(stmt) => {
                            branches[i].body.push(stmt);
                        }
                        Err(Token::If) => {
                            break;
                        }
                        Err(token) => {
                            return Err(Error::Bad(
                                token_span.pos,
                                format!("END {} without {}", token, token),
                            ));
                        }
                    }
                }

                _ => match self.parse_one_safe()? {
                    Some(stmt) => {
                        branches[i].body.push(stmt);
                    }
                    None => {
                        break;
                    }
                },
            }
        }

        self.expect_and_consume_with_pos(Token::If, if_pos, "IF without END IF")
    }

    /// Parses an `IF` statement.
    fn parse_if(&mut self, if_pos: LineCol) -> Result<Statement> {
        let expr = self.parse_required_expr("No expression in IF statement")?;
        self.expect_and_consume(Token::Then, "No THEN in IF statement")?;

        let mut branches = vec![IfBranchSpan { guard: expr, body: vec![] }];

        let peeked = self.lexer.peek()?;
        match peeked.token {
            Token::Eol | Token::Eof => self.parse_if_multiline(if_pos, &mut branches)?,
            _ => self.parse_if_uniline(&mut branches)?,
        }

        Ok(Statement::If(IfSpan { branches }))
    }

    /// Advances until the next statement after failing to parse an `IF` statement.
    fn reset_if(&mut self, if_pos: LineCol) -> Result<()> {
        loop {
            match self.lexer.peek()?.token {
                Token::Eof => break,
                Token::End => {
                    self.lexer.consume_peeked();
                    self.expect_and_consume_with_pos(Token::If, if_pos, "IF without END IF")?;
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
    ///
    /// Returns the step as an expression, an `Ordering` value representing how the step value
    /// compares to zero, and whether the step is a double or not.
    fn parse_step(&mut self) -> Result<(Expr, Ordering, bool)> {
        let peeked = self.lexer.peek()?;
        match peeked.token {
            Token::Step => self.lexer.consume_peeked(),
            _ => {
                // The position we return here for the step isn't truly the right value, but given
                // that we know the hardcoded step of 1 is valid, the caller will not error out and
                // will not print the slightly invalid position.
                return Ok((
                    Expr::Integer(IntegerSpan { value: 1, pos: peeked.pos }),
                    Ordering::Greater,
                    false,
                ));
            }
        };

        let peeked = self.lexer.peek()?;
        match peeked.token {
            Token::Double(d) => {
                let peeked = self.lexer.consume_peeked();
                let sign = if d == 0.0 { Ordering::Equal } else { Ordering::Greater };
                Ok((Expr::Double(DoubleSpan { value: d, pos: peeked.pos }), sign, true))
            }
            Token::Integer(i) => {
                let peeked = self.lexer.consume_peeked();
                Ok((Expr::Integer(IntegerSpan { value: i, pos: peeked.pos }), i.cmp(&0), false))
            }
            Token::Minus => {
                self.lexer.consume_peeked();
                let peeked = self.lexer.peek()?;
                match peeked.token {
                    Token::Double(d) => {
                        let peeked = self.lexer.consume_peeked();
                        let sign = if d == 0.0 { Ordering::Equal } else { Ordering::Less };
                        Ok((Expr::Double(DoubleSpan { value: -d, pos: peeked.pos }), sign, true))
                    }
                    Token::Integer(i) => {
                        let peeked = self.lexer.consume_peeked();
                        Ok((
                            Expr::Integer(IntegerSpan { value: -i, pos: peeked.pos }),
                            (-i).cmp(&0),
                            false,
                        ))
                    }
                    _ => Err(Error::Bad(peeked.pos, "STEP needs a literal number".to_owned())),
                }
            }
            _ => Err(Error::Bad(peeked.pos, "STEP needs a literal number".to_owned())),
        }
    }

    /// Parses a `FOR` statement.
    fn parse_for(&mut self, for_pos: LineCol) -> Result<Statement> {
        let token_span = self.lexer.read()?;
        let iterator = match token_span.token {
            Token::Symbol(iterator) => match iterator.ref_type() {
                None | Some(ExprType::Double) | Some(ExprType::Integer) => iterator,
                _ => {
                    return Err(Error::Bad(
                        token_span.pos,
                        "Iterator name in FOR statement must be a numeric reference".to_owned(),
                    ))
                }
            },
            _ => {
                return Err(Error::Bad(
                    token_span.pos,
                    "No iterator name in FOR statement".to_owned(),
                ))
            }
        };
        let iterator_pos = token_span.pos;

        self.expect_and_consume(Token::Equal, "No equal sign in FOR statement")?;
        let start = self.parse_required_expr("No start expression in FOR statement")?;

        let to_span = self.expect_and_consume(Token::To, "No TO in FOR statement")?;
        let end = self.parse_required_expr("No end expression in FOR statement")?;

        let (step, step_sign, iter_double) = self.parse_step()?;
        let end_condition = match step_sign {
            Ordering::Greater => Expr::LessEqual(Box::from(BinaryOpSpan {
                lhs: Expr::Symbol(SymbolSpan { vref: iterator.clone(), pos: iterator_pos }),
                rhs: end,
                pos: to_span.pos,
            })),
            Ordering::Less => Expr::GreaterEqual(Box::from(BinaryOpSpan {
                lhs: Expr::Symbol(SymbolSpan { vref: iterator.clone(), pos: iterator_pos }),
                rhs: end,
                pos: to_span.pos,
            })),
            Ordering::Equal => {
                return Err(Error::Bad(
                    step.start_pos(),
                    "Infinite FOR loop; STEP cannot be 0".to_owned(),
                ))
            }
        };

        let next_value = Expr::Add(Box::from(BinaryOpSpan {
            lhs: Expr::Symbol(SymbolSpan { vref: iterator.clone(), pos: iterator_pos }),
            rhs: step,
            pos: to_span.pos,
        }));

        self.expect_and_consume(Token::Eol, "Expecting newline after FOR")?;

        let stmts = self.parse_until(Token::Next)?;
        self.expect_and_consume_with_pos(Token::Next, for_pos, "FOR without NEXT")?;

        Ok(Statement::For(ForSpan {
            iter: iterator,
            iter_pos: iterator_pos,
            iter_double,
            start,
            end: end_condition,
            next: next_value,
            body: stmts,
        }))
    }

    /// Advances until the next statement after failing to parse a `FOR` statement.
    fn reset_for(&mut self) -> Result<()> {
        loop {
            match self.lexer.peek()?.token {
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

    /// Parses the optional parameter list that may appear after a `FUNCTION` or `SUB` definition,
    /// including the opening and closing parenthesis.
    fn parse_callable_args(&mut self) -> Result<Vec<VarRef>> {
        let mut params = vec![];
        let peeked = self.lexer.peek()?;
        if peeked.token == Token::LeftParen {
            self.lexer.consume_peeked();

            loop {
                let token_span = self.lexer.read()?;
                match token_span.token {
                    Token::Symbol(param) => {
                        let peeked = self.lexer.peek()?;
                        if peeked.token == Token::As {
                            self.lexer.consume_peeked();

                            let name = vref_to_unannotated_string(param, token_span.pos)?;
                            let (vtype, _pos) = self.parse_as_type()?;
                            params.push(VarRef::new(name, Some(vtype)));
                        } else {
                            params.push(param);
                        }
                    }
                    _ => {
                        return Err(Error::Bad(
                            token_span.pos,
                            "Expected a parameter name".to_owned(),
                        ));
                    }
                }

                let token_span = self.lexer.read()?;
                match token_span.token {
                    Token::Comma => (),
                    Token::RightParen => break,
                    _ => {
                        return Err(Error::Bad(
                            token_span.pos,
                            "Expected comma, AS, or end of parameters list".to_owned(),
                        ));
                    }
                }
            }
        }
        Ok(params)
    }

    /// Parses the body of a callable and returns the collection of statements and the position
    /// of the end of the body.
    fn parse_callable_body(
        &mut self,
        start_pos: LineCol,
        exp_token: Token,
    ) -> Result<(Vec<Statement>, LineCol)> {
        debug_assert!(matches!(exp_token, Token::Function | Token::Sub));

        let mut body = vec![];
        let end_pos;
        loop {
            let peeked = self.lexer.peek()?;
            match peeked.token {
                Token::Eof => {
                    end_pos = peeked.pos;
                    break;
                }

                Token::Eol => {
                    self.lexer.consume_peeked();
                }

                Token::Function | Token::Sub => {
                    return Err(Error::Bad(
                        peeked.pos,
                        "Cannot nest FUNCTION or SUB definitions".to_owned(),
                    ));
                }

                Token::End => {
                    let end_span = self.lexer.consume_peeked();
                    match self.maybe_parse_end()? {
                        Ok(stmt) => {
                            body.push(stmt);
                        }
                        Err(token) if token == exp_token => {
                            end_pos = end_span.pos;
                            break;
                        }
                        Err(token) => {
                            return Err(Error::Bad(
                                end_span.pos,
                                format!("END {} without {}", token, token),
                            ));
                        }
                    }
                }

                // TODO(jmmv): Handle `EXIT FUNCTION` or `EXIT SUB`.
                _ => match self.parse_one_safe()? {
                    Some(stmt) => body.push(stmt),
                    None => {
                        return Err(Error::Bad(
                            start_pos,
                            format!("{} without END {}", exp_token, exp_token),
                        ));
                    }
                },
            }
        }

        self.expect_and_consume_with_pos(
            exp_token.clone(),
            start_pos,
            format!("{} without END {}", exp_token, exp_token),
        )?;

        Ok((body, end_pos))
    }

    /// Parses a `FUNCTION` definition.
    fn parse_function(&mut self, function_pos: LineCol) -> Result<Statement> {
        let token_span = self.lexer.read()?;
        let name = match token_span.token {
            Token::Symbol(name) => {
                if name.ref_type().is_none() {
                    VarRef::new(name.take_name(), Some(ExprType::Integer))
                } else {
                    name
                }
            }
            _ => {
                return Err(Error::Bad(
                    token_span.pos,
                    "Expected a function name after FUNCTION".to_owned(),
                ));
            }
        };
        let name_pos = token_span.pos;

        let params = self.parse_callable_args()?;
        self.expect_and_consume(Token::Eol, "Expected newline after FUNCTION name")?;

        let (body, end_pos) = self.parse_callable_body(function_pos, Token::Function)?;

        Ok(Statement::Callable(CallableSpan { name, name_pos, params, body, end_pos }))
    }

    /// Parses a `SUB` definition.
    fn parse_sub(&mut self, sub_pos: LineCol) -> Result<Statement> {
        let token_span = self.lexer.read()?;
        let name = match token_span.token {
            Token::Symbol(name) => {
                if name.ref_type().is_some() {
                    return Err(Error::Bad(
                        token_span.pos,
                        "SUBs cannot return a value so type annotations are not allowed".to_owned(),
                    ));
                }
                name
            }
            _ => {
                return Err(Error::Bad(
                    token_span.pos,
                    "Expected a function name after SUB".to_owned(),
                ));
            }
        };
        let name_pos = token_span.pos;

        let params = self.parse_callable_args()?;
        self.expect_and_consume(Token::Eol, "Expected newline after SUB name")?;

        let (body, end_pos) = self.parse_callable_body(sub_pos, Token::Sub)?;

        Ok(Statement::Callable(CallableSpan { name, name_pos, params, body, end_pos }))
    }

    /// Advances until the next statement after failing to parse a `FUNCTION` or `SUB` definition.
    fn reset_callable(&mut self, exp_token: Token) -> Result<()> {
        loop {
            match self.lexer.peek()?.token {
                Token::Eof => break,
                Token::End => {
                    self.lexer.consume_peeked();

                    let token_span = self.lexer.read()?;
                    if token_span.token == exp_token {
                        break;
                    }
                }
                _ => {
                    self.lexer.consume_peeked();
                }
            }
        }
        self.reset()
    }

    /// Parses an `ON ERROR` statement.  Only `ON` has been consumed so far.
    fn parse_on(&mut self) -> Result<Statement> {
        self.expect_and_consume(Token::Error, "Expected ERROR after ON")?;

        let token_span = self.lexer.read()?;
        match token_span.token {
            Token::Goto => {
                let token_span = self.lexer.read()?;
                match token_span.token {
                    Token::Integer(0) => Ok(Statement::OnError(OnErrorSpan::Reset)),
                    Token::Integer(i) => Ok(Statement::OnError(OnErrorSpan::Goto(GotoSpan {
                        target: format!("{}", i),
                        target_pos: token_span.pos,
                    }))),
                    Token::Label(target) => Ok(Statement::OnError(OnErrorSpan::Goto(GotoSpan {
                        target,
                        target_pos: token_span.pos,
                    }))),
                    _ => Err(Error::Bad(
                        token_span.pos,
                        "Expected label name or 0 after ON ERROR GOTO".to_owned(),
                    )),
                }
            }
            Token::Resume => {
                self.expect_and_consume(Token::Next, "Expected NEXT after ON ERROR RESUME")?;
                Ok(Statement::OnError(OnErrorSpan::ResumeNext))
            }
            _ => {
                Err(Error::Bad(token_span.pos, "Expected GOTO or RESUME after ON ERROR".to_owned()))
            }
        }
    }

    /// Parses the guards after a `CASE` keyword.
    fn parse_case_guards(&mut self) -> Result<Vec<CaseGuardSpan>> {
        let mut guards = vec![];

        loop {
            let peeked = self.lexer.peek()?;
            match peeked.token {
                Token::Else => {
                    let token_span = self.lexer.consume_peeked();

                    if !guards.is_empty() {
                        return Err(Error::Bad(
                            token_span.pos,
                            "CASE ELSE must be on its own".to_owned(),
                        ));
                    }

                    let peeked = self.lexer.peek()?;
                    if peeked.token != Token::Eol && peeked.token != Token::Eof {
                        return Err(Error::Bad(
                            peeked.pos,
                            "Expected newline after CASE ELSE".to_owned(),
                        ));
                    }

                    break;
                }

                Token::Is => {
                    self.lexer.consume_peeked();

                    let token_span = self.lexer.read()?;
                    let rel_op = match token_span.token {
                        Token::Equal => CaseRelOp::Equal,
                        Token::NotEqual => CaseRelOp::NotEqual,
                        Token::Less => CaseRelOp::Less,
                        Token::LessEqual => CaseRelOp::LessEqual,
                        Token::Greater => CaseRelOp::Greater,
                        Token::GreaterEqual => CaseRelOp::GreaterEqual,
                        _ => {
                            return Err(Error::Bad(
                                token_span.pos,
                                "Expected relational operator".to_owned(),
                            ));
                        }
                    };

                    let expr =
                        self.parse_required_expr("Missing expression after relational operator")?;
                    guards.push(CaseGuardSpan::Is(rel_op, expr));
                }

                _ => {
                    let from_expr = self.parse_required_expr("Missing expression in CASE guard")?;

                    let peeked = self.lexer.peek()?;
                    match peeked.token {
                        Token::Eol | Token::Comma => {
                            guards.push(CaseGuardSpan::Is(CaseRelOp::Equal, from_expr));
                        }
                        Token::To => {
                            self.lexer.consume_peeked();
                            let to_expr = self
                                .parse_required_expr("Missing expression after TO in CASE guard")?;
                            guards.push(CaseGuardSpan::To(from_expr, to_expr));
                        }
                        _ => {
                            return Err(Error::Bad(
                                peeked.pos,
                                "Expected comma, newline, or TO after expression".to_owned(),
                            ));
                        }
                    }
                }
            }

            let peeked = self.lexer.peek()?;
            match peeked.token {
                Token::Eol => {
                    break;
                }
                Token::Comma => {
                    self.lexer.consume_peeked();
                }
                _ => {
                    return Err(Error::Bad(
                        peeked.pos,
                        "Expected comma, newline, or TO after expression".to_owned(),
                    ));
                }
            }
        }

        Ok(guards)
    }

    /// Parses a `SELECT` statement.
    fn parse_select(&mut self, select_pos: LineCol) -> Result<Statement> {
        self.expect_and_consume(Token::Case, "Expecting CASE after SELECT")?;

        let expr = self.parse_required_expr("No expression in SELECT CASE statement")?;
        self.expect_and_consume(Token::Eol, "Expecting newline after SELECT CASE")?;

        let mut cases = vec![];

        let mut i = 0;
        let mut last = false;
        let end_pos;
        loop {
            let peeked = self.lexer.peek()?;
            match peeked.token {
                Token::Eof => {
                    end_pos = peeked.pos;
                    break;
                }

                Token::Eol => {
                    self.lexer.consume_peeked();
                }

                Token::Case => {
                    let peeked = self.lexer.consume_peeked();
                    let guards = self.parse_case_guards()?;
                    self.expect_and_consume(Token::Eol, "Expecting newline after CASE")?;

                    let is_last = guards.is_empty();
                    if last {
                        if is_last {
                            return Err(Error::Bad(
                                peeked.pos,
                                "CASE ELSE must be unique".to_owned(),
                            ));
                        } else {
                            return Err(Error::Bad(peeked.pos, "CASE ELSE is not last".to_owned()));
                        }
                    }
                    last |= is_last;

                    cases.push(CaseSpan { guards, body: vec![] });
                    if cases.len() > 1 {
                        i += 1;
                    }
                }

                Token::End => {
                    let end_span = self.lexer.consume_peeked();
                    match self.maybe_parse_end()? {
                        Ok(stmt) => {
                            if cases.is_empty() {
                                return Err(Error::Bad(
                                    end_span.pos,
                                    "Expected CASE after SELECT CASE before any statement"
                                        .to_owned(),
                                ));
                            }

                            cases[i].body.push(stmt);
                        }
                        Err(Token::Select) => {
                            end_pos = end_span.pos;
                            break;
                        }
                        Err(token) => {
                            if cases.is_empty() {
                                return Err(Error::Bad(
                                    end_span.pos,
                                    "Expected CASE after SELECT CASE before any statement"
                                        .to_owned(),
                                ));
                            } else {
                                return Err(Error::Bad(
                                    end_span.pos,
                                    format!("END {} without {}", token, token),
                                ));
                            }
                        }
                    }
                }

                _ => {
                    if cases.is_empty() {
                        return Err(Error::Bad(
                            peeked.pos,
                            "Expected CASE after SELECT CASE before any statement".to_owned(),
                        ));
                    }

                    if let Some(stmt) = self.parse_one_safe()? {
                        cases[i].body.push(stmt);
                    }
                }
            }
        }

        self.expect_and_consume_with_pos(Token::Select, select_pos, "SELECT without END SELECT")?;

        Ok(Statement::Select(SelectSpan { expr, cases, end_pos }))
    }

    /// Advances until the next statement after failing to parse a `SELECT` statement.
    fn reset_select(&mut self, select_pos: LineCol) -> Result<()> {
        loop {
            match self.lexer.peek()?.token {
                Token::Eof => break,
                Token::End => {
                    self.lexer.consume_peeked();
                    self.expect_and_consume_with_pos(
                        Token::Select,
                        select_pos,
                        "SELECT without END SELECT",
                    )?;
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
    fn parse_while(&mut self, while_pos: LineCol) -> Result<Statement> {
        let expr = self.parse_required_expr("No expression in WHILE statement")?;
        self.expect_and_consume(Token::Eol, "Expecting newline after WHILE")?;

        let stmts = self.parse_until(Token::Wend)?;
        self.expect_and_consume_with_pos(Token::Wend, while_pos, "WHILE without WEND")?;

        Ok(Statement::While(WhileSpan { expr, body: stmts }))
    }

    /// Advances until the next statement after failing to parse a `WHILE` statement.
    fn reset_while(&mut self) -> Result<()> {
        loop {
            match self.lexer.peek()?.token {
                Token::Eof => break,
                Token::Wend => {
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

    /// Extracts the next available uniline statement from the input stream, or `None` if none is
    /// available.
    ///
    /// The statement must be specifiable in a single line as part of a uniline `IF` statement, and
    /// we currently expect this to only be used while parsing an `IF`.
    ///
    /// On success, the stream is left in a position where the next statement can be extracted.
    /// On failure, the caller must advance the stream to the next statement by calling `reset`.
    fn parse_uniline(&mut self) -> Result<Option<Statement>> {
        let token_span = self.lexer.read()?;
        match token_span.token {
            Token::Data => Ok(Some(self.parse_data()?)),
            Token::End => Ok(Some(self.parse_end(token_span.pos)?)),
            Token::Eof | Token::Eol => Ok(None),
            Token::Exit => Ok(Some(self.parse_exit(token_span.pos)?)),
            Token::Gosub => Ok(Some(self.parse_gosub()?)),
            Token::Goto => Ok(Some(self.parse_goto()?)),
            Token::On => Ok(Some(self.parse_on()?)),
            Token::Return => Ok(Some(Statement::Return(ReturnSpan { pos: token_span.pos }))),
            Token::Symbol(vref) => {
                let peeked = self.lexer.peek()?;
                if peeked.token == Token::Equal {
                    self.lexer.consume_peeked();
                    Ok(Some(self.parse_assignment(vref, token_span.pos)?))
                } else {
                    Ok(Some(self.parse_array_or_builtin_call(vref, token_span.pos)?))
                }
            }
            Token::Bad(msg) => Err(Error::Bad(token_span.pos, msg)),
            t => Err(Error::Bad(token_span.pos, format!("Unexpected {} in uniline IF branch", t))),
        }
    }

    /// Extracts the next available statement from the input stream, or `None` if none is available.
    ///
    /// On success, the stream is left in a position where the next statement can be extracted.
    /// On failure, the caller must advance the stream to the next statement by calling `reset`.
    fn parse_one(&mut self) -> Result<Option<Statement>> {
        loop {
            match self.lexer.peek()?.token {
                Token::Eol => {
                    self.lexer.consume_peeked();
                }
                Token::Eof => return Ok(None),
                _ => break,
            }
        }
        let token_span = self.lexer.read()?;
        let res = match token_span.token {
            Token::Data => Ok(Some(self.parse_data()?)),
            Token::Dim => Ok(Some(self.parse_dim()?)),
            Token::Do => {
                let result = self.parse_do(token_span.pos);
                if result.is_err() {
                    self.reset_do()?;
                }
                Ok(Some(result?))
            }
            Token::End => Ok(Some(self.parse_end(token_span.pos)?)),
            Token::Eof => return Ok(None),
            Token::Eol => Ok(None),
            Token::Exit => Ok(Some(self.parse_exit(token_span.pos)?)),
            Token::If => {
                let result = self.parse_if(token_span.pos);
                if result.is_err() {
                    self.reset_if(token_span.pos)?;
                }
                Ok(Some(result?))
            }
            Token::For => {
                let result = self.parse_for(token_span.pos);
                if result.is_err() {
                    self.reset_for()?;
                }
                Ok(Some(result?))
            }
            Token::Function => {
                let result = self.parse_function(token_span.pos);
                if result.is_err() {
                    self.reset_callable(Token::Function)?;
                }
                Ok(Some(result?))
            }
            Token::Gosub => {
                let result = self.parse_gosub();
                Ok(Some(result?))
            }
            Token::Goto => {
                let result = self.parse_goto();
                Ok(Some(result?))
            }
            Token::Integer(i) => {
                let name = format!("{}", i);
                // When we encounter a line number, we must return early to avoid looking for a line
                // ending given that the next statement may start after the label we found.
                return Ok(Some(Statement::Label(LabelSpan { name, name_pos: token_span.pos })));
            }
            Token::Label(name) => {
                // When we encounter a label, we must return early to avoid looking for a line
                // ending given that the next statement may start after the label we found.
                return Ok(Some(Statement::Label(LabelSpan { name, name_pos: token_span.pos })));
            }
            Token::On => Ok(Some(self.parse_on()?)),
            Token::Return => Ok(Some(Statement::Return(ReturnSpan { pos: token_span.pos }))),
            Token::Select => {
                let result = self.parse_select(token_span.pos);
                if result.is_err() {
                    self.reset_select(token_span.pos)?;
                }
                Ok(Some(result?))
            }
            Token::Sub => {
                let result = self.parse_sub(token_span.pos);
                if result.is_err() {
                    self.reset_callable(Token::Sub)?;
                }
                Ok(Some(result?))
            }
            Token::Symbol(vref) => {
                let peeked = self.lexer.peek()?;
                if peeked.token == Token::Equal {
                    self.lexer.consume_peeked();
                    Ok(Some(self.parse_assignment(vref, token_span.pos)?))
                } else {
                    Ok(Some(self.parse_array_or_builtin_call(vref, token_span.pos)?))
                }
            }
            Token::While => {
                let result = self.parse_while(token_span.pos);
                if result.is_err() {
                    self.reset_while()?;
                }
                Ok(Some(result?))
            }
            Token::Bad(msg) => return Err(Error::Bad(token_span.pos, msg)),
            t => return Err(Error::Bad(token_span.pos, format!("Unexpected {} in statement", t))),
        };

        let token_span = self.lexer.peek()?;
        match token_span.token {
            Token::Eof => (),
            Token::Eol => {
                self.lexer.consume_peeked();
            }
            _ => {
                return Err(Error::Bad(
                    token_span.pos,
                    format!("Expected newline but found {}", token_span.token),
                ))
            }
        };

        res
    }

    /// Advances until the next statement after failing to parse a single statement.
    fn reset(&mut self) -> Result<()> {
        loop {
            match self.lexer.peek()?.token {
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
    fn parse_one_safe(&mut self) -> Result<Option<Statement>> {
        let result = self.parse_one();
        if result.is_err() {
            self.reset()?;
        }
        result
    }
}

pub(crate) struct StatementIter<'a> {
    parser: Parser<'a>,
}

impl Iterator for StatementIter<'_> {
    type Item = Result<Statement>;

    fn next(&mut self) -> Option<Self::Item> {
        self.parser.parse_one_safe().transpose()
    }
}

/// Extracts all statements from the input stream.
pub(crate) fn parse(input: &mut dyn io::Read) -> StatementIter<'_> {
    StatementIter { parser: Parser::from(input) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::ExprType;

    /// Syntactic sugar to instantiate a `LineCol` for testing.
    fn lc(line: usize, col: usize) -> LineCol {
        LineCol { line, col }
    }

    /// Syntactic sugar to instantiate an `Expr::Boolean` for testing.
    fn expr_boolean(value: bool, line: usize, col: usize) -> Expr {
        Expr::Boolean(BooleanSpan { value, pos: LineCol { line, col } })
    }

    /// Syntactic sugar to instantiate an `Expr::Double` for testing.
    fn expr_double(value: f64, line: usize, col: usize) -> Expr {
        Expr::Double(DoubleSpan { value, pos: LineCol { line, col } })
    }

    /// Syntactic sugar to instantiate an `Expr::Integer` for testing.
    fn expr_integer(value: i32, line: usize, col: usize) -> Expr {
        Expr::Integer(IntegerSpan { value, pos: LineCol { line, col } })
    }

    /// Syntactic sugar to instantiate an `Expr::Text` for testing.
    fn expr_text<S: Into<String>>(value: S, line: usize, col: usize) -> Expr {
        Expr::Text(TextSpan { value: value.into(), pos: LineCol { line, col } })
    }

    /// Syntactic sugar to instantiate an `Expr::Symbol` for testing.
    fn expr_symbol(vref: VarRef, line: usize, col: usize) -> Expr {
        Expr::Symbol(SymbolSpan { vref, pos: LineCol { line, col } })
    }

    #[test]
    fn test_varref_to_unannotated_string() {
        assert_eq!(
            "print",
            &vref_to_unannotated_string(VarRef::new("print", None), LineCol { line: 0, col: 0 })
                .unwrap()
        );

        assert_eq!(
            "7:6: Type annotation not allowed in print$",
            format!(
                "{}",
                &vref_to_unannotated_string(
                    VarRef::new("print", Some(ExprType::Text)),
                    LineCol { line: 7, col: 6 }
                )
                .unwrap_err()
            )
        );
    }

    /// Runs the parser on the given `input` and expects the returned statements to match
    /// `exp_statements`.
    fn do_ok_test(input: &str, exp_statements: &[Statement]) {
        let mut input = input.as_bytes();
        let statements =
            parse(&mut input).map(|r| r.expect("Parsing failed")).collect::<Vec<Statement>>();
        assert_eq!(exp_statements, statements.as_slice());
    }

    /// Runs the parser on the given `input` and expects the `err` error message.
    fn do_error_test(input: &str, expected_err: &str) {
        let mut input = input.as_bytes();
        let mut parser = Parser::from(&mut input);
        assert_eq!(
            expected_err,
            format!("{}", parser.parse_one_safe().expect_err("Parsing did not fail"))
        );
        assert!(parser.parse_one_safe().unwrap().is_none());
    }

    /// Runs the parser on the given `input` and expects the `err` error message.
    ///
    /// Does not expect the parser to be reset to the next (EOF) statement.
    // TODO(jmmv): Need better testing to ensure the parser is reset to something that can be
    // parsed next.
    fn do_error_test_no_reset(input: &str, expected_err: &str) {
        let mut input = input.as_bytes();
        for result in parse(&mut input) {
            if let Err(e) = result {
                assert_eq!(expected_err, format!("{}", e));
                return;
            }
        }
        panic!("Parsing did not fail")
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
                Statement::Assignment(AssignmentSpan {
                    vref: VarRef::new("a", None),
                    vref_pos: lc(1, 1),
                    expr: expr_integer(1, 1, 3),
                }),
                Statement::Assignment(AssignmentSpan {
                    vref: VarRef::new("b", None),
                    vref_pos: lc(2, 1),
                    expr: expr_integer(2, 2, 3),
                }),
                Statement::Assignment(AssignmentSpan {
                    vref: VarRef::new("c", None),
                    vref_pos: lc(2, 5),
                    expr: expr_integer(3, 2, 7),
                }),
                Statement::Assignment(AssignmentSpan {
                    vref: VarRef::new("d", None),
                    vref_pos: lc(3, 1),
                    expr: expr_integer(4, 3, 3),
                }),
            ],
        );
    }

    #[test]
    fn test_array_assignments() {
        do_ok_test(
            "a(1)=100\nfoo(2, 3)=\"text\"\nabc$ (5 + z, 6) = TRUE OR FALSE",
            &[
                Statement::ArrayAssignment(ArrayAssignmentSpan {
                    vref: VarRef::new("a", None),
                    vref_pos: lc(1, 1),
                    subscripts: vec![expr_integer(1, 1, 3)],
                    expr: expr_integer(100, 1, 6),
                }),
                Statement::ArrayAssignment(ArrayAssignmentSpan {
                    vref: VarRef::new("foo", None),
                    vref_pos: lc(2, 1),
                    subscripts: vec![expr_integer(2, 2, 5), expr_integer(3, 2, 8)],
                    expr: expr_text("text", 2, 11),
                }),
                Statement::ArrayAssignment(ArrayAssignmentSpan {
                    vref: VarRef::new("abc", Some(ExprType::Text)),
                    vref_pos: lc(3, 1),
                    subscripts: vec![
                        Expr::Add(Box::from(BinaryOpSpan {
                            lhs: expr_integer(5, 3, 7),
                            rhs: expr_symbol(VarRef::new("z".to_owned(), None), 3, 11),
                            pos: lc(3, 9),
                        })),
                        expr_integer(6, 3, 14),
                    ],
                    expr: Expr::Or(Box::from(BinaryOpSpan {
                        lhs: expr_boolean(true, 3, 19),
                        rhs: expr_boolean(false, 3, 27),
                        pos: lc(3, 24),
                    })),
                }),
            ],
        );
    }

    #[test]
    fn test_array_assignment_errors() {
        do_error_test("a(", "1:3: Unexpected <<EOF>>");
        do_error_test("a()", "1:2: Expected expression");
        do_error_test("a() =", "1:6: Missing expression in array assignment");
        do_error_test("a() IF", "1:2: Expected expression");
        do_error_test("a() = 3 4", "1:9: Unexpected value in expression");
        do_error_test("a() = 3 THEN", "1:9: Unexpected THEN in array assignment");
        do_error_test("a(,) = 3", "1:3: Missing expression");
        do_error_test("a(2;3) = 3", "1:4: Unexpected ;");
        do_error_test("(2) = 3", "1:1: Unexpected ( in statement");
    }

    #[test]
    fn test_assignments() {
        do_ok_test(
            "a=1\nfoo$ = \"bar\"\nb$ = 3 + z",
            &[
                Statement::Assignment(AssignmentSpan {
                    vref: VarRef::new("a", None),
                    vref_pos: lc(1, 1),
                    expr: expr_integer(1, 1, 3),
                }),
                Statement::Assignment(AssignmentSpan {
                    vref: VarRef::new("foo", Some(ExprType::Text)),
                    vref_pos: lc(2, 1),
                    expr: expr_text("bar", 2, 8),
                }),
                Statement::Assignment(AssignmentSpan {
                    vref: VarRef::new("b", Some(ExprType::Text)),
                    vref_pos: lc(3, 1),
                    expr: Expr::Add(Box::from(BinaryOpSpan {
                        lhs: expr_integer(3, 3, 6),
                        rhs: expr_symbol(VarRef::new("z", None), 3, 10),
                        pos: lc(3, 8),
                    })),
                }),
            ],
        );
    }

    #[test]
    fn test_assignment_errors() {
        do_error_test("a =", "1:4: Missing expression in assignment");
        do_error_test("a = b 3", "1:7: Unexpected value in expression");
        do_error_test("a = b, 3", "1:6: Unexpected , in assignment");
        do_error_test("a = if 3", "1:5: Unexpected keyword in expression");
        do_error_test("true = 1", "1:1: Unexpected TRUE in statement");
    }

    #[test]
    fn test_builtin_calls() {
        do_ok_test(
            "PRINT a\nPRINT ; 3 , c$\nNOARGS\nNAME 3 AS 4",
            &[
                Statement::Call(CallSpan {
                    vref: VarRef::new("PRINT", None),
                    vref_pos: lc(1, 1),
                    args: vec![ArgSpan {
                        expr: Some(expr_symbol(VarRef::new("a", None), 1, 7)),
                        sep: ArgSep::End,
                        sep_pos: lc(1, 8),
                    }],
                }),
                Statement::Call(CallSpan {
                    vref: VarRef::new("PRINT", None),
                    vref_pos: lc(2, 1),
                    args: vec![
                        ArgSpan { expr: None, sep: ArgSep::Short, sep_pos: lc(2, 7) },
                        ArgSpan {
                            expr: Some(expr_integer(3, 2, 9)),
                            sep: ArgSep::Long,
                            sep_pos: lc(2, 11),
                        },
                        ArgSpan {
                            expr: Some(expr_symbol(VarRef::new("c", Some(ExprType::Text)), 2, 13)),
                            sep: ArgSep::End,
                            sep_pos: lc(2, 15),
                        },
                    ],
                }),
                Statement::Call(CallSpan {
                    vref: VarRef::new("NOARGS", None),
                    vref_pos: lc(3, 1),
                    args: vec![],
                }),
                Statement::Call(CallSpan {
                    vref: VarRef::new("NAME", None),
                    vref_pos: lc(4, 1),
                    args: vec![
                        ArgSpan {
                            expr: Some(expr_integer(3, 4, 6)),
                            sep: ArgSep::As,
                            sep_pos: lc(4, 8),
                        },
                        ArgSpan {
                            expr: Some(expr_integer(4, 4, 11)),
                            sep: ArgSep::End,
                            sep_pos: lc(4, 12),
                        },
                    ],
                }),
            ],
        );
    }

    #[test]
    fn test_builtin_calls_and_array_references_disambiguation() {
        use Expr::*;

        do_ok_test(
            "PRINT(1)",
            &[Statement::Call(CallSpan {
                vref: VarRef::new("PRINT", None),
                vref_pos: lc(1, 1),
                args: vec![ArgSpan {
                    expr: Some(expr_integer(1, 1, 7)),
                    sep: ArgSep::End,
                    sep_pos: lc(1, 9),
                }],
            })],
        );

        do_ok_test(
            "PRINT(1), 2",
            &[Statement::Call(CallSpan {
                vref: VarRef::new("PRINT", None),
                vref_pos: lc(1, 1),
                args: vec![
                    ArgSpan {
                        expr: Some(expr_integer(1, 1, 7)),
                        sep: ArgSep::Long,
                        sep_pos: lc(1, 9),
                    },
                    ArgSpan {
                        expr: Some(expr_integer(2, 1, 11)),
                        sep: ArgSep::End,
                        sep_pos: lc(1, 12),
                    },
                ],
            })],
        );

        do_ok_test(
            "PRINT(1); 2",
            &[Statement::Call(CallSpan {
                vref: VarRef::new("PRINT", None),
                vref_pos: lc(1, 1),
                args: vec![
                    ArgSpan {
                        expr: Some(expr_integer(1, 1, 7)),
                        sep: ArgSep::Short,
                        sep_pos: lc(1, 9),
                    },
                    ArgSpan {
                        expr: Some(expr_integer(2, 1, 11)),
                        sep: ArgSep::End,
                        sep_pos: lc(1, 12),
                    },
                ],
            })],
        );

        do_ok_test(
            "PRINT(1);",
            &[Statement::Call(CallSpan {
                vref: VarRef::new("PRINT", None),
                vref_pos: lc(1, 1),
                args: vec![
                    ArgSpan {
                        expr: Some(expr_integer(1, 1, 7)),
                        sep: ArgSep::Short,
                        sep_pos: lc(1, 9),
                    },
                    ArgSpan { expr: None, sep: ArgSep::End, sep_pos: lc(1, 10) },
                ],
            })],
        );

        do_ok_test(
            "PRINT(1) + 2; 3",
            &[Statement::Call(CallSpan {
                vref: VarRef::new("PRINT", None),
                vref_pos: lc(1, 1),
                args: vec![
                    ArgSpan {
                        expr: Some(Add(Box::from(BinaryOpSpan {
                            lhs: expr_integer(1, 1, 7),
                            rhs: expr_integer(2, 1, 12),
                            pos: lc(1, 10),
                        }))),
                        sep: ArgSep::Short,
                        sep_pos: lc(1, 13),
                    },
                    ArgSpan {
                        expr: Some(expr_integer(3, 1, 15)),
                        sep: ArgSep::End,
                        sep_pos: lc(1, 16),
                    },
                ],
            })],
        );
    }

    #[test]
    fn test_builtin_calls_errors() {
        do_error_test("FOO 3 5\n", "1:7: Unexpected value in expression");
        do_error_test("INPUT$ a\n", "1:1: Type annotation not allowed in INPUT$");
        do_error_test("PRINT IF 1\n", "1:7: Unexpected keyword in expression");
        do_error_test("PRINT 3, IF 1\n", "1:10: Unexpected keyword in expression");
        do_error_test("PRINT 3 THEN\n", "1:9: Expected comma, semicolon, or end of statement");
        do_error_test("PRINT ()\n", "1:7: Expected expression");
        do_error_test("PRINT (2, 3)\n", "1:7: Expected expression");
        do_error_test("PRINT (2, 3); 4\n", "1:7: Expected expression");
    }

    #[test]
    fn test_data() {
        do_ok_test("DATA", &[Statement::Data(DataSpan { values: vec![None] })]);

        do_ok_test("DATA , ", &[Statement::Data(DataSpan { values: vec![None, None] })]);
        do_ok_test(
            "DATA , , ,",
            &[Statement::Data(DataSpan { values: vec![None, None, None, None] })],
        );

        do_ok_test(
            "DATA 1: DATA 2",
            &[
                Statement::Data(DataSpan { values: vec![Some(Value::Integer(1))] }),
                Statement::Data(DataSpan { values: vec![Some(Value::Integer(2))] }),
            ],
        );

        do_ok_test(
            "DATA TRUE, -3, 5.1, \"foo\"",
            &[Statement::Data(DataSpan {
                values: vec![
                    Some(Value::Boolean(true)),
                    Some(Value::Integer(-3)),
                    Some(Value::Double(5.1)),
                    Some(Value::Text("foo".to_owned())),
                ],
            })],
        );

        do_ok_test(
            "DATA , TRUE, , 3, , 5.1, , \"foo\",",
            &[Statement::Data(DataSpan {
                values: vec![
                    None,
                    Some(Value::Boolean(true)),
                    None,
                    Some(Value::Integer(3)),
                    None,
                    Some(Value::Double(5.1)),
                    None,
                    Some(Value::Text("foo".to_owned())),
                    None,
                ],
            })],
        );

        do_ok_test(
            "DATA -3, -5.1",
            &[Statement::Data(DataSpan {
                values: vec![Some(Value::Integer(-3)), Some(Value::Double(-5.1))],
            })],
        );
    }

    #[test]
    fn test_data_errors() {
        do_error_test("DATA + 2", "1:6: Unexpected + in DATA statement");
        do_error_test("DATA ;", "1:6: Unexpected ; in DATA statement");
        do_error_test("DATA 5 + 1", "1:8: Expected comma after datum but found +");
        do_error_test("DATA 5 ; 1", "1:8: Expected comma after datum but found ;");
        do_error_test("DATA -FALSE", "1:7: Expected number after -");
        do_error_test("DATA -\"abc\"", "1:7: Expected number after -");
        do_error_test("DATA -foo", "1:7: Expected number after -");
    }

    #[test]
    fn test_dim_default_type() {
        do_ok_test(
            "DIM i",
            &[Statement::Dim(DimSpan {
                name: "i".to_owned(),
                name_pos: lc(1, 5),
                shared: false,
                vtype: ExprType::Integer,
                vtype_pos: lc(1, 6),
            })],
        );
    }

    #[test]
    fn test_dim_as_simple_types() {
        do_ok_test(
            "DIM i AS BOOLEAN",
            &[Statement::Dim(DimSpan {
                name: "i".to_owned(),
                name_pos: lc(1, 5),
                shared: false,
                vtype: ExprType::Boolean,
                vtype_pos: lc(1, 10),
            })],
        );
        do_ok_test(
            "DIM i AS DOUBLE",
            &[Statement::Dim(DimSpan {
                name: "i".to_owned(),
                name_pos: lc(1, 5),
                shared: false,
                vtype: ExprType::Double,
                vtype_pos: lc(1, 10),
            })],
        );
        do_ok_test(
            "DIM i AS INTEGER",
            &[Statement::Dim(DimSpan {
                name: "i".to_owned(),
                name_pos: lc(1, 5),
                shared: false,
                vtype: ExprType::Integer,
                vtype_pos: lc(1, 10),
            })],
        );
        do_ok_test(
            "DIM i AS STRING",
            &[Statement::Dim(DimSpan {
                name: "i".to_owned(),
                name_pos: lc(1, 5),
                shared: false,
                vtype: ExprType::Text,
                vtype_pos: lc(1, 10),
            })],
        );
    }

    #[test]
    fn test_dim_consecutive() {
        do_ok_test(
            "DIM i\nDIM j AS BOOLEAN\nDIM k",
            &[
                Statement::Dim(DimSpan {
                    name: "i".to_owned(),
                    name_pos: lc(1, 5),
                    shared: false,
                    vtype: ExprType::Integer,
                    vtype_pos: lc(1, 6),
                }),
                Statement::Dim(DimSpan {
                    name: "j".to_owned(),
                    name_pos: lc(2, 5),
                    shared: false,
                    vtype: ExprType::Boolean,
                    vtype_pos: lc(2, 10),
                }),
                Statement::Dim(DimSpan {
                    name: "k".to_owned(),
                    name_pos: lc(3, 5),
                    shared: false,
                    vtype: ExprType::Integer,
                    vtype_pos: lc(3, 6),
                }),
            ],
        );
    }

    #[test]
    fn test_dim_shared() {
        do_ok_test(
            "DIM SHARED i",
            &[Statement::Dim(DimSpan {
                name: "i".to_owned(),
                name_pos: lc(1, 12),
                shared: true,
                vtype: ExprType::Integer,
                vtype_pos: lc(1, 13),
            })],
        );
        do_ok_test(
            "DIM SHARED i AS BOOLEAN",
            &[Statement::Dim(DimSpan {
                name: "i".to_owned(),
                name_pos: lc(1, 12),
                shared: true,
                vtype: ExprType::Boolean,
                vtype_pos: lc(1, 17),
            })],
        );
    }

    #[test]
    fn test_dim_array() {
        use Expr::*;

        do_ok_test(
            "DIM i(10)",
            &[Statement::DimArray(DimArraySpan {
                name: "i".to_owned(),
                name_pos: lc(1, 5),
                shared: false,
                dimensions: vec![expr_integer(10, 1, 7)],
                subtype: ExprType::Integer,
                subtype_pos: lc(1, 10),
            })],
        );

        do_ok_test(
            "DIM foo(-5, 0) AS STRING",
            &[Statement::DimArray(DimArraySpan {
                name: "foo".to_owned(),
                name_pos: lc(1, 5),
                shared: false,
                dimensions: vec![
                    Negate(Box::from(UnaryOpSpan { expr: expr_integer(5, 1, 10), pos: lc(1, 9) })),
                    expr_integer(0, 1, 13),
                ],
                subtype: ExprType::Text,
                subtype_pos: lc(1, 19),
            })],
        );

        do_ok_test(
            "DIM foo(bar$() + 3, 8, -1)",
            &[Statement::DimArray(DimArraySpan {
                name: "foo".to_owned(),
                name_pos: lc(1, 5),
                shared: false,
                dimensions: vec![
                    Add(Box::from(BinaryOpSpan {
                        lhs: Call(CallSpan {
                            vref: VarRef::new("bar", Some(ExprType::Text)),
                            vref_pos: lc(1, 9),
                            args: vec![],
                        }),
                        rhs: expr_integer(3, 1, 18),
                        pos: lc(1, 16),
                    })),
                    expr_integer(8, 1, 21),
                    Negate(Box::from(UnaryOpSpan { expr: expr_integer(1, 1, 25), pos: lc(1, 24) })),
                ],
                subtype: ExprType::Integer,
                subtype_pos: lc(1, 27),
            })],
        );

        do_ok_test(
            "DIM SHARED i(10)",
            &[Statement::DimArray(DimArraySpan {
                name: "i".to_owned(),
                name_pos: lc(1, 12),
                shared: true,
                dimensions: vec![expr_integer(10, 1, 14)],
                subtype: ExprType::Integer,
                subtype_pos: lc(1, 17),
            })],
        );
    }

    #[test]
    fn test_dim_errors() {
        do_error_test("DIM", "1:4: Expected variable name after DIM");
        do_error_test("DIM 3", "1:5: Expected variable name after DIM");
        do_error_test("DIM AS", "1:5: Expected variable name after DIM");
        do_error_test("DIM foo 3", "1:9: Expected AS or end of statement");
        do_error_test("DIM a AS", "1:9: Invalid type name <<EOF>> in AS type definition");
        do_error_test("DIM a$ AS", "1:5: Type annotation not allowed in a$");
        do_error_test("DIM a AS 3", "1:10: Invalid type name 3 in AS type definition");
        do_error_test("DIM a AS INTEGER 3", "1:18: Unexpected 3 in DIM statement");

        do_error_test("DIM a()", "1:6: Arrays require at least one dimension");
        do_error_test("DIM a(,)", "1:7: Missing expression");
        do_error_test("DIM a(, 3)", "1:7: Missing expression");
        do_error_test("DIM a(3, )", "1:10: Missing expression");
        do_error_test("DIM a(3, , 4)", "1:10: Missing expression");
        do_error_test("DIM a(1) AS INTEGER 3", "1:21: Unexpected 3 in DIM statement");
    }

    #[test]
    fn test_do_until_empty() {
        do_ok_test(
            "DO UNTIL TRUE\nLOOP",
            &[Statement::Do(DoSpan {
                guard: DoGuard::PreUntil(expr_boolean(true, 1, 10)),
                body: vec![],
            })],
        );

        do_ok_test(
            "DO UNTIL FALSE\nREM foo\nLOOP",
            &[Statement::Do(DoSpan {
                guard: DoGuard::PreUntil(expr_boolean(false, 1, 10)),
                body: vec![],
            })],
        );
    }

    #[test]
    fn test_do_infinite_empty() {
        do_ok_test("DO\nLOOP", &[Statement::Do(DoSpan { guard: DoGuard::Infinite, body: vec![] })]);
    }

    #[test]
    fn test_do_pre_until_loops() {
        do_ok_test(
            "DO UNTIL TRUE\nA\nB\nLOOP",
            &[Statement::Do(DoSpan {
                guard: DoGuard::PreUntil(expr_boolean(true, 1, 10)),
                body: vec![make_bare_builtin_call("A", 2, 1), make_bare_builtin_call("B", 3, 1)],
            })],
        );
    }

    #[test]
    fn test_do_pre_while_loops() {
        do_ok_test(
            "DO WHILE TRUE\nA\nB\nLOOP",
            &[Statement::Do(DoSpan {
                guard: DoGuard::PreWhile(expr_boolean(true, 1, 10)),
                body: vec![make_bare_builtin_call("A", 2, 1), make_bare_builtin_call("B", 3, 1)],
            })],
        );
    }

    #[test]
    fn test_do_post_until_loops() {
        do_ok_test(
            "DO\nA\nB\nLOOP UNTIL TRUE",
            &[Statement::Do(DoSpan {
                guard: DoGuard::PostUntil(expr_boolean(true, 4, 12)),

                body: vec![make_bare_builtin_call("A", 2, 1), make_bare_builtin_call("B", 3, 1)],
            })],
        );
    }

    #[test]
    fn test_do_post_while_loops() {
        do_ok_test(
            "DO\nA\nB\nLOOP WHILE FALSE",
            &[Statement::Do(DoSpan {
                guard: DoGuard::PostWhile(expr_boolean(false, 4, 12)),
                body: vec![make_bare_builtin_call("A", 2, 1), make_bare_builtin_call("B", 3, 1)],
            })],
        );
    }

    #[test]
    fn test_do_nested() {
        let code = r#"
            DO WHILE TRUE
                A
                DO
                    B
                LOOP UNTIL FALSE
                C
            LOOP
        "#;
        do_ok_test(
            code,
            &[Statement::Do(DoSpan {
                guard: DoGuard::PreWhile(expr_boolean(true, 2, 22)),
                body: vec![
                    make_bare_builtin_call("A", 3, 17),
                    Statement::Do(DoSpan {
                        guard: DoGuard::PostUntil(expr_boolean(false, 6, 28)),
                        body: vec![make_bare_builtin_call("B", 5, 21)],
                    }),
                    make_bare_builtin_call("C", 7, 17),
                ],
            })],
        );
    }

    #[test]
    fn test_do_errors() {
        do_error_test("DO\n", "1:1: DO without LOOP");
        do_error_test("DO FOR\n", "1:4: Expecting newline, UNTIL or WHILE after DO");

        do_error_test("\n\nDO UNTIL TRUE\n", "3:1: DO without LOOP");
        do_error_test("\n\nDO WHILE TRUE\n", "3:1: DO without LOOP");
        do_error_test("DO UNTIL TRUE\nEND", "1:1: DO without LOOP");
        do_error_test("DO WHILE TRUE\nEND", "1:1: DO without LOOP");
        do_error_test("DO UNTIL TRUE\nEND\n", "1:1: DO without LOOP");
        do_error_test("DO WHILE TRUE\nEND\n", "1:1: DO without LOOP");
        do_error_test("DO UNTIL TRUE\nEND WHILE\n", "2:5: Unexpected keyword in expression");
        do_error_test("DO WHILE TRUE\nEND WHILE\n", "2:5: Unexpected keyword in expression");

        do_error_test("DO UNTIL\n", "1:9: No expression in UNTIL clause");
        do_error_test("DO WHILE\n", "1:9: No expression in WHILE clause");
        do_error_test("DO UNTIL TRUE", "1:14: Expecting newline after DO");
        do_error_test("DO WHILE TRUE", "1:14: Expecting newline after DO");

        do_error_test("DO\nLOOP UNTIL", "2:11: No expression in UNTIL clause");
        do_error_test("DO\nLOOP WHILE\n", "2:11: No expression in WHILE clause");

        do_error_test("DO UNTIL ,\nLOOP", "1:10: No expression in UNTIL clause");
        do_error_test("DO WHILE ,\nLOOP", "1:10: No expression in WHILE clause");

        do_error_test("DO\nLOOP UNTIL ,\n", "2:12: No expression in UNTIL clause");
        do_error_test("DO\nLOOP WHILE ,\n", "2:12: No expression in WHILE clause");

        do_error_test(
            "DO WHILE TRUE\nLOOP UNTIL FALSE",
            "1:1: DO loop cannot have pre and post guards at the same time",
        );
    }

    #[test]
    fn test_exit_do() {
        do_ok_test("  EXIT DO", &[Statement::ExitDo(ExitSpan { pos: lc(1, 3) })]);
    }

    #[test]
    fn test_exit_for() {
        do_ok_test("  EXIT FOR", &[Statement::ExitFor(ExitSpan { pos: lc(1, 3) })]);
    }

    #[test]
    fn test_exit_errors() {
        do_error_test("EXIT", "1:5: Expecting DO or FOR after EXIT");
        do_error_test("EXIT 5", "1:6: Expecting DO or FOR after EXIT");
    }

    /// Wrapper around `do_ok_test` to parse an expression.  Given that expressions alone are not
    /// valid statements, we have to put them in a statement to parse them.  In doing so, we can
    /// also put an extra statement after them to ensure we detect their end properly.
    fn do_expr_ok_test(input: &str, expr: Expr) {
        do_ok_test(
            &format!("PRINT {}, 1", input),
            &[Statement::Call(CallSpan {
                vref: VarRef::new("PRINT", None),
                vref_pos: lc(1, 1),
                args: vec![
                    ArgSpan {
                        expr: Some(expr),
                        sep: ArgSep::Long,
                        sep_pos: lc(1, 7 + input.len()),
                    },
                    ArgSpan {
                        expr: Some(expr_integer(1, 1, 6 + input.len() + 3)),
                        sep: ArgSep::End,
                        sep_pos: lc(1, 10 + input.len()),
                    },
                ],
            })],
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
        do_expr_ok_test("TRUE", expr_boolean(true, 1, 7));
        do_expr_ok_test("FALSE", expr_boolean(false, 1, 7));
        do_expr_ok_test("5", expr_integer(5, 1, 7));
        do_expr_ok_test("\"some text\"", expr_text("some text", 1, 7));
    }

    #[test]
    fn test_expr_symbols() {
        do_expr_ok_test("foo", expr_symbol(VarRef::new("foo", None), 1, 7));
        do_expr_ok_test("bar$", expr_symbol(VarRef::new("bar", Some(ExprType::Text)), 1, 7));
    }

    #[test]
    fn test_expr_parens() {
        use Expr::*;
        do_expr_ok_test("(1)", expr_integer(1, 1, 8));
        do_expr_ok_test("((1))", expr_integer(1, 1, 9));
        do_expr_ok_test(" ( ( 1 ) ) ", expr_integer(1, 1, 12));
        do_expr_ok_test(
            "3 * (2 + 5)",
            Multiply(Box::from(BinaryOpSpan {
                lhs: expr_integer(3, 1, 7),
                rhs: Add(Box::from(BinaryOpSpan {
                    lhs: expr_integer(2, 1, 12),
                    rhs: expr_integer(5, 1, 16),
                    pos: lc(1, 14),
                })),
                pos: lc(1, 9),
            })),
        );
        do_expr_ok_test(
            "(7) - (1) + (-2)",
            Add(Box::from(BinaryOpSpan {
                lhs: Subtract(Box::from(BinaryOpSpan {
                    lhs: expr_integer(7, 1, 8),
                    rhs: expr_integer(1, 1, 14),
                    pos: lc(1, 11),
                })),
                rhs: Negate(Box::from(UnaryOpSpan {
                    expr: expr_integer(2, 1, 21),
                    pos: lc(1, 20),
                })),
                pos: lc(1, 17),
            })),
        );
    }

    #[test]
    fn test_expr_arith_ops() {
        use Expr::*;
        let span = Box::from(BinaryOpSpan {
            lhs: expr_integer(1, 1, 7),
            rhs: expr_integer(2, 1, 11),
            pos: lc(1, 9),
        });
        do_expr_ok_test("1 + 2", Add(span.clone()));
        do_expr_ok_test("1 - 2", Subtract(span.clone()));
        do_expr_ok_test("1 * 2", Multiply(span.clone()));
        do_expr_ok_test("1 / 2", Divide(span.clone()));
        do_expr_ok_test("1 ^ 2", Power(span));
        let span = Box::from(BinaryOpSpan {
            lhs: expr_integer(1, 1, 7),
            rhs: expr_integer(2, 1, 13),
            pos: lc(1, 9),
        });
        do_expr_ok_test("1 MOD 2", Modulo(span));
    }

    #[test]
    fn test_expr_rel_ops() {
        use Expr::*;
        let span1 = Box::from(BinaryOpSpan {
            lhs: expr_integer(1, 1, 7),
            rhs: expr_integer(2, 1, 11),
            pos: lc(1, 9),
        });
        let span2 = Box::from(BinaryOpSpan {
            lhs: expr_integer(1, 1, 7),
            rhs: expr_integer(2, 1, 12),
            pos: lc(1, 9),
        });
        do_expr_ok_test("1 = 2", Equal(span1.clone()));
        do_expr_ok_test("1 <> 2", NotEqual(span2.clone()));
        do_expr_ok_test("1 < 2", Less(span1.clone()));
        do_expr_ok_test("1 <= 2", LessEqual(span2.clone()));
        do_expr_ok_test("1 > 2", Greater(span1));
        do_expr_ok_test("1 >= 2", GreaterEqual(span2));
    }

    #[test]
    fn test_expr_logical_ops() {
        use Expr::*;
        do_expr_ok_test(
            "1 AND 2",
            And(Box::from(BinaryOpSpan {
                lhs: expr_integer(1, 1, 7),
                rhs: expr_integer(2, 1, 13),
                pos: lc(1, 9),
            })),
        );
        do_expr_ok_test(
            "1 OR 2",
            Or(Box::from(BinaryOpSpan {
                lhs: expr_integer(1, 1, 7),
                rhs: expr_integer(2, 1, 12),
                pos: lc(1, 9),
            })),
        );
        do_expr_ok_test(
            "1 XOR 2",
            Xor(Box::from(BinaryOpSpan {
                lhs: expr_integer(1, 1, 7),
                rhs: expr_integer(2, 1, 13),
                pos: lc(1, 9),
            })),
        );
    }

    #[test]
    fn test_expr_logical_ops_not() {
        use Expr::*;
        do_expr_ok_test(
            "NOT TRUE",
            Not(Box::from(UnaryOpSpan { expr: expr_boolean(true, 1, 11), pos: lc(1, 7) })),
        );
        do_expr_ok_test(
            "NOT 6",
            Not(Box::from(UnaryOpSpan { expr: expr_integer(6, 1, 11), pos: lc(1, 7) })),
        );
        do_expr_ok_test(
            "NOT NOT TRUE",
            Not(Box::from(UnaryOpSpan {
                expr: Not(Box::from(UnaryOpSpan {
                    expr: expr_boolean(true, 1, 15),
                    pos: lc(1, 11),
                })),
                pos: lc(1, 7),
            })),
        );
        do_expr_ok_test(
            "1 - NOT 4",
            Subtract(Box::from(BinaryOpSpan {
                lhs: expr_integer(1, 1, 7),
                rhs: Not(Box::from(UnaryOpSpan { expr: expr_integer(4, 1, 15), pos: lc(1, 11) })),
                pos: lc(1, 9),
            })),
        );
    }

    #[test]
    fn test_expr_bitwise_ops() {
        use Expr::*;
        do_expr_ok_test(
            "1 << 2",
            ShiftLeft(Box::from(BinaryOpSpan {
                lhs: expr_integer(1, 1, 7),
                rhs: expr_integer(2, 1, 12),
                pos: lc(1, 9),
            })),
        );
        do_expr_ok_test(
            "1 >> 2",
            ShiftRight(Box::from(BinaryOpSpan {
                lhs: expr_integer(1, 1, 7),
                rhs: expr_integer(2, 1, 12),
                pos: lc(1, 9),
            })),
        );
    }

    #[test]
    fn test_expr_op_priorities() {
        use Expr::*;
        do_expr_ok_test(
            "3 * (2 + 5) = (3 + 1 = 2 OR 1 = 3 XOR FALSE * \"a\")",
            Equal(Box::from(BinaryOpSpan {
                lhs: Multiply(Box::from(BinaryOpSpan {
                    lhs: expr_integer(3, 1, 7),
                    rhs: Add(Box::from(BinaryOpSpan {
                        lhs: expr_integer(2, 1, 12),
                        rhs: expr_integer(5, 1, 16),
                        pos: lc(1, 14),
                    })),
                    pos: lc(1, 9),
                })),
                rhs: Xor(Box::from(BinaryOpSpan {
                    lhs: Or(Box::from(BinaryOpSpan {
                        lhs: Equal(Box::from(BinaryOpSpan {
                            lhs: Add(Box::from(BinaryOpSpan {
                                lhs: expr_integer(3, 1, 22),
                                rhs: expr_integer(1, 1, 26),
                                pos: lc(1, 24),
                            })),
                            rhs: expr_integer(2, 1, 30),
                            pos: lc(1, 28),
                        })),
                        rhs: Equal(Box::from(BinaryOpSpan {
                            lhs: expr_integer(1, 1, 35),
                            rhs: expr_integer(3, 1, 39),
                            pos: lc(1, 37),
                        })),
                        pos: lc(1, 32),
                    })),
                    rhs: Multiply(Box::from(BinaryOpSpan {
                        lhs: expr_boolean(false, 1, 45),
                        rhs: expr_text("a", 1, 53),
                        pos: lc(1, 51),
                    })),
                    pos: lc(1, 41),
                })),
                pos: lc(1, 19),
            })),
        );
        do_expr_ok_test(
            "-1 ^ 3",
            Negate(Box::from(UnaryOpSpan {
                expr: Power(Box::from(BinaryOpSpan {
                    lhs: expr_integer(1, 1, 8),
                    rhs: expr_integer(3, 1, 12),
                    pos: lc(1, 10),
                })),
                pos: lc(1, 7),
            })),
        );
        do_expr_ok_test(
            "-(1 ^ 3)",
            Negate(Box::from(UnaryOpSpan {
                expr: Power(Box::from(BinaryOpSpan {
                    lhs: expr_integer(1, 1, 9),
                    rhs: expr_integer(3, 1, 13),
                    pos: lc(1, 11),
                })),
                pos: lc(1, 7),
            })),
        );
        do_expr_ok_test(
            "(-1) ^ 3",
            Power(Box::from(BinaryOpSpan {
                lhs: Negate(Box::from(UnaryOpSpan { expr: expr_integer(1, 1, 9), pos: lc(1, 8) })),
                rhs: expr_integer(3, 1, 14),
                pos: lc(1, 12),
            })),
        );
        do_expr_ok_test(
            "1 ^ (-3)",
            Power(Box::from(BinaryOpSpan {
                lhs: expr_integer(1, 1, 7),
                rhs: Negate(Box::from(UnaryOpSpan {
                    expr: expr_integer(3, 1, 13),
                    pos: lc(1, 12),
                })),
                pos: lc(1, 9),
            })),
        );
        do_expr_ok_test(
            "0 <> 2 >> 1",
            NotEqual(Box::from(BinaryOpSpan {
                lhs: expr_integer(0, 1, 7),
                rhs: ShiftRight(Box::from(BinaryOpSpan {
                    lhs: expr_integer(2, 1, 12),
                    rhs: expr_integer(1, 1, 17),
                    pos: lc(1, 14),
                })),
                pos: lc(1, 9),
            })),
        );
    }

    #[test]
    fn test_expr_numeric_signs() {
        use Expr::*;

        do_expr_ok_test(
            "-a",
            Negate(Box::from(UnaryOpSpan {
                expr: expr_symbol(VarRef::new("a", None), 1, 8),
                pos: lc(1, 7),
            })),
        );

        do_expr_ok_test(
            "1 - -3",
            Subtract(Box::from(BinaryOpSpan {
                lhs: expr_integer(1, 1, 7),
                rhs: Negate(Box::from(UnaryOpSpan {
                    expr: expr_integer(3, 1, 12),
                    pos: lc(1, 11),
                })),
                pos: lc(1, 9),
            })),
        );
        do_expr_ok_test(
            "-1 - 3",
            Subtract(Box::from(BinaryOpSpan {
                lhs: Negate(Box::from(UnaryOpSpan { expr: expr_integer(1, 1, 8), pos: lc(1, 7) })),
                rhs: expr_integer(3, 1, 12),
                pos: lc(1, 10),
            })),
        );
        do_expr_ok_test(
            "5 + -1",
            Add(Box::from(BinaryOpSpan {
                lhs: expr_integer(5, 1, 7),
                rhs: Negate(Box::from(UnaryOpSpan {
                    expr: expr_integer(1, 1, 12),
                    pos: lc(1, 11),
                })),
                pos: lc(1, 9),
            })),
        );
        do_expr_ok_test(
            "-5 + 1",
            Add(Box::from(BinaryOpSpan {
                lhs: Negate(Box::from(UnaryOpSpan { expr: expr_integer(5, 1, 8), pos: lc(1, 7) })),
                rhs: expr_integer(1, 1, 12),
                pos: lc(1, 10),
            })),
        );
        do_expr_ok_test(
            "NOT -3",
            Not(Box::from(UnaryOpSpan {
                expr: Negate(Box::from(UnaryOpSpan {
                    expr: expr_integer(3, 1, 12),
                    pos: lc(1, 11),
                })),
                pos: lc(1, 7),
            })),
        );

        do_expr_ok_test(
            "1.0 - -3.5",
            Subtract(Box::from(BinaryOpSpan {
                lhs: expr_double(1.0, 1, 7),
                rhs: Negate(Box::from(UnaryOpSpan {
                    expr: expr_double(3.5, 1, 14),
                    pos: lc(1, 13),
                })),
                pos: lc(1, 11),
            })),
        );
        do_expr_ok_test(
            "5.12 + -0.50",
            Add(Box::from(BinaryOpSpan {
                lhs: expr_double(5.12, 1, 7),
                rhs: Negate(Box::from(UnaryOpSpan {
                    expr: expr_double(0.50, 1, 15),
                    pos: lc(1, 14),
                })),
                pos: lc(1, 12),
            })),
        );
        do_expr_ok_test(
            "NOT -3",
            Not(Box::from(UnaryOpSpan {
                expr: Negate(Box::from(UnaryOpSpan {
                    expr: expr_integer(3, 1, 12),
                    pos: lc(1, 11),
                })),
                pos: lc(1, 7),
            })),
        );
    }

    #[test]
    fn test_expr_functions_variadic() {
        use Expr::*;
        do_expr_ok_test(
            "zero()",
            Call(CallSpan { vref: VarRef::new("zero", None), vref_pos: lc(1, 7), args: vec![] }),
        );
        do_expr_ok_test(
            "one%(1)",
            Call(CallSpan {
                vref: VarRef::new("one", Some(ExprType::Integer)),
                vref_pos: lc(1, 7),
                args: vec![ArgSpan {
                    expr: Some(expr_integer(1, 1, 12)),
                    sep: ArgSep::End,
                    sep_pos: lc(1, 13),
                }],
            }),
        );
        do_expr_ok_test(
            "many$(3, \"x\", TRUE)",
            Call(CallSpan {
                vref: VarRef::new("many", Some(ExprType::Text)),
                vref_pos: lc(1, 7),
                args: vec![
                    ArgSpan {
                        expr: Some(expr_integer(3, 1, 13)),
                        sep: ArgSep::Long,
                        sep_pos: lc(1, 14),
                    },
                    ArgSpan {
                        expr: Some(expr_text("x", 1, 16)),
                        sep: ArgSep::Long,
                        sep_pos: lc(1, 19),
                    },
                    ArgSpan {
                        expr: Some(expr_boolean(true, 1, 21)),
                        sep: ArgSep::End,
                        sep_pos: lc(1, 25),
                    },
                ],
            }),
        );
    }

    #[test]
    fn test_expr_functions_nested() {
        use Expr::*;
        do_expr_ok_test(
            "consecutive(parenthesis())",
            Call(CallSpan {
                vref: VarRef::new("consecutive", None),
                vref_pos: lc(1, 7),
                args: vec![ArgSpan {
                    expr: Some(Call(CallSpan {
                        vref: VarRef::new("parenthesis", None),
                        vref_pos: lc(1, 19),
                        args: vec![],
                    })),
                    sep: ArgSep::End,
                    sep_pos: lc(1, 32),
                }],
            }),
        );
        do_expr_ok_test(
            "outer?(1, inner1(2, 3), 4, inner2(), 5)",
            Call(CallSpan {
                vref: VarRef::new("outer", Some(ExprType::Boolean)),
                vref_pos: lc(1, 7),
                args: vec![
                    ArgSpan {
                        expr: Some(expr_integer(1, 1, 14)),
                        sep: ArgSep::Long,
                        sep_pos: lc(1, 15),
                    },
                    ArgSpan {
                        expr: Some(Call(CallSpan {
                            vref: VarRef::new("inner1", None),
                            vref_pos: lc(1, 17),
                            args: vec![
                                ArgSpan {
                                    expr: Some(expr_integer(2, 1, 24)),
                                    sep: ArgSep::Long,
                                    sep_pos: lc(1, 25),
                                },
                                ArgSpan {
                                    expr: Some(expr_integer(3, 1, 27)),
                                    sep: ArgSep::End,
                                    sep_pos: lc(1, 28),
                                },
                            ],
                        })),
                        sep: ArgSep::Long,
                        sep_pos: lc(1, 29),
                    },
                    ArgSpan {
                        expr: Some(expr_integer(4, 1, 31)),
                        sep: ArgSep::Long,
                        sep_pos: lc(1, 32),
                    },
                    ArgSpan {
                        expr: Some(Call(CallSpan {
                            vref: VarRef::new("inner2", None),
                            vref_pos: lc(1, 34),
                            args: vec![],
                        })),
                        sep: ArgSep::Long,
                        sep_pos: lc(1, 42),
                    },
                    ArgSpan {
                        expr: Some(expr_integer(5, 1, 44)),
                        sep: ArgSep::End,
                        sep_pos: lc(1, 45),
                    },
                ],
            }),
        );
    }

    #[test]
    fn test_expr_functions_and_ops() {
        use Expr::*;
        do_expr_ok_test(
            "b AND ask?(34 + 15, ask(1, FALSE), -5)",
            And(Box::from(BinaryOpSpan {
                lhs: expr_symbol(VarRef::new("b".to_owned(), None), 1, 7),
                rhs: Call(CallSpan {
                    vref: VarRef::new("ask", Some(ExprType::Boolean)),
                    vref_pos: lc(1, 13),
                    args: vec![
                        ArgSpan {
                            expr: Some(Add(Box::from(BinaryOpSpan {
                                lhs: expr_integer(34, 1, 18),
                                rhs: expr_integer(15, 1, 23),
                                pos: lc(1, 21),
                            }))),
                            sep: ArgSep::Long,
                            sep_pos: lc(1, 25),
                        },
                        ArgSpan {
                            expr: Some(Call(CallSpan {
                                vref: VarRef::new("ask", None),
                                vref_pos: lc(1, 27),
                                args: vec![
                                    ArgSpan {
                                        expr: Some(expr_integer(1, 1, 31)),
                                        sep: ArgSep::Long,
                                        sep_pos: lc(1, 32),
                                    },
                                    ArgSpan {
                                        expr: Some(expr_boolean(false, 1, 34)),
                                        sep: ArgSep::End,
                                        sep_pos: lc(1, 39),
                                    },
                                ],
                            })),
                            sep: ArgSep::Long,
                            sep_pos: lc(1, 40),
                        },
                        ArgSpan {
                            expr: Some(Negate(Box::from(UnaryOpSpan {
                                expr: expr_integer(5, 1, 43),
                                pos: lc(1, 42),
                            }))),
                            sep: ArgSep::End,
                            sep_pos: lc(1, 44),
                        },
                    ],
                }),
                pos: lc(1, 9),
            })),
        );
    }

    #[test]
    fn test_expr_functions_not_confused_with_symbols() {
        use Expr::*;
        let iref = VarRef::new("i", None);
        let jref = VarRef::new("j", None);
        do_expr_ok_test(
            "i = 0 OR i = (j - 1)",
            Or(Box::from(BinaryOpSpan {
                lhs: Equal(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iref.clone(), 1, 7),
                    rhs: expr_integer(0, 1, 11),
                    pos: lc(1, 9),
                })),
                rhs: Equal(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iref, 1, 16),
                    rhs: Subtract(Box::from(BinaryOpSpan {
                        lhs: expr_symbol(jref, 1, 21),
                        rhs: expr_integer(1, 1, 25),
                        pos: lc(1, 23),
                    })),
                    pos: lc(1, 18),
                })),
                pos: lc(1, 13),
            })),
        );
    }

    #[test]
    fn test_expr_errors() {
        // Note that all column numbers in the errors below are offset by 6 (due to "PRINT ") as
        // that's what the do_expr_error_test function is prefixing to the given strings.

        do_expr_error_test("+3", "1:7: Not enough values to apply operator");
        do_expr_error_test("2 + * 3", "1:9: Not enough values to apply operator");
        do_expr_error_test("(2(3))", "1:9: Unexpected ( in expression");
        do_expr_error_test("((3)2)", "1:11: Unexpected value in expression");
        do_expr_error_test("2 3", "1:9: Unexpected value in expression");

        do_expr_error_test("(", "1:8: Missing expression");

        do_expr_error_test(")", "1:7: Expected comma, semicolon, or end of statement");
        do_expr_error_test("(()", "1:10: Missing expression");
        do_expr_error_test("())", "1:7: Expected expression");
        do_expr_error_test("3 + (2 + 1) + (4 - 5", "1:21: Unbalanced parenthesis");
        do_expr_error_test(
            "3 + 2 + 1) + (4 - 5)",
            "1:16: Expected comma, semicolon, or end of statement",
        );

        do_expr_error_test("foo(,)", "1:11: Missing expression");
        do_expr_error_test("foo(, 3)", "1:11: Missing expression");
        do_expr_error_test("foo(3, )", "1:14: Missing expression");
        do_expr_error_test("foo(3, , 4)", "1:14: Missing expression");
        // TODO(jmmv): These are not the best error messages...
        do_expr_error_test("(,)", "1:8: Missing expression");
        do_expr_error_test("(3, 4)", "1:7: Expected expression");
        do_expr_error_test("((), ())", "1:10: Missing expression");

        // TODO(jmmv): This succeeds because `PRINT` is interned as a `Token::Symbol` so the
        // expression parser sees it as a variable reference... but this should probably fail.
        // Would need to intern builtin call names as a separate token to catch this, but that
        // also means that the lexer must be aware of builtin call names upfront.
        use Expr::*;
        do_expr_ok_test(
            "1 + PRINT",
            Add(Box::from(BinaryOpSpan {
                lhs: expr_integer(1, 1, 7),
                rhs: expr_symbol(VarRef::new("PRINT", None), 1, 11),
                pos: lc(1, 9),
            })),
        );
    }

    #[test]
    fn test_expr_errors_due_to_keywords() {
        for kw in &[
            "BOOLEAN", "CASE", "DATA", "DIM", "DOUBLE", "ELSEIF", "END", "ERROR", "EXIT", "FOR",
            "GOSUB", "GOTO", "IF", "IS", "INTEGER", "LOOP", "NEXT", "ON", "RESUME", "RETURN",
            "SELECT", "STRING", "UNTIL", "WEND", "WHILE",
        ] {
            do_expr_error_test(
                &format!("2 + {} - 1", kw),
                "1:11: Unexpected keyword in expression",
            );
        }
    }

    #[test]
    fn test_if_empty_branches() {
        do_ok_test(
            "IF 1 THEN\nEND IF",
            &[Statement::If(IfSpan {
                branches: vec![IfBranchSpan { guard: expr_integer(1, 1, 4), body: vec![] }],
            })],
        );
        do_ok_test(
            "IF 1 THEN\nREM Some comment to skip over\n\nEND IF",
            &[Statement::If(IfSpan {
                branches: vec![IfBranchSpan { guard: expr_integer(1, 1, 4), body: vec![] }],
            })],
        );
        do_ok_test(
            "IF 1 THEN\nELSEIF 2 THEN\nEND IF",
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan { guard: expr_integer(1, 1, 4), body: vec![] },
                    IfBranchSpan { guard: expr_integer(2, 2, 8), body: vec![] },
                ],
            })],
        );
        do_ok_test(
            "IF 1 THEN\nELSEIF 2 THEN\nELSE\nEND IF",
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan { guard: expr_integer(1, 1, 4), body: vec![] },
                    IfBranchSpan { guard: expr_integer(2, 2, 8), body: vec![] },
                    IfBranchSpan { guard: expr_boolean(true, 3, 1), body: vec![] },
                ],
            })],
        );
        do_ok_test(
            "IF 1 THEN\nELSE\nEND IF",
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan { guard: expr_integer(1, 1, 4), body: vec![] },
                    IfBranchSpan { guard: expr_boolean(true, 2, 1), body: vec![] },
                ],
            })],
        );
    }

    /// Helper to instantiate a trivial `Statement::BuiltinCall` that has no arguments.
    fn make_bare_builtin_call(name: &str, line: usize, col: usize) -> Statement {
        Statement::Call(CallSpan {
            vref: VarRef::new(name, None),
            vref_pos: LineCol { line, col },
            args: vec![],
        })
    }

    #[test]
    fn test_if_with_one_statement_or_empty_lines() {
        do_ok_test(
            "IF 1 THEN\nPRINT\nEND IF",
            &[Statement::If(IfSpan {
                branches: vec![IfBranchSpan {
                    guard: expr_integer(1, 1, 4),
                    body: vec![make_bare_builtin_call("PRINT", 2, 1)],
                }],
            })],
        );
        do_ok_test(
            "IF 1 THEN\nREM foo\nELSEIF 2 THEN\nPRINT\nEND IF",
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan { guard: expr_integer(1, 1, 4), body: vec![] },
                    IfBranchSpan {
                        guard: expr_integer(2, 3, 8),
                        body: vec![make_bare_builtin_call("PRINT", 4, 1)],
                    },
                ],
            })],
        );
        do_ok_test(
            "IF 1 THEN\nELSEIF 2 THEN\nELSE\n\nPRINT\nEND IF",
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan { guard: expr_integer(1, 1, 4), body: vec![] },
                    IfBranchSpan { guard: expr_integer(2, 2, 8), body: vec![] },
                    IfBranchSpan {
                        guard: expr_boolean(true, 3, 1),
                        body: vec![make_bare_builtin_call("PRINT", 5, 1)],
                    },
                ],
            })],
        );
        do_ok_test(
            "IF 1 THEN\n\n\nELSE\nPRINT\nEND IF",
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan { guard: expr_integer(1, 1, 4), body: vec![] },
                    IfBranchSpan {
                        guard: expr_boolean(true, 4, 1),
                        body: vec![make_bare_builtin_call("PRINT", 5, 1)],
                    },
                ],
            })],
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
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan {
                        guard: expr_integer(1, 2, 16),
                        body: vec![
                            make_bare_builtin_call("A", 3, 17),
                            make_bare_builtin_call("B", 4, 17),
                        ],
                    },
                    IfBranchSpan {
                        guard: expr_integer(2, 5, 20),
                        body: vec![
                            make_bare_builtin_call("C", 6, 17),
                            make_bare_builtin_call("D", 7, 17),
                        ],
                    },
                    IfBranchSpan {
                        guard: expr_integer(3, 8, 20),
                        body: vec![
                            make_bare_builtin_call("E", 9, 17),
                            make_bare_builtin_call("F", 10, 17),
                        ],
                    },
                    IfBranchSpan {
                        guard: expr_boolean(true, 11, 13),
                        body: vec![
                            make_bare_builtin_call("G", 12, 17),
                            make_bare_builtin_call("H", 13, 17),
                        ],
                    },
                ],
            })],
        );
    }

    #[test]
    fn test_if_with_interleaved_end_complex() {
        let code = r#"
            IF 1 THEN 'First branch
                A
                END
                B
            ELSEIF 2 THEN 'Second branch
                C
                END 8
                D
            ELSEIF 3 THEN 'Third branch
                E
                END
                F
            ELSE 'Last branch
                G
                END 5
                H
            END IF
        "#;
        do_ok_test(
            code,
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan {
                        guard: expr_integer(1, 2, 16),
                        body: vec![
                            make_bare_builtin_call("A", 3, 17),
                            Statement::End(EndSpan { code: None }),
                            make_bare_builtin_call("B", 5, 17),
                        ],
                    },
                    IfBranchSpan {
                        guard: expr_integer(2, 6, 20),
                        body: vec![
                            make_bare_builtin_call("C", 7, 17),
                            Statement::End(EndSpan {
                                code: Some(Expr::Integer(IntegerSpan { value: 8, pos: lc(8, 21) })),
                            }),
                            make_bare_builtin_call("D", 9, 17),
                        ],
                    },
                    IfBranchSpan {
                        guard: expr_integer(3, 10, 20),
                        body: vec![
                            make_bare_builtin_call("E", 11, 17),
                            Statement::End(EndSpan { code: None }),
                            make_bare_builtin_call("F", 13, 17),
                        ],
                    },
                    IfBranchSpan {
                        guard: expr_boolean(true, 14, 13),
                        body: vec![
                            make_bare_builtin_call("G", 15, 17),
                            Statement::End(EndSpan {
                                code: Some(Expr::Integer(IntegerSpan {
                                    value: 5,
                                    pos: lc(16, 21),
                                })),
                            }),
                            make_bare_builtin_call("H", 17, 17),
                        ],
                    },
                ],
            })],
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
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan {
                        guard: expr_integer(1, 2, 16),
                        body: vec![make_bare_builtin_call("A", 3, 17)],
                    },
                    IfBranchSpan {
                        guard: expr_integer(2, 4, 20),
                        body: vec![Statement::If(IfSpan {
                            branches: vec![IfBranchSpan {
                                guard: expr_integer(3, 5, 20),
                                body: vec![make_bare_builtin_call("B", 6, 21)],
                            }],
                        })],
                    },
                ],
            })],
        );
    }

    #[test]
    fn test_if_errors() {
        do_error_test("IF\n", "1:3: No expression in IF statement");
        do_error_test("IF 3 + 1", "1:9: No THEN in IF statement");
        do_error_test("IF 3 + 1\n", "1:9: No THEN in IF statement");
        do_error_test("IF 3 + 1 PRINT foo\n", "1:10: Unexpected value in expression");
        do_error_test("IF 3 + 1\nPRINT foo\n", "1:9: No THEN in IF statement");
        do_error_test("IF 3 + 1 THEN", "1:1: IF without END IF");

        do_error_test("IF 1 THEN\n", "1:1: IF without END IF");
        do_error_test("IF 1 THEN\nELSEIF 1 THEN\n", "1:1: IF without END IF");
        do_error_test("IF 1 THEN\nELSE\n", "1:1: IF without END IF");
        do_error_test("REM\n   IF 1 THEN\n", "2:4: IF without END IF");

        do_error_test("IF 1 THEN\nELSEIF\n", "2:7: No expression in ELSEIF statement");
        do_error_test("IF 1 THEN\nELSEIF 3 + 1", "2:13: No THEN in ELSEIF statement");
        do_error_test("IF 1 THEN\nELSEIF 3 + 1\n", "2:13: No THEN in ELSEIF statement");
        do_error_test(
            "IF 1 THEN\nELSEIF 3 + 1 PRINT foo\n",
            "2:14: Unexpected value in expression",
        );
        do_error_test("IF 1 THEN\nELSEIF 3 + 1\nPRINT foo\n", "2:13: No THEN in ELSEIF statement");
        do_error_test("IF 1 THEN\nELSEIF 3 + 1 THEN", "2:18: Expecting newline after THEN");

        do_error_test("IF 1 THEN\nELSE", "2:5: Expecting newline after ELSE");
        do_error_test("IF 1 THEN\nELSE foo", "2:6: Expecting newline after ELSE");

        do_error_test("IF 1 THEN\nEND", "1:1: IF without END IF");
        do_error_test("IF 1 THEN\nEND\n", "1:1: IF without END IF");
        do_error_test("IF 1 THEN\nEND IF foo", "2:8: Expected newline but found foo");
        do_error_test("IF 1 THEN\nEND SELECT\n", "2:1: END SELECT without SELECT");
        do_error_test("IF 1 THEN\nEND SELECT\nEND IF\n", "2:1: END SELECT without SELECT");

        do_error_test(
            "IF 1 THEN\nELSE\nELSEIF 2 THEN\nEND IF",
            "3:1: Unexpected ELSEIF after ELSE",
        );
        do_error_test("IF 1 THEN\nELSE\nELSE\nEND IF", "3:1: Duplicate ELSE after ELSE");

        do_error_test_no_reset("ELSEIF 1 THEN\nEND IF", "1:1: Unexpected ELSEIF in statement");
        do_error_test_no_reset("ELSE 1\nEND IF", "1:1: Unexpected ELSE in statement");

        do_error_test("IF 1 THEN\nEND 3 IF", "2:7: Unexpected keyword in expression");
        do_error_test("END 3 IF", "1:7: Unexpected keyword in expression");
        do_error_test("END IF", "1:1: END IF without IF");

        do_error_test("IF TRUE THEN PRINT ELSE ELSE", "1:25: Unexpected ELSE in uniline IF branch");
    }

    #[test]
    fn test_if_uniline_then() {
        do_ok_test(
            "IF 1 THEN A",
            &[Statement::If(IfSpan {
                branches: vec![IfBranchSpan {
                    guard: expr_integer(1, 1, 4),
                    body: vec![make_bare_builtin_call("A", 1, 11)],
                }],
            })],
        );
    }

    #[test]
    fn test_if_uniline_then_else() {
        do_ok_test(
            "IF 1 THEN A ELSE B",
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan {
                        guard: expr_integer(1, 1, 4),
                        body: vec![make_bare_builtin_call("A", 1, 11)],
                    },
                    IfBranchSpan {
                        guard: expr_boolean(true, 1, 13),
                        body: vec![make_bare_builtin_call("B", 1, 18)],
                    },
                ],
            })],
        );
    }

    #[test]
    fn test_if_uniline_empty_then_else() {
        do_ok_test(
            "IF 1 THEN ELSE B",
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan { guard: expr_integer(1, 1, 4), body: vec![] },
                    IfBranchSpan {
                        guard: expr_boolean(true, 1, 11),
                        body: vec![make_bare_builtin_call("B", 1, 16)],
                    },
                ],
            })],
        );
    }

    #[test]
    fn test_if_uniline_then_empty_else() {
        do_ok_test(
            "IF 1 THEN A ELSE",
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan {
                        guard: expr_integer(1, 1, 4),
                        body: vec![make_bare_builtin_call("A", 1, 11)],
                    },
                    IfBranchSpan { guard: expr_boolean(true, 1, 13), body: vec![] },
                ],
            })],
        );
    }

    #[test]
    fn test_if_uniline_empty_then_empty_else() {
        do_ok_test(
            "IF 1 THEN ELSE",
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan { guard: expr_integer(1, 1, 4), body: vec![] },
                    IfBranchSpan { guard: expr_boolean(true, 1, 11), body: vec![] },
                ],
            })],
        );
    }

    /// Performs a test of a uniline if statement followed by a specific allowed statement type.
    ///
    /// `text` is the literal statement to append to the if statement, and `stmt` contains the
    /// expected parsed statement.  The expected positions for the parsed statement are line 1 and
    /// columns offset by 11 characters.
    fn do_if_uniline_allowed_test(text: &str, stmt: Statement) {
        do_ok_test(
            &format!("IF 1 THEN {}\nZ", text),
            &[
                Statement::If(IfSpan {
                    branches: vec![IfBranchSpan { guard: expr_integer(1, 1, 4), body: vec![stmt] }],
                }),
                make_bare_builtin_call("Z", 2, 1),
            ],
        );
    }

    #[test]
    fn test_if_uniline_allowed_data() {
        do_if_uniline_allowed_test("DATA", Statement::Data(DataSpan { values: vec![None] }));
    }

    #[test]
    fn test_if_uniline_allowed_end() {
        do_if_uniline_allowed_test(
            "END 8",
            Statement::End(EndSpan { code: Some(expr_integer(8, 1, 15)) }),
        );
    }

    #[test]
    fn test_if_uniline_allowed_exit() {
        do_if_uniline_allowed_test("EXIT DO", Statement::ExitDo(ExitSpan { pos: lc(1, 11) }));

        do_error_test("IF 1 THEN EXIT", "1:15: Expecting DO or FOR after EXIT");
    }

    #[test]
    fn test_if_uniline_allowed_gosub() {
        do_if_uniline_allowed_test(
            "GOSUB 10",
            Statement::Gosub(GotoSpan { target: "10".to_owned(), target_pos: lc(1, 17) }),
        );

        do_error_test("IF 1 THEN GOSUB", "1:16: Expected label name after GOSUB");
    }

    #[test]
    fn test_if_uniline_allowed_goto() {
        do_if_uniline_allowed_test(
            "GOTO 10",
            Statement::Goto(GotoSpan { target: "10".to_owned(), target_pos: lc(1, 16) }),
        );

        do_error_test("IF 1 THEN GOTO", "1:15: Expected label name after GOTO");
    }

    #[test]
    fn test_if_uniline_allowed_on_error() {
        do_if_uniline_allowed_test(
            "ON ERROR RESUME NEXT",
            Statement::OnError(OnErrorSpan::ResumeNext),
        );

        do_error_test("IF 1 THEN ON", "1:13: Expected ERROR after ON");
    }

    #[test]
    fn test_if_uniline_allowed_return() {
        do_if_uniline_allowed_test("RETURN", Statement::Return(ReturnSpan { pos: lc(1, 11) }));
    }

    #[test]
    fn test_if_uniline_allowed_assignment() {
        do_if_uniline_allowed_test(
            "a = 3",
            Statement::Assignment(AssignmentSpan {
                vref: VarRef::new("a", None),
                vref_pos: lc(1, 11),
                expr: expr_integer(3, 1, 15),
            }),
        );
    }

    #[test]
    fn test_if_uniline_allowed_array_assignment() {
        do_if_uniline_allowed_test(
            "a(3) = 5",
            Statement::ArrayAssignment(ArrayAssignmentSpan {
                vref: VarRef::new("a", None),
                vref_pos: lc(1, 11),
                subscripts: vec![expr_integer(3, 1, 13)],
                expr: expr_integer(5, 1, 18),
            }),
        );
    }

    #[test]
    fn test_if_uniline_allowed_builtin_call() {
        do_if_uniline_allowed_test(
            "a 0",
            Statement::Call(CallSpan {
                vref: VarRef::new("A", None),
                vref_pos: lc(1, 11),
                args: vec![ArgSpan {
                    expr: Some(expr_integer(0, 1, 13)),
                    sep: ArgSep::End,
                    sep_pos: lc(1, 14),
                }],
            }),
        );
    }

    #[test]
    fn test_if_uniline_unallowed_statements() {
        for t in ["DIM", "DO", "IF", "FOR", "10", "@label", "SELECT", "WHILE"] {
            do_error_test(
                &format!("IF 1 THEN {}", t),
                &format!("1:11: Unexpected {} in uniline IF branch", t),
            );
        }
    }

    #[test]
    fn test_for_empty() {
        let auto_iter = VarRef::new("i", None);
        do_ok_test(
            "FOR i = 1 TO 10\nNEXT",
            &[Statement::For(ForSpan {
                iter: auto_iter.clone(),
                iter_pos: lc(1, 5),
                iter_double: false,
                start: expr_integer(1, 1, 9),
                end: Expr::LessEqual(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(auto_iter.clone(), 1, 5),
                    rhs: expr_integer(10, 1, 14),
                    pos: lc(1, 11),
                })),
                next: Expr::Add(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(auto_iter, 1, 5),
                    rhs: expr_integer(1, 1, 16),
                    pos: lc(1, 11),
                })),
                body: vec![],
            })],
        );

        let typed_iter = VarRef::new("d", Some(ExprType::Double));
        do_ok_test(
            "FOR d# = 1.0 TO 10.2\nREM Nothing to do\nNEXT",
            &[Statement::For(ForSpan {
                iter: typed_iter.clone(),
                iter_pos: lc(1, 5),
                iter_double: false,
                start: expr_double(1.0, 1, 10),
                end: Expr::LessEqual(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(typed_iter.clone(), 1, 5),
                    rhs: expr_double(10.2, 1, 17),
                    pos: lc(1, 14),
                })),
                next: Expr::Add(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(typed_iter, 1, 5),
                    rhs: expr_integer(1, 1, 21),
                    pos: lc(1, 14),
                })),
                body: vec![],
            })],
        );
    }

    #[test]
    fn test_for_incrementing() {
        let iter = VarRef::new("i", None);
        do_ok_test(
            "FOR i = 0 TO 5\nA\nB\nNEXT",
            &[Statement::For(ForSpan {
                iter: iter.clone(),
                iter_pos: lc(1, 5),
                iter_double: false,
                start: expr_integer(0, 1, 9),
                end: Expr::LessEqual(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iter.clone(), 1, 5),
                    rhs: expr_integer(5, 1, 14),
                    pos: lc(1, 11),
                })),
                next: Expr::Add(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iter, 1, 5),
                    rhs: expr_integer(1, 1, 15),
                    pos: lc(1, 11),
                })),
                body: vec![make_bare_builtin_call("A", 2, 1), make_bare_builtin_call("B", 3, 1)],
            })],
        );
    }

    #[test]
    fn test_for_incrementing_with_step() {
        let iter = VarRef::new("i", None);
        do_ok_test(
            "FOR i = 0 TO 5 STEP 2\nA\nNEXT",
            &[Statement::For(ForSpan {
                iter: iter.clone(),
                iter_pos: lc(1, 5),
                iter_double: false,
                start: expr_integer(0, 1, 9),
                end: Expr::LessEqual(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iter.clone(), 1, 5),
                    rhs: expr_integer(5, 1, 14),
                    pos: lc(1, 11),
                })),
                next: Expr::Add(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iter, 1, 5),
                    rhs: expr_integer(2, 1, 21),
                    pos: lc(1, 11),
                })),
                body: vec![make_bare_builtin_call("A", 2, 1)],
            })],
        );

        let iter = VarRef::new("i", None);
        do_ok_test(
            "FOR i = 0 TO 5 STEP 2.5\nA\nNEXT",
            &[Statement::For(ForSpan {
                iter: iter.clone(),
                iter_pos: lc(1, 5),
                iter_double: true,
                start: expr_integer(0, 1, 9),
                end: Expr::LessEqual(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iter.clone(), 1, 5),
                    rhs: expr_integer(5, 1, 14),
                    pos: lc(1, 11),
                })),
                next: Expr::Add(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iter, 1, 5),
                    rhs: expr_double(2.5, 1, 21),
                    pos: lc(1, 11),
                })),
                body: vec![make_bare_builtin_call("A", 2, 1)],
            })],
        );
    }

    #[test]
    fn test_for_decrementing_with_step() {
        let iter = VarRef::new("i", None);
        do_ok_test(
            "FOR i = 5 TO 0 STEP -1\nA\nNEXT",
            &[Statement::For(ForSpan {
                iter: iter.clone(),
                iter_pos: lc(1, 5),
                iter_double: false,
                start: expr_integer(5, 1, 9),
                end: Expr::GreaterEqual(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iter.clone(), 1, 5),
                    rhs: expr_integer(0, 1, 14),
                    pos: lc(1, 11),
                })),
                next: Expr::Add(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iter, 1, 5),
                    rhs: expr_integer(-1, 1, 22),
                    pos: lc(1, 11),
                })),
                body: vec![make_bare_builtin_call("A", 2, 1)],
            })],
        );

        let iter = VarRef::new("i", None);
        do_ok_test(
            "FOR i = 5 TO 0 STEP -1.2\nA\nNEXT",
            &[Statement::For(ForSpan {
                iter: iter.clone(),
                iter_pos: lc(1, 5),
                iter_double: true,
                start: expr_integer(5, 1, 9),
                end: Expr::GreaterEqual(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iter.clone(), 1, 5),
                    rhs: expr_integer(0, 1, 14),
                    pos: lc(1, 11),
                })),
                next: Expr::Add(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iter, 1, 5),
                    rhs: expr_double(-1.2, 1, 22),
                    pos: lc(1, 11),
                })),
                body: vec![make_bare_builtin_call("A", 2, 1)],
            })],
        );
    }

    #[test]
    fn test_for_errors() {
        do_error_test("FOR\n", "1:4: No iterator name in FOR statement");
        do_error_test("FOR =\n", "1:5: No iterator name in FOR statement");
        do_error_test(
            "FOR a$\n",
            "1:5: Iterator name in FOR statement must be a numeric reference",
        );

        do_error_test("FOR d#\n", "1:7: No equal sign in FOR statement");
        do_error_test("FOR i 3\n", "1:7: No equal sign in FOR statement");
        do_error_test("FOR i = TO\n", "1:9: No start expression in FOR statement");
        do_error_test("FOR i = NEXT\n", "1:9: Unexpected keyword in expression");

        do_error_test("FOR i = 3 STEP\n", "1:11: No TO in FOR statement");
        do_error_test("FOR i = 3 TO STEP\n", "1:14: No end expression in FOR statement");
        do_error_test("FOR i = 3 TO NEXT\n", "1:14: Unexpected keyword in expression");

        do_error_test("FOR i = 3 TO 1 STEP a\n", "1:21: STEP needs a literal number");
        do_error_test("FOR i = 3 TO 1 STEP -a\n", "1:22: STEP needs a literal number");
        do_error_test("FOR i = 3 TO 1 STEP NEXT\n", "1:21: STEP needs a literal number");
        do_error_test("FOR i = 3 TO 1 STEP 0\n", "1:21: Infinite FOR loop; STEP cannot be 0");
        do_error_test("FOR i = 3 TO 1 STEP 0.0\n", "1:21: Infinite FOR loop; STEP cannot be 0");

        do_error_test("FOR i = 3 TO 1", "1:15: Expecting newline after FOR");
        do_error_test("FOR i = 1 TO 3 STEP 1", "1:22: Expecting newline after FOR");
        do_error_test("FOR i = 3 TO 1 STEP -1", "1:23: Expecting newline after FOR");

        do_error_test("    FOR i = 0 TO 10\nPRINT i\n", "1:5: FOR without NEXT");
    }

    #[test]
    fn test_function_empty() {
        do_ok_test(
            "FUNCTION foo$\nEND FUNCTION",
            &[Statement::Callable(CallableSpan {
                name: VarRef::new("foo", Some(ExprType::Text)),
                name_pos: lc(1, 10),
                params: vec![],
                body: vec![],
                end_pos: lc(2, 1),
            })],
        );
    }

    #[test]
    fn test_function_some_content() {
        do_ok_test(
            r#"
                FUNCTION foo$
                    A
                    END
                    END 8
                    B
                END FUNCTION
            "#,
            &[Statement::Callable(CallableSpan {
                name: VarRef::new("foo", Some(ExprType::Text)),
                name_pos: lc(2, 26),
                params: vec![],
                body: vec![
                    make_bare_builtin_call("A", 3, 21),
                    Statement::End(EndSpan { code: None }),
                    Statement::End(EndSpan {
                        code: Some(Expr::Integer(IntegerSpan { value: 8, pos: lc(5, 25) })),
                    }),
                    make_bare_builtin_call("B", 6, 21),
                ],
                end_pos: lc(7, 17),
            })],
        );
    }

    #[test]
    fn test_function_one_param() {
        do_ok_test(
            "FUNCTION foo$(x)\nEND FUNCTION",
            &[Statement::Callable(CallableSpan {
                name: VarRef::new("foo", Some(ExprType::Text)),
                name_pos: lc(1, 10),
                params: vec![VarRef::new("x", None)],
                body: vec![],
                end_pos: lc(2, 1),
            })],
        );
    }

    #[test]
    fn test_function_multiple_params() {
        do_ok_test(
            "FUNCTION foo$(x$, y, z AS BOOLEAN)\nEND FUNCTION",
            &[Statement::Callable(CallableSpan {
                name: VarRef::new("foo", Some(ExprType::Text)),
                name_pos: lc(1, 10),
                params: vec![
                    VarRef::new("x", Some(ExprType::Text)),
                    VarRef::new("y", None),
                    VarRef::new("z", Some(ExprType::Boolean)),
                ],
                body: vec![],
                end_pos: lc(2, 1),
            })],
        );
    }

    #[test]
    fn test_function_errors() {
        do_error_test("FUNCTION", "1:9: Expected a function name after FUNCTION");
        do_error_test("FUNCTION foo", "1:13: Expected newline after FUNCTION name");
        do_error_test("FUNCTION foo 3", "1:14: Expected newline after FUNCTION name");
        do_error_test("FUNCTION foo\nEND", "1:1: FUNCTION without END FUNCTION");
        do_error_test("FUNCTION foo\nEND IF", "2:1: END IF without IF");
        do_error_test("FUNCTION foo\nEND SUB", "2:1: END SUB without SUB");
        do_error_test(
            "FUNCTION foo\nFUNCTION bar\nEND FUNCTION\nEND FUNCTION",
            "2:1: Cannot nest FUNCTION or SUB definitions",
        );
        do_error_test(
            "FUNCTION foo\nSUB bar\nEND SUB\nEND FUNCTION",
            "2:1: Cannot nest FUNCTION or SUB definitions",
        );
        do_error_test("FUNCTION foo (", "1:15: Expected a parameter name");
        do_error_test("FUNCTION foo ()", "1:15: Expected a parameter name");
        do_error_test("FUNCTION foo (,)", "1:15: Expected a parameter name");
        do_error_test("FUNCTION foo (a,)", "1:17: Expected a parameter name");
        do_error_test("FUNCTION foo (,b)", "1:15: Expected a parameter name");
        do_error_test("FUNCTION foo (a AS)", "1:19: Invalid type name ) in AS type definition");
        do_error_test(
            "FUNCTION foo (a INTEGER)",
            "1:17: Expected comma, AS, or end of parameters list",
        );
        do_error_test("FUNCTION foo (a? AS BOOLEAN)", "1:15: Type annotation not allowed in a?");
    }

    #[test]
    fn test_gosub_ok() {
        do_ok_test(
            "GOSUB 10",
            &[Statement::Gosub(GotoSpan { target: "10".to_owned(), target_pos: lc(1, 7) })],
        );

        do_ok_test(
            "GOSUB @foo",
            &[Statement::Gosub(GotoSpan { target: "foo".to_owned(), target_pos: lc(1, 7) })],
        );
    }

    #[test]
    fn test_gosub_errors() {
        do_error_test("GOSUB\n", "1:6: Expected label name after GOSUB");
        do_error_test("GOSUB foo\n", "1:7: Expected label name after GOSUB");
        do_error_test("GOSUB \"foo\"\n", "1:7: Expected label name after GOSUB");
        do_error_test("GOSUB @foo, @bar\n", "1:11: Expected newline but found ,");
        do_error_test("GOSUB @foo, 3\n", "1:11: Expected newline but found ,");
    }

    #[test]
    fn test_goto_ok() {
        do_ok_test(
            "GOTO 10",
            &[Statement::Goto(GotoSpan { target: "10".to_owned(), target_pos: lc(1, 6) })],
        );

        do_ok_test(
            "GOTO @foo",
            &[Statement::Goto(GotoSpan { target: "foo".to_owned(), target_pos: lc(1, 6) })],
        );
    }

    #[test]
    fn test_goto_errors() {
        do_error_test("GOTO\n", "1:5: Expected label name after GOTO");
        do_error_test("GOTO foo\n", "1:6: Expected label name after GOTO");
        do_error_test("GOTO \"foo\"\n", "1:6: Expected label name after GOTO");
        do_error_test("GOTO @foo, @bar\n", "1:10: Expected newline but found ,");
        do_error_test("GOTO @foo, 3\n", "1:10: Expected newline but found ,");
    }

    #[test]
    fn test_label_own_line() {
        do_ok_test(
            "@foo\nPRINT",
            &[
                Statement::Label(LabelSpan { name: "foo".to_owned(), name_pos: lc(1, 1) }),
                make_bare_builtin_call("PRINT", 2, 1),
            ],
        );
    }

    #[test]
    fn test_label_before_statement() {
        do_ok_test(
            "@foo PRINT",
            &[
                Statement::Label(LabelSpan { name: "foo".to_owned(), name_pos: lc(1, 1) }),
                make_bare_builtin_call("PRINT", 1, 6),
            ],
        );
    }

    #[test]
    fn test_label_multiple_same_line() {
        do_ok_test(
            "@foo @bar",
            &[
                Statement::Label(LabelSpan { name: "foo".to_owned(), name_pos: lc(1, 1) }),
                Statement::Label(LabelSpan { name: "bar".to_owned(), name_pos: lc(1, 6) }),
            ],
        );
    }

    #[test]
    fn test_label_errors() {
        do_error_test("PRINT @foo", "1:7: Unexpected keyword in expression");
    }

    #[test]
    fn test_parse_on_error_ok() {
        do_ok_test("ON ERROR GOTO 0", &[Statement::OnError(OnErrorSpan::Reset)]);

        do_ok_test(
            "ON ERROR GOTO 10",
            &[Statement::OnError(OnErrorSpan::Goto(GotoSpan {
                target: "10".to_owned(),
                target_pos: lc(1, 15),
            }))],
        );

        do_ok_test(
            "ON ERROR GOTO @foo",
            &[Statement::OnError(OnErrorSpan::Goto(GotoSpan {
                target: "foo".to_owned(),
                target_pos: lc(1, 15),
            }))],
        );

        do_ok_test("ON ERROR RESUME NEXT", &[Statement::OnError(OnErrorSpan::ResumeNext)]);
    }

    #[test]
    fn test_parse_on_error_errors() {
        do_error_test("ON", "1:3: Expected ERROR after ON");
        do_error_test("ON NEXT", "1:4: Expected ERROR after ON");
        do_error_test("ON ERROR", "1:9: Expected GOTO or RESUME after ON ERROR");
        do_error_test("ON ERROR FOR", "1:10: Expected GOTO or RESUME after ON ERROR");

        do_error_test("ON ERROR RESUME", "1:16: Expected NEXT after ON ERROR RESUME");
        do_error_test("ON ERROR RESUME 3", "1:17: Expected NEXT after ON ERROR RESUME");
        do_error_test("ON ERROR RESUME NEXT 3", "1:22: Expected newline but found 3");

        do_error_test("ON ERROR GOTO", "1:14: Expected label name or 0 after ON ERROR GOTO");
        do_error_test("ON ERROR GOTO NEXT", "1:15: Expected label name or 0 after ON ERROR GOTO");
        do_error_test("ON ERROR GOTO 0 @a", "1:17: Expected newline but found @a");
    }

    #[test]
    fn test_select_empty() {
        do_ok_test(
            "SELECT CASE 7\nEND SELECT",
            &[Statement::Select(SelectSpan {
                expr: expr_integer(7, 1, 13),
                cases: vec![],
                end_pos: lc(2, 1),
            })],
        );

        do_ok_test(
            "SELECT CASE 5 - TRUE\n    \nEND SELECT",
            &[Statement::Select(SelectSpan {
                expr: Expr::Subtract(Box::from(BinaryOpSpan {
                    lhs: expr_integer(5, 1, 13),
                    rhs: expr_boolean(true, 1, 17),
                    pos: lc(1, 15),
                })),
                cases: vec![],
                end_pos: lc(3, 1),
            })],
        );
    }

    #[test]
    fn test_select_case_else_only() {
        do_ok_test(
            "SELECT CASE 7\nCASE ELSE\nA\nEND SELECT",
            &[Statement::Select(SelectSpan {
                expr: expr_integer(7, 1, 13),
                cases: vec![CaseSpan {
                    guards: vec![],
                    body: vec![make_bare_builtin_call("A", 3, 1)],
                }],
                end_pos: lc(4, 1),
            })],
        );
    }

    #[test]
    fn test_select_multiple_cases_without_else() {
        do_ok_test(
            "SELECT CASE 7\nCASE 1\nA\nCASE 2\nB\nEND SELECT",
            &[Statement::Select(SelectSpan {
                expr: expr_integer(7, 1, 13),
                cases: vec![
                    CaseSpan {
                        guards: vec![CaseGuardSpan::Is(CaseRelOp::Equal, expr_integer(1, 2, 6))],
                        body: vec![make_bare_builtin_call("A", 3, 1)],
                    },
                    CaseSpan {
                        guards: vec![CaseGuardSpan::Is(CaseRelOp::Equal, expr_integer(2, 4, 6))],
                        body: vec![make_bare_builtin_call("B", 5, 1)],
                    },
                ],
                end_pos: lc(6, 1),
            })],
        );
    }

    #[test]
    fn test_select_multiple_cases_with_else() {
        do_ok_test(
            "SELECT CASE 7\nCASE 1\nA\nCASE 2\nB\nCASE ELSE\nC\nEND SELECT",
            &[Statement::Select(SelectSpan {
                expr: expr_integer(7, 1, 13),
                cases: vec![
                    CaseSpan {
                        guards: vec![CaseGuardSpan::Is(CaseRelOp::Equal, expr_integer(1, 2, 6))],
                        body: vec![make_bare_builtin_call("A", 3, 1)],
                    },
                    CaseSpan {
                        guards: vec![CaseGuardSpan::Is(CaseRelOp::Equal, expr_integer(2, 4, 6))],
                        body: vec![make_bare_builtin_call("B", 5, 1)],
                    },
                    CaseSpan { guards: vec![], body: vec![make_bare_builtin_call("C", 7, 1)] },
                ],
                end_pos: lc(8, 1),
            })],
        );
    }

    #[test]
    fn test_select_multiple_cases_empty_bodies() {
        do_ok_test(
            "SELECT CASE 7\nCASE 1\n\nCASE 2\n\nCASE ELSE\n\nEND SELECT",
            &[Statement::Select(SelectSpan {
                expr: expr_integer(7, 1, 13),
                cases: vec![
                    CaseSpan {
                        guards: vec![CaseGuardSpan::Is(CaseRelOp::Equal, expr_integer(1, 2, 6))],
                        body: vec![],
                    },
                    CaseSpan {
                        guards: vec![CaseGuardSpan::Is(CaseRelOp::Equal, expr_integer(2, 4, 6))],
                        body: vec![],
                    },
                    CaseSpan { guards: vec![], body: vec![] },
                ],
                end_pos: lc(8, 1),
            })],
        );
    }

    #[test]
    fn test_select_multiple_cases_with_interleaved_end() {
        let code = r#"
            SELECT CASE 7
                CASE 1
                    A
                    END
                    B
                CASE 2 ' Second case.
                    C
                    END 8
                    D
                CASE ELSE
                    E
                    END
                    F
            END SELECT
        "#;
        do_ok_test(
            code,
            &[Statement::Select(SelectSpan {
                expr: expr_integer(7, 2, 25),
                cases: vec![
                    CaseSpan {
                        guards: vec![CaseGuardSpan::Is(CaseRelOp::Equal, expr_integer(1, 3, 22))],
                        body: vec![
                            make_bare_builtin_call("A", 4, 21),
                            Statement::End(EndSpan { code: None }),
                            make_bare_builtin_call("B", 6, 21),
                        ],
                    },
                    CaseSpan {
                        guards: vec![CaseGuardSpan::Is(CaseRelOp::Equal, expr_integer(2, 7, 22))],
                        body: vec![
                            make_bare_builtin_call("C", 8, 21),
                            Statement::End(EndSpan {
                                code: Some(Expr::Integer(IntegerSpan { value: 8, pos: lc(9, 25) })),
                            }),
                            make_bare_builtin_call("D", 10, 21),
                        ],
                    },
                    CaseSpan {
                        guards: vec![],
                        body: vec![
                            make_bare_builtin_call("E", 12, 21),
                            Statement::End(EndSpan { code: None }),
                            make_bare_builtin_call("F", 14, 21),
                        ],
                    },
                ],
                end_pos: lc(15, 13),
            })],
        );
    }

    #[test]
    fn test_select_case_guards_equals() {
        do_ok_test(
            "SELECT CASE 7: CASE 9, 10, FALSE: END SELECT",
            &[Statement::Select(SelectSpan {
                expr: expr_integer(7, 1, 13),
                cases: vec![CaseSpan {
                    guards: vec![
                        CaseGuardSpan::Is(CaseRelOp::Equal, expr_integer(9, 1, 21)),
                        CaseGuardSpan::Is(CaseRelOp::Equal, expr_integer(10, 1, 24)),
                        CaseGuardSpan::Is(CaseRelOp::Equal, expr_boolean(false, 1, 28)),
                    ],
                    body: vec![],
                }],
                end_pos: lc(1, 35),
            })],
        );
    }

    #[test]
    fn test_select_case_guards_is() {
        do_ok_test(
            "SELECT CASE 7: CASE IS = 1, IS <> 2, IS < 3, IS <= 4, IS > 5, IS >= 6: END SELECT",
            &[Statement::Select(SelectSpan {
                expr: expr_integer(7, 1, 13),
                cases: vec![CaseSpan {
                    guards: vec![
                        CaseGuardSpan::Is(CaseRelOp::Equal, expr_integer(1, 1, 26)),
                        CaseGuardSpan::Is(CaseRelOp::NotEqual, expr_integer(2, 1, 35)),
                        CaseGuardSpan::Is(CaseRelOp::Less, expr_integer(3, 1, 43)),
                        CaseGuardSpan::Is(CaseRelOp::LessEqual, expr_integer(4, 1, 52)),
                        CaseGuardSpan::Is(CaseRelOp::Greater, expr_integer(5, 1, 60)),
                        CaseGuardSpan::Is(CaseRelOp::GreaterEqual, expr_integer(6, 1, 69)),
                    ],
                    body: vec![],
                }],
                end_pos: lc(1, 72),
            })],
        );
    }

    #[test]
    fn test_select_case_guards_to() {
        do_ok_test(
            "SELECT CASE 7: CASE 1 TO 20, 10 TO 1: END SELECT",
            &[Statement::Select(SelectSpan {
                expr: expr_integer(7, 1, 13),
                cases: vec![CaseSpan {
                    guards: vec![
                        CaseGuardSpan::To(expr_integer(1, 1, 21), expr_integer(20, 1, 26)),
                        CaseGuardSpan::To(expr_integer(10, 1, 30), expr_integer(1, 1, 36)),
                    ],
                    body: vec![],
                }],
                end_pos: lc(1, 39),
            })],
        );
    }

    #[test]
    fn test_select_errors() {
        do_error_test("SELECT\n", "1:7: Expecting CASE after SELECT");
        do_error_test("SELECT CASE\n", "1:12: No expression in SELECT CASE statement");
        do_error_test("SELECT CASE 3 + 7", "1:18: Expecting newline after SELECT CASE");
        do_error_test("SELECT CASE 3 + 7 ,", "1:19: Expecting newline after SELECT CASE");
        do_error_test("SELECT CASE 3 + 7 IF", "1:19: Unexpected keyword in expression");

        do_error_test("SELECT CASE 1\n", "1:1: SELECT without END SELECT");

        do_error_test(
            "SELECT CASE 1\nEND",
            "2:1: Expected CASE after SELECT CASE before any statement",
        );
        do_error_test(
            "SELECT CASE 1\nEND IF",
            "2:1: Expected CASE after SELECT CASE before any statement",
        );
        do_error_test(
            "SELECT CASE 1\na = 1",
            "2:1: Expected CASE after SELECT CASE before any statement",
        );

        do_error_test(
            "SELECT CASE 1\nCASE 1",
            "2:7: Expected comma, newline, or TO after expression",
        );
        do_error_test("SELECT CASE 1\nCASE ELSE", "2:10: Expecting newline after CASE");

        do_error_test("SELECT CASE 1\nCASE ELSE\nEND", "1:1: SELECT without END SELECT");
        do_error_test("SELECT CASE 1\nCASE ELSE\nEND IF", "3:1: END IF without IF");

        do_error_test("SELECT CASE 1\nCASE ELSE\nCASE ELSE\n", "3:1: CASE ELSE must be unique");
        do_error_test("SELECT CASE 1\nCASE ELSE\nCASE 1\n", "3:1: CASE ELSE is not last");
    }

    #[test]
    fn test_select_case_errors() {
        fn do_case_error_test(cases: &str, exp_error: &str) {
            do_error_test(&format!("SELECT CASE 1\nCASE {}\n", cases), exp_error);
        }

        do_case_error_test("ELSE, ELSE", "2:10: Expected newline after CASE ELSE");
        do_case_error_test("ELSE, 7", "2:10: Expected newline after CASE ELSE");
        do_case_error_test("7, ELSE", "2:9: CASE ELSE must be on its own");

        do_case_error_test("IS 7", "2:9: Expected relational operator");
        do_case_error_test("IS AND", "2:9: Expected relational operator");
        do_case_error_test("IS END", "2:9: Expected relational operator");

        do_case_error_test("IS <>", "2:11: Missing expression after relational operator");
        do_case_error_test("IS <> IF", "2:12: Unexpected keyword in expression");

        do_case_error_test("", "2:6: Missing expression in CASE guard");
        do_case_error_test("2 + 5 TO", "2:14: Missing expression after TO in CASE guard");
        do_case_error_test("2 + 5 TO AS", "2:15: Missing expression after TO in CASE guard");
        do_case_error_test(
            "2 + 5 TO 8 AS",
            "2:17: Expected comma, newline, or TO after expression",
        );
    }

    #[test]
    fn test_sub_empty() {
        do_ok_test(
            "SUB foo\nEND SUB",
            &[Statement::Callable(CallableSpan {
                name: VarRef::new("foo", None),
                name_pos: lc(1, 5),
                params: vec![],
                body: vec![],
                end_pos: lc(2, 1),
            })],
        );
    }

    #[test]
    fn test_sub_some_content() {
        do_ok_test(
            r#"
                SUB foo
                    A
                    END
                    END 8
                    B
                END SUB
            "#,
            &[Statement::Callable(CallableSpan {
                name: VarRef::new("foo", None),
                name_pos: lc(2, 21),
                params: vec![],
                body: vec![
                    make_bare_builtin_call("A", 3, 21),
                    Statement::End(EndSpan { code: None }),
                    Statement::End(EndSpan {
                        code: Some(Expr::Integer(IntegerSpan { value: 8, pos: lc(5, 25) })),
                    }),
                    make_bare_builtin_call("B", 6, 21),
                ],
                end_pos: lc(7, 17),
            })],
        );
    }

    #[test]
    fn test_sub_one_param() {
        do_ok_test(
            "SUB foo(x)\nEND SUB",
            &[Statement::Callable(CallableSpan {
                name: VarRef::new("foo", None),
                name_pos: lc(1, 5),
                params: vec![VarRef::new("x", None)],
                body: vec![],
                end_pos: lc(2, 1),
            })],
        );
    }

    #[test]
    fn test_sub_multiple_params() {
        do_ok_test(
            "SUB foo(x$, y, z AS BOOLEAN)\nEND SUB",
            &[Statement::Callable(CallableSpan {
                name: VarRef::new("foo", None),
                name_pos: lc(1, 5),
                params: vec![
                    VarRef::new("x", Some(ExprType::Text)),
                    VarRef::new("y", None),
                    VarRef::new("z", Some(ExprType::Boolean)),
                ],
                body: vec![],
                end_pos: lc(2, 1),
            })],
        );
    }

    #[test]
    fn test_sub_errors() {
        do_error_test("SUB", "1:4: Expected a function name after SUB");
        do_error_test("SUB foo", "1:8: Expected newline after SUB name");
        do_error_test("SUB foo 3", "1:9: Expected newline after SUB name");
        do_error_test("SUB foo\nEND", "1:1: SUB without END SUB");
        do_error_test("SUB foo\nEND IF", "2:1: END IF without IF");
        do_error_test("SUB foo\nEND FUNCTION", "2:1: END FUNCTION without FUNCTION");
        do_error_test(
            "SUB foo\nSUB bar\nEND SUB\nEND SUB",
            "2:1: Cannot nest FUNCTION or SUB definitions",
        );
        do_error_test(
            "SUB foo\nFUNCTION bar\nEND FUNCTION\nEND SUB",
            "2:1: Cannot nest FUNCTION or SUB definitions",
        );
        do_error_test("SUB foo (", "1:10: Expected a parameter name");
        do_error_test("SUB foo ()", "1:10: Expected a parameter name");
        do_error_test("SUB foo (,)", "1:10: Expected a parameter name");
        do_error_test("SUB foo (a,)", "1:12: Expected a parameter name");
        do_error_test("SUB foo (,b)", "1:10: Expected a parameter name");
        do_error_test("SUB foo (a AS)", "1:14: Invalid type name ) in AS type definition");
        do_error_test("SUB foo (a INTEGER)", "1:12: Expected comma, AS, or end of parameters list");
        do_error_test("SUB foo (a? AS BOOLEAN)", "1:10: Type annotation not allowed in a?");
        do_error_test(
            "SUB foo$",
            "1:5: SUBs cannot return a value so type annotations are not allowed",
        );
        do_error_test(
            "SUB foo$\nEND SUB",
            "1:5: SUBs cannot return a value so type annotations are not allowed",
        );
    }

    #[test]
    fn test_while_empty() {
        do_ok_test(
            "WHILE 2 + 3\nWEND",
            &[Statement::While(WhileSpan {
                expr: Expr::Add(Box::from(BinaryOpSpan {
                    lhs: expr_integer(2, 1, 7),
                    rhs: expr_integer(3, 1, 11),
                    pos: lc(1, 9),
                })),
                body: vec![],
            })],
        );
        do_ok_test(
            "WHILE 5\n\nREM foo\n\nWEND\n",
            &[Statement::While(WhileSpan { expr: expr_integer(5, 1, 7), body: vec![] })],
        );
    }

    #[test]
    fn test_while_loops() {
        do_ok_test(
            "WHILE TRUE\nA\nB\nWEND",
            &[Statement::While(WhileSpan {
                expr: expr_boolean(true, 1, 7),
                body: vec![make_bare_builtin_call("A", 2, 1), make_bare_builtin_call("B", 3, 1)],
            })],
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
            &[Statement::While(WhileSpan {
                expr: expr_boolean(true, 2, 19),
                body: vec![
                    make_bare_builtin_call("A", 3, 17),
                    Statement::While(WhileSpan {
                        expr: expr_boolean(false, 4, 23),
                        body: vec![make_bare_builtin_call("B", 5, 21)],
                    }),
                    make_bare_builtin_call("C", 7, 17),
                ],
            })],
        );
    }

    #[test]
    fn test_while_errors() {
        do_error_test("WHILE\n", "1:6: No expression in WHILE statement");
        do_error_test("WHILE TRUE", "1:11: Expecting newline after WHILE");
        do_error_test("\n\nWHILE TRUE\n", "3:1: WHILE without WEND");
        do_error_test("WHILE TRUE\nEND", "1:1: WHILE without WEND");
        do_error_test("WHILE TRUE\nEND\n", "1:1: WHILE without WEND");
        do_error_test("WHILE TRUE\nEND WHILE\n", "2:5: Unexpected keyword in expression");

        do_error_test("WHILE ,\nWEND", "1:7: No expression in WHILE statement");
        do_error_test("WHILE ,\nEND", "1:7: No expression in WHILE statement");
    }
}
