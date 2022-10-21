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
use crate::lexer::{Lexer, PeekableLexer, Token};
use crate::reader::LineCol;
use std::cmp::Ordering;
use std::io;

/// Parser errors.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Bad syntax in the input program.
    #[error("{}:{}: {}", .0.line, .0.col, .1)]
    Bad(LineCol, String),

    /// I/O error while parsing the input program.
    #[error("read error")]
    Io(#[from] io::Error),
}

/// Result for parser return values.
pub type Result<T> = std::result::Result<T, Error>;

/// Transforms a `VarRef` into an unannotated name.
///
/// This is only valid for references that have no annotations in them.
fn vref_to_unannotated_string(vref: VarRef, pos: LineCol) -> Result<String> {
    if vref.ref_type() != VarType::Auto {
        return Err(Error::Bad(pos, format!("Type annotation not allowed in {}", vref)));
    }
    Ok(vref.take_name())
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
            exprs.push(f(Box::from(UnaryOpSpan { expr })));
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
            exprs.push(f(Box::from(BinaryOpSpan { lhs, rhs })));
            Ok(())
        }

        match self.op {
            ExprOp::Add => apply2(exprs, self.pos, Expr::Add),
            ExprOp::Subtract => apply2(exprs, self.pos, Expr::Subtract),
            ExprOp::Multiply => apply2(exprs, self.pos, Expr::Multiply),
            ExprOp::Divide => apply2(exprs, self.pos, Expr::Divide),
            ExprOp::Modulo => apply2(exprs, self.pos, Expr::Modulo),
            ExprOp::Equal => apply2(exprs, self.pos, Expr::Equal),
            ExprOp::NotEqual => apply2(exprs, self.pos, Expr::NotEqual),
            ExprOp::Less => apply2(exprs, self.pos, Expr::Less),
            ExprOp::LessEqual => apply2(exprs, self.pos, Expr::LessEqual),
            ExprOp::Greater => apply2(exprs, self.pos, Expr::Greater),
            ExprOp::GreaterEqual => apply2(exprs, self.pos, Expr::GreaterEqual),
            ExprOp::And => apply2(exprs, self.pos, Expr::And),
            ExprOp::Or => apply2(exprs, self.pos, Expr::Or),
            ExprOp::Xor => apply2(exprs, self.pos, Expr::Xor),

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
    fn expect_and_consume(&mut self, t: Token, err: &'static str) -> Result<()> {
        let peeked = self.lexer.peek()?;
        if peeked.token != t {
            return Err(Error::Bad(peeked.pos, err.to_owned()));
        }
        self.lexer.consume_peeked();
        Ok(())
    }

    /// Expects the peeked token to be `t` and consumes it.  Otherwise, leaves the token in the
    /// stream and fails with error `err`, pointing at `pos` as the original location of the
    /// problem.
    fn expect_and_consume_with_pos(
        &mut self,
        t: Token,
        pos: LineCol,
        err: &'static str,
    ) -> Result<()> {
        let peeked = self.lexer.peek()?;
        if peeked.token != t {
            return Err(Error::Bad(pos, err.to_owned()));
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
            if delims.contains(&peeked.token) {
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

    /// Parses an assignment for the variable reference `varref` already read.
    fn parse_assignment(&mut self, vref: VarRef) -> Result<Statement> {
        let expr = self.parse_required_expr("Missing expression in assignment")?;

        let next = self.lexer.peek()?;
        match &next.token {
            Token::Eof | Token::Eol => (),
            t => return Err(Error::Bad(next.pos, format!("Unexpected {} in assignment", t))),
        }
        Ok(Statement::Assignment(AssignmentSpan { vref, expr }))
    }

    /// Parses an assignment to the array `varref` with `subscripts`, both of which have already
    /// been read.
    fn parse_array_assignment(&mut self, vref: VarRef, subscripts: Vec<Expr>) -> Result<Statement> {
        let expr = self.parse_required_expr("Missing expression in array assignment")?;

        let next = self.lexer.peek()?;
        match &next.token {
            Token::Eof | Token::Eol => (),
            t => return Err(Error::Bad(next.pos, format!("Unexpected {} in array assignment", t))),
        }
        Ok(Statement::ArrayAssignment(ArrayAssignmentSpan { vref, subscripts, expr }))
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
                Token::Eof | Token::Eol => {
                    if expr.is_some() || !args.is_empty() {
                        args.push(ArgSpan { expr, sep: ArgSep::End });
                    }
                    break;
                }
                Token::Semicolon => {
                    self.lexer.consume_peeked();
                    args.push(ArgSpan { expr, sep: ArgSep::Short });
                }
                Token::Comma => {
                    self.lexer.consume_peeked();
                    args.push(ArgSpan { expr, sep: ArgSep::Long });
                }
                _ => {
                    return Err(Error::Bad(
                        peeked.pos,
                        "Expected comma, semicolon, or end of statement".to_owned(),
                    ))
                }
            }
        }
        Ok(Statement::BuiltinCall(BuiltinCallSpan { name, args }))
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
                let mut exprs = self.parse_comma_separated_exprs()?;
                match self.lexer.peek()?.token {
                    Token::Equal => {
                        self.lexer.consume_peeked();
                        self.parse_array_assignment(vref, exprs)
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

    /// Parses the `AS typename` clause of a `DIM` statement.  The caller has already consumed the
    /// `AS` token.
    fn parse_dim_as(&mut self) -> Result<VarType> {
        let peeked = self.lexer.peek()?;
        let vartype = match peeked.token {
            Token::Eof | Token::Eol => VarType::Integer,
            Token::As => {
                self.lexer.consume_peeked();
                let token_span = self.lexer.read()?;
                match token_span.token {
                    Token::BooleanName => VarType::Boolean,
                    Token::DoubleName => VarType::Double,
                    Token::IntegerName => VarType::Integer,
                    Token::TextName => VarType::Text,
                    t => {
                        return Err(Error::Bad(
                            token_span.pos,
                            format!("Invalid type name {} in DIM AS statement", t),
                        ))
                    }
                }
            }
            _ => return Err(Error::Bad(peeked.pos, "Expected AS or end of statement".to_owned())),
        };

        let next = self.lexer.peek()?;
        match &next.token {
            Token::Eof | Token::Eol => (),
            t => return Err(Error::Bad(next.pos, format!("Unexpected {} in DIM statement", t))),
        }

        Ok(vartype)
    }

    /// Parses a `DIM` statement.
    fn parse_dim(&mut self) -> Result<Statement> {
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
                let subtype = self.parse_dim_as()?;
                Ok(Statement::DimArray(DimArraySpan { name, dimensions, subtype }))
            }
            _ => {
                let vartype = self.parse_dim_as()?;
                Ok(Statement::Dim(DimSpan { name, vtype: vartype }))
            }
        }
    }

    /// Parses a variable list of comma-separated expressions.  The caller must have consumed the
    /// open parenthesis and we stop processing when we encounter the terminating parenthesis (and
    /// consume it).  We expect at least one expression.
    fn parse_comma_separated_exprs(&mut self) -> Result<Vec<Expr>> {
        let mut exprs = vec![];
        let first_pos = self.lexer.peek()?.pos;
        if let Some(expr) = self.parse_expr(None)? {
            // The first expression is optional to support calls to functions without arguments.
            exprs.push(expr);
        }

        loop {
            let peeked = self.lexer.peek()?;
            let pos = peeked.pos;
            match &peeked.token {
                Token::RightParen => {
                    self.lexer.consume_peeked();
                    break;
                }
                Token::Comma => {
                    self.lexer.consume_peeked();
                    if exprs.is_empty() {
                        // The first expression (parsed outside the loop) cannot be empty if we
                        // encounter more than one expression.
                        return Err(Error::Bad(first_pos, "Missing expression".to_owned()));
                    }
                    let expr = self.parse_required_expr("Missing expression")?;
                    exprs.push(expr);
                }
                t => return Err(Error::Bad(pos, format!("Unexpected {}", t))),
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
                | Token::Comma
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
                    handle_operand(Expr::Boolean(BooleanSpan { value }), ts.pos)?
                }
                Token::Double(value) => handle_operand(Expr::Double(DoubleSpan { value }), ts.pos)?,
                Token::Integer(value) => {
                    handle_operand(Expr::Integer(IntegerSpan { value }), ts.pos)?
                }
                Token::Text(value) => handle_operand(Expr::Text(TextSpan { value }), ts.pos)?,
                Token::Symbol(vref) => handle_operand(Expr::Symbol(SymbolSpan { vref }), ts.pos)?,

                Token::LeftParen => {
                    // If the last operand we encountered was a symbol, collapse it and the left
                    // parenthesis into the beginning of a function call.
                    match exprs.pop() {
                        Some(Expr::Symbol(span)) => {
                            if !need_operand {
                                exprs.push(Expr::Call(FunctionCallSpan {
                                    fref: span.vref,
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
                | Token::And
                | Token::Or
                | Token::Xor => {
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
                | Token::Goto
                | Token::If
                | Token::IntegerName
                | Token::Label(_)
                | Token::Next
                | Token::TextName
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

    /// Parses a `GOTO` statement.
    fn parse_goto(&mut self) -> Result<Statement> {
        let token_span = self.lexer.read()?;
        let target = match token_span.token {
            Token::Label(target) => target,
            _ => {
                return Err(Error::Bad(token_span.pos, "Expected label name after GOTO".to_owned()))
            }
        };
        Ok(Statement::Goto(GotoSpan { target }))
    }

    /// Parses an `IF` statement.
    fn parse_if(&mut self, if_pos: LineCol) -> Result<Statement> {
        let expr = self.parse_required_expr("No expression in IF statement")?;
        self.expect_and_consume(Token::Then, "No THEN in IF statement")?;
        self.expect_and_consume(Token::Eol, "Expecting newline after THEN")?;

        let mut branches = vec![IfBranchSpan {
            guard: expr,
            body: self.parse_until(&[Token::Elseif, Token::Else, Token::End])?,
        }];
        loop {
            let peeked = self.lexer.peek()?;
            match peeked.token {
                Token::Elseif => {
                    self.lexer.consume_peeked();
                    let expr = self.parse_required_expr("No expression in ELSEIF statement")?;
                    self.expect_and_consume(Token::Then, "No THEN in ELSEIF statement")?;
                    self.expect_and_consume(Token::Eol, "Expecting newline after THEN")?;
                    let stmts2 = self.parse_until(&[Token::Elseif, Token::Else, Token::End])?;
                    branches.push(IfBranchSpan { guard: expr, body: stmts2 });
                }
                _ => break,
            }
        }

        let peeked = self.lexer.peek()?;
        if peeked.token == Token::Else {
            self.lexer.consume_peeked();
            self.expect_and_consume(Token::Eol, "Expecting newline after ELSE")?;
            let stmts2 = self.parse_until(&[Token::Elseif, Token::Else, Token::End])?;
            let peeked = self.lexer.peek()?;
            match peeked.token {
                Token::Elseif => {
                    return Err(Error::Bad(peeked.pos, "Unexpected ELSEIF after ELSE".to_owned()))
                }
                Token::Else => {
                    return Err(Error::Bad(peeked.pos, "Duplicate ELSE after ELSE".to_owned()))
                }
                _ => (),
            }
            branches.push(IfBranchSpan {
                guard: Expr::Boolean(BooleanSpan { value: true }),
                body: stmts2,
            });
        }

        self.expect_and_consume_with_pos(Token::End, if_pos, "IF without END IF")?;
        self.expect_and_consume_with_pos(Token::If, if_pos, "IF without END IF")?;

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
    fn parse_step(&mut self) -> Result<(i32, LineCol)> {
        let peeked = self.lexer.peek()?;
        match peeked.token {
            Token::Step => self.lexer.consume_peeked(),
            _ => {
                // The position we return here for the step isn't truly the right value, but given
                // that we know the hardcoded step of 1 is valid, the caller will not error out and
                // will not print the slightly invalid position.
                return Ok((1, peeked.pos));
            }
        };

        let peeked = self.lexer.peek()?;
        match peeked.token {
            Token::Integer(i) => {
                let peeked = self.lexer.consume_peeked();
                Ok((i, peeked.pos))
            }
            Token::Minus => {
                self.lexer.consume_peeked();
                let peeked = self.lexer.peek()?;
                match peeked.token {
                    Token::Integer(i) => {
                        let peeked = self.lexer.consume_peeked();
                        Ok((-i, peeked.pos))
                    }
                    _ => Err(Error::Bad(peeked.pos, "STEP needs an integer".to_owned())),
                }
            }
            _ => Err(Error::Bad(peeked.pos, "STEP needs an integer".to_owned())),
        }
    }

    /// Parses a `FOR` statement.
    fn parse_for(&mut self, for_pos: LineCol) -> Result<Statement> {
        let token_span = self.lexer.read()?;
        let iterator = match token_span.token {
            Token::Symbol(iterator) => match iterator.ref_type() {
                // TODO(jmmv): Should we support doubles in for loops?
                VarType::Auto | VarType::Integer => iterator,
                _ => {
                    return Err(Error::Bad(
                        token_span.pos,
                        "Iterator name in FOR statement must be an integer reference".to_owned(),
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

        self.expect_and_consume(Token::Equal, "No equal sign in FOR statement")?;
        let start = self.parse_required_expr("No start expression in FOR statement")?;

        self.expect_and_consume(Token::To, "No TO in FOR statement")?;
        let end = self.parse_required_expr("No end expression in FOR statement")?;

        let (step, step_pos) = self.parse_step()?;
        let end_condition = match step.cmp(&0) {
            Ordering::Greater => Expr::LessEqual(Box::from(BinaryOpSpan {
                lhs: Expr::Symbol(SymbolSpan { vref: iterator.clone() }),
                rhs: end,
            })),
            Ordering::Less => Expr::GreaterEqual(Box::from(BinaryOpSpan {
                lhs: Expr::Symbol(SymbolSpan { vref: iterator.clone() }),
                rhs: end,
            })),
            Ordering::Equal => {
                return Err(Error::Bad(step_pos, "Infinite FOR loop; STEP cannot be 0".to_owned()))
            }
        };

        let next_value = Expr::Add(Box::from(BinaryOpSpan {
            lhs: Expr::Symbol(SymbolSpan { vref: iterator.clone() }),
            rhs: Expr::Integer(IntegerSpan { value: step }),
        }));

        self.expect_and_consume(Token::Eol, "Expecting newline after FOR")?;

        let stmts = self.parse_until(&[Token::Next])?;
        self.expect_and_consume_with_pos(Token::Next, for_pos, "FOR without NEXT")?;

        Ok(Statement::For(ForSpan {
            iter: iterator,
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

    /// Parses a `WHILE` statement.
    fn parse_while(&mut self, while_pos: LineCol) -> Result<Statement> {
        let expr = self.parse_required_expr("No expression in WHILE statement")?;
        self.expect_and_consume(Token::Eol, "Expecting newline after WHILE")?;

        let stmts = self.parse_until(&[Token::Wend])?;
        self.expect_and_consume_with_pos(Token::Wend, while_pos, "WHILE without WEND")?;

        Ok(Statement::While(WhileSpan { expr, body: stmts }))
    }

    /// Advances until the next statement after failing to parse a `WHILE` statement.
    fn reset_while(&mut self, while_pos: LineCol) -> Result<()> {
        loop {
            match self.lexer.peek()?.token {
                Token::Eof => break,
                Token::End => {
                    self.lexer.consume_peeked();
                    self.expect_and_consume_with_pos(
                        Token::While,
                        while_pos,
                        "WHILE without WEND",
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
            Token::Eof => return Ok(None),
            Token::Eol => Ok(None),
            Token::Dim => Ok(Some(self.parse_dim()?)),
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
            Token::Goto => {
                let result = self.parse_goto();
                Ok(Some(result?))
            }
            Token::Label(name) => {
                // Handling a label here means that it must be followed by a newline, which might
                // seem "strange" considering that other languages allow specifying a label in the
                // same line as other code.  This is intentional to keep the parser simpler.  And,
                // in any case, because line separators can be a colon character, placing one after
                // the label name to join it with a statement looks "natural".
                Ok(Some(Statement::Label(LabelSpan { name })))
            }
            Token::Symbol(vref) => {
                let peeked = self.lexer.peek()?;
                if peeked.token == Token::Equal {
                    self.lexer.consume_peeked();
                    Ok(Some(self.parse_assignment(vref)?))
                } else {
                    Ok(Some(self.parse_array_or_builtin_call(vref, token_span.pos)?))
                }
            }
            Token::While => {
                let result = self.parse_while(token_span.pos);
                if result.is_err() {
                    self.reset_while(token_span.pos)?;
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

/// Extracts all statements from the input stream.
pub fn parse(input: &mut dyn io::Read) -> Result<Vec<Statement>> {
    let mut parser = Parser::from(input);
    let mut statements = vec![];
    while let Some(statement) = parser.parse_one_safe()? {
        statements.push(statement);
    }
    Ok(statements)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::VarType;

    /// Syntactic sugar to instantiate an `Expr::Boolean` for testing.
    fn expr_boolean(value: bool) -> Expr {
        Expr::Boolean(BooleanSpan { value })
    }

    /// Syntactic sugar to instantiate an `Expr::Double` for testing.
    fn expr_double(value: f64) -> Expr {
        Expr::Double(DoubleSpan { value })
    }

    /// Syntactic sugar to instantiate an `Expr::Integer` for testing.
    fn expr_integer(value: i32) -> Expr {
        Expr::Integer(IntegerSpan { value })
    }

    /// Syntactic sugar to instantiate an `Expr::Text` for testing.
    fn expr_text<S: Into<String>>(value: S) -> Expr {
        Expr::Text(TextSpan { value: value.into() })
    }

    /// Syntactic sugar to instantiate an `Expr::Symbol` for testing.
    fn expr_symbol(vref: VarRef) -> Expr {
        Expr::Symbol(SymbolSpan { vref })
    }

    #[test]
    fn test_varref_to_unannotated_string() {
        assert_eq!(
            "print",
            &vref_to_unannotated_string(
                VarRef::new("print", VarType::Auto),
                LineCol { line: 0, col: 0 }
            )
            .unwrap()
        );

        assert_eq!(
            "7:6: Type annotation not allowed in print$",
            format!(
                "{}",
                &vref_to_unannotated_string(
                    VarRef::new("print", VarType::Text),
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
        let statements = parse(&mut input).expect("Parsing failed");
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
        assert_eq!(
            expected_err,
            format!("{}", parse(&mut input).expect_err("Parsing did not fail"))
        );
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
                    vref: VarRef::new("a", VarType::Auto),
                    expr: expr_integer(1),
                }),
                Statement::Assignment(AssignmentSpan {
                    vref: VarRef::new("b", VarType::Auto),
                    expr: expr_integer(2),
                }),
                Statement::Assignment(AssignmentSpan {
                    vref: VarRef::new("c", VarType::Auto),
                    expr: expr_integer(3),
                }),
                Statement::Assignment(AssignmentSpan {
                    vref: VarRef::new("d", VarType::Auto),
                    expr: expr_integer(4),
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
                    vref: VarRef::new("a", VarType::Auto),
                    subscripts: vec![expr_integer(1)],
                    expr: expr_integer(100),
                }),
                Statement::ArrayAssignment(ArrayAssignmentSpan {
                    vref: VarRef::new("foo", VarType::Auto),
                    subscripts: vec![expr_integer(2), expr_integer(3)],
                    expr: expr_text("text"),
                }),
                Statement::ArrayAssignment(ArrayAssignmentSpan {
                    vref: VarRef::new("abc", VarType::Text),
                    subscripts: vec![
                        Expr::Add(Box::from(BinaryOpSpan {
                            lhs: expr_integer(5),
                            rhs: expr_symbol(VarRef::new("z".to_owned(), VarType::Auto)),
                        })),
                        expr_integer(6),
                    ],
                    expr: Expr::Or(Box::from(BinaryOpSpan {
                        lhs: expr_boolean(true),
                        rhs: expr_boolean(false),
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
                    vref: VarRef::new("a", VarType::Auto),
                    expr: expr_integer(1),
                }),
                Statement::Assignment(AssignmentSpan {
                    vref: VarRef::new("foo", VarType::Text),
                    expr: expr_text("bar"),
                }),
                Statement::Assignment(AssignmentSpan {
                    vref: VarRef::new("b", VarType::Text),
                    expr: Expr::Add(Box::from(BinaryOpSpan {
                        lhs: expr_integer(3),
                        rhs: expr_symbol(VarRef::new("z", VarType::Auto)),
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
        do_error_test("3 = a", "1:1: Unexpected 3 in statement");
    }

    #[test]
    fn test_builtin_calls() {
        do_ok_test(
            "PRINT a\nPRINT ; 3 , c$\nNOARGS",
            &[
                Statement::BuiltinCall(BuiltinCallSpan {
                    name: "PRINT".to_owned(),
                    args: vec![ArgSpan {
                        expr: Some(expr_symbol(VarRef::new("a", VarType::Auto))),
                        sep: ArgSep::End,
                    }],
                }),
                Statement::BuiltinCall(BuiltinCallSpan {
                    name: "PRINT".to_owned(),
                    args: vec![
                        ArgSpan { expr: None, sep: ArgSep::Short },
                        ArgSpan { expr: Some(expr_integer(3)), sep: ArgSep::Long },
                        ArgSpan {
                            expr: Some(expr_symbol(VarRef::new("c", VarType::Text))),
                            sep: ArgSep::End,
                        },
                    ],
                }),
                Statement::BuiltinCall(BuiltinCallSpan { name: "NOARGS".to_owned(), args: vec![] }),
            ],
        );
    }

    #[test]
    fn test_builtin_calls_and_array_references_disambiguation() {
        use Expr::*;

        do_ok_test(
            "PRINT(1)",
            &[Statement::BuiltinCall(BuiltinCallSpan {
                name: "PRINT".to_owned(),
                args: vec![ArgSpan { expr: Some(expr_integer(1)), sep: ArgSep::End }],
            })],
        );

        do_ok_test(
            "PRINT(1), 2",
            &[Statement::BuiltinCall(BuiltinCallSpan {
                name: "PRINT".to_owned(),
                args: vec![
                    ArgSpan { expr: Some(expr_integer(1)), sep: ArgSep::Long },
                    ArgSpan { expr: Some(expr_integer(2)), sep: ArgSep::End },
                ],
            })],
        );

        do_ok_test(
            "PRINT(1); 2",
            &[Statement::BuiltinCall(BuiltinCallSpan {
                name: "PRINT".to_owned(),
                args: vec![
                    ArgSpan { expr: Some(expr_integer(1)), sep: ArgSep::Short },
                    ArgSpan { expr: Some(expr_integer(2)), sep: ArgSep::End },
                ],
            })],
        );

        do_ok_test(
            "PRINT(1);",
            &[Statement::BuiltinCall(BuiltinCallSpan {
                name: "PRINT".to_owned(),
                args: vec![
                    ArgSpan { expr: Some(expr_integer(1)), sep: ArgSep::Short },
                    ArgSpan { expr: None, sep: ArgSep::End },
                ],
            })],
        );

        do_ok_test(
            "PRINT(1) + 2; 3",
            &[Statement::BuiltinCall(BuiltinCallSpan {
                name: "PRINT".to_owned(),
                args: vec![
                    ArgSpan {
                        expr: Some(Add(Box::from(BinaryOpSpan {
                            lhs: expr_integer(1),
                            rhs: expr_integer(2),
                        }))),
                        sep: ArgSep::Short,
                    },
                    ArgSpan { expr: Some(expr_integer(3)), sep: ArgSep::End },
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
    fn test_dim_default_type() {
        do_ok_test(
            "DIM i",
            &[Statement::Dim(DimSpan { name: "i".to_owned(), vtype: VarType::Integer })],
        );
    }

    #[test]
    fn test_dim_as_simple_types() {
        do_ok_test(
            "DIM i AS BOOLEAN",
            &[Statement::Dim(DimSpan { name: "i".to_owned(), vtype: VarType::Boolean })],
        );
        do_ok_test(
            "DIM i AS DOUBLE",
            &[Statement::Dim(DimSpan { name: "i".to_owned(), vtype: VarType::Double })],
        );
        do_ok_test(
            "DIM i AS INTEGER",
            &[Statement::Dim(DimSpan { name: "i".to_owned(), vtype: VarType::Integer })],
        );
        do_ok_test(
            "DIM i AS STRING",
            &[Statement::Dim(DimSpan { name: "i".to_owned(), vtype: VarType::Text })],
        );
    }

    #[test]
    fn test_dim_consecutive() {
        do_ok_test(
            "DIM i\nDIM j AS BOOLEAN\nDIM k",
            &[
                Statement::Dim(DimSpan { name: "i".to_owned(), vtype: VarType::Integer }),
                Statement::Dim(DimSpan { name: "j".to_owned(), vtype: VarType::Boolean }),
                Statement::Dim(DimSpan { name: "k".to_owned(), vtype: VarType::Integer }),
            ],
        );
    }

    #[test]
    fn test_dim_array() {
        use Expr::*;

        do_ok_test(
            "DIM i(10)",
            &[Statement::DimArray(DimArraySpan {
                name: "i".to_owned(),
                dimensions: vec![expr_integer(10)],
                subtype: VarType::Integer,
            })],
        );

        do_ok_test(
            "DIM foo(-5, 0) AS STRING",
            &[Statement::DimArray(DimArraySpan {
                name: "foo".to_owned(),
                dimensions: vec![
                    Negate(Box::from(UnaryOpSpan { expr: expr_integer(5) })),
                    expr_integer(0),
                ],
                subtype: VarType::Text,
            })],
        );

        do_ok_test(
            "DIM foo(bar$() + 3, 8, -1)",
            &[Statement::DimArray(DimArraySpan {
                name: "foo".to_owned(),
                dimensions: vec![
                    Add(Box::from(BinaryOpSpan {
                        lhs: Call(FunctionCallSpan {
                            fref: VarRef::new("bar", VarType::Text),
                            args: vec![],
                        }),
                        rhs: expr_integer(3),
                    })),
                    expr_integer(8),
                    Negate(Box::from(UnaryOpSpan { expr: expr_integer(1) })),
                ],
                subtype: VarType::Integer,
            })],
        );
    }

    #[test]
    fn test_dim_errors() {
        do_error_test("DIM", "1:4: Expected variable name after DIM");
        do_error_test("DIM 3", "1:5: Expected variable name after DIM");
        do_error_test("DIM AS", "1:5: Expected variable name after DIM");
        do_error_test("DIM foo 3", "1:9: Expected AS or end of statement");
        do_error_test("DIM a AS", "1:9: Invalid type name <<EOF>> in DIM AS statement");
        do_error_test("DIM a$ AS", "1:5: Type annotation not allowed in a$");
        do_error_test("DIM a AS 3", "1:10: Invalid type name 3 in DIM AS statement");
        do_error_test("DIM a AS INTEGER 3", "1:18: Unexpected 3 in DIM statement");

        do_error_test("DIM a()", "1:6: Arrays require at least one dimension");
        do_error_test("DIM a(,)", "1:7: Missing expression");
        do_error_test("DIM a(, 3)", "1:7: Missing expression");
        do_error_test("DIM a(3, )", "1:10: Missing expression");
        do_error_test("DIM a(3, , 4)", "1:10: Missing expression");
        do_error_test("DIM a(1) AS INTEGER 3", "1:21: Unexpected 3 in DIM statement");
    }

    /// Wrapper around `do_ok_test` to parse an expression.  Given that expressions alone are not
    /// valid statements, we have to put them in a statement to parse them.  In doing so, we can
    /// also put an extra statement after them to ensure we detect their end properly.
    fn do_expr_ok_test(input: &str, expr: Expr) {
        do_ok_test(
            &format!("PRINT {}, 1", input),
            &[Statement::BuiltinCall(BuiltinCallSpan {
                name: "PRINT".to_owned(),
                args: vec![
                    ArgSpan { expr: Some(expr), sep: ArgSep::Long },
                    ArgSpan { expr: Some(expr_integer(1)), sep: ArgSep::End },
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
        do_expr_ok_test("TRUE", expr_boolean(true));
        do_expr_ok_test("FALSE", expr_boolean(false));
        do_expr_ok_test("5", expr_integer(5));
        do_expr_ok_test("\"some text\"", expr_text("some text"));
    }

    #[test]
    fn test_expr_symbols() {
        do_expr_ok_test("foo", expr_symbol(VarRef::new("foo", VarType::Auto)));
        do_expr_ok_test("bar$", expr_symbol(VarRef::new("bar", VarType::Text)));
    }

    #[test]
    fn test_expr_parens() {
        use Expr::*;
        do_expr_ok_test("(1)", expr_integer(1));
        do_expr_ok_test("((1))", expr_integer(1));
        do_expr_ok_test(" ( ( 1 ) ) ", expr_integer(1));
        do_expr_ok_test(
            "3 * (2 + 5)",
            Multiply(Box::from(BinaryOpSpan {
                lhs: expr_integer(3),
                rhs: Add(Box::from(BinaryOpSpan { lhs: expr_integer(2), rhs: expr_integer(5) })),
            })),
        );
        do_expr_ok_test(
            "(7) - (1) + (-2)",
            Add(Box::from(BinaryOpSpan {
                lhs: Subtract(Box::from(BinaryOpSpan {
                    lhs: expr_integer(7),
                    rhs: expr_integer(1),
                })),
                rhs: Negate(Box::from(UnaryOpSpan { expr: expr_integer(2) })),
            })),
        );
    }

    #[test]
    fn test_expr_arith_ops() {
        use Expr::*;
        let span = Box::from(BinaryOpSpan { lhs: expr_integer(1), rhs: expr_integer(2) });
        do_expr_ok_test("1 + 2", Add(span.clone()));
        do_expr_ok_test("1 - 2", Subtract(span.clone()));
        do_expr_ok_test("1 * 2", Multiply(span.clone()));
        do_expr_ok_test("1 / 2", Divide(span.clone()));
        do_expr_ok_test("1 MOD 2", Modulo(span));
    }

    #[test]
    fn test_expr_rel_ops() {
        use Expr::*;
        let span = Box::from(BinaryOpSpan { lhs: expr_integer(1), rhs: expr_integer(2) });
        do_expr_ok_test("1 = 2", Equal(span.clone()));
        do_expr_ok_test("1 <> 2", NotEqual(span.clone()));
        do_expr_ok_test("1 < 2", Less(span.clone()));
        do_expr_ok_test("1 <= 2", LessEqual(span.clone()));
        do_expr_ok_test("1 > 2", Greater(span.clone()));
        do_expr_ok_test("1 >= 2", GreaterEqual(span));
    }

    #[test]
    fn test_expr_logical_ops() {
        use Expr::*;
        let span = Box::from(BinaryOpSpan { lhs: expr_integer(1), rhs: expr_integer(2) });
        do_expr_ok_test("1 AND 2", And(span.clone()));
        do_expr_ok_test("1 OR 2", Or(span.clone()));
        do_expr_ok_test("1 XOR 2", Xor(span));
    }

    #[test]
    fn test_expr_logical_ops_not() {
        use Expr::*;
        do_expr_ok_test("NOT TRUE", Not(Box::from(UnaryOpSpan { expr: expr_boolean(true) })));
        do_expr_ok_test("NOT 6", Not(Box::from(UnaryOpSpan { expr: expr_integer(6) })));
        do_expr_ok_test(
            "NOT NOT TRUE",
            Not(Box::from(UnaryOpSpan {
                expr: Not(Box::from(UnaryOpSpan { expr: expr_boolean(true) })),
            })),
        );
        do_expr_ok_test(
            "1 - NOT 4",
            Subtract(Box::from(BinaryOpSpan {
                lhs: expr_integer(1),
                rhs: Not(Box::from(UnaryOpSpan { expr: expr_integer(4) })),
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
                    lhs: expr_integer(3),
                    rhs: Add(Box::from(BinaryOpSpan {
                        lhs: expr_integer(2),
                        rhs: expr_integer(5),
                    })),
                })),
                rhs: Xor(Box::from(BinaryOpSpan {
                    lhs: Or(Box::from(BinaryOpSpan {
                        lhs: Equal(Box::from(BinaryOpSpan {
                            lhs: Add(Box::from(BinaryOpSpan {
                                lhs: expr_integer(3),
                                rhs: expr_integer(1),
                            })),
                            rhs: expr_integer(2),
                        })),
                        rhs: Equal(Box::from(BinaryOpSpan {
                            lhs: expr_integer(1),
                            rhs: expr_integer(3),
                        })),
                    })),
                    rhs: Multiply(Box::from(BinaryOpSpan {
                        lhs: expr_boolean(false),
                        rhs: expr_text("a"),
                    })),
                })),
            })),
        );
    }

    #[test]
    fn test_expr_numeric_signs() {
        use Expr::*;

        do_expr_ok_test(
            "-a",
            Negate(Box::from(UnaryOpSpan { expr: expr_symbol(VarRef::new("a", VarType::Auto)) })),
        );

        do_expr_ok_test(
            "1 - -3",
            Subtract(Box::from(BinaryOpSpan {
                lhs: expr_integer(1),
                rhs: Negate(Box::from(UnaryOpSpan { expr: expr_integer(3) })),
            })),
        );
        do_expr_ok_test(
            "-1 - 3",
            Subtract(Box::from(BinaryOpSpan {
                lhs: Negate(Box::from(UnaryOpSpan { expr: expr_integer(1) })),
                rhs: expr_integer(3),
            })),
        );
        do_expr_ok_test(
            "5 + -1",
            Add(Box::from(BinaryOpSpan {
                lhs: expr_integer(5),
                rhs: Negate(Box::from(UnaryOpSpan { expr: expr_integer(1) })),
            })),
        );
        do_expr_ok_test(
            "-5 + 1",
            Add(Box::from(BinaryOpSpan {
                lhs: Negate(Box::from(UnaryOpSpan { expr: expr_integer(5) })),
                rhs: expr_integer(1),
            })),
        );
        do_expr_ok_test(
            "NOT -3",
            Not(Box::from(UnaryOpSpan {
                expr: Negate(Box::from(UnaryOpSpan { expr: expr_integer(3) })),
            })),
        );

        do_expr_ok_test(
            "1.0 - -3.5",
            Subtract(Box::from(BinaryOpSpan {
                lhs: expr_double(1.0),
                rhs: Negate(Box::from(UnaryOpSpan { expr: expr_double(3.5) })),
            })),
        );
        do_expr_ok_test(
            "5.12 + -0.50",
            Add(Box::from(BinaryOpSpan {
                lhs: expr_double(5.12),
                rhs: Negate(Box::from(UnaryOpSpan { expr: expr_double(0.50) })),
            })),
        );
        do_expr_ok_test(
            "NOT -3",
            Not(Box::from(UnaryOpSpan {
                expr: Negate(Box::from(UnaryOpSpan { expr: expr_integer(3) })),
            })),
        );
    }

    #[test]
    fn test_expr_functions_variadic() {
        use Expr::*;
        do_expr_ok_test(
            "zero()",
            Call(FunctionCallSpan { fref: VarRef::new("zero", VarType::Auto), args: vec![] }),
        );
        do_expr_ok_test(
            "one%(1)",
            Call(FunctionCallSpan {
                fref: VarRef::new("one", VarType::Integer),
                args: vec![expr_integer(1)],
            }),
        );
        do_expr_ok_test(
            "many$(3, \"x\", TRUE)",
            Call(FunctionCallSpan {
                fref: VarRef::new("many", VarType::Text),
                args: vec![expr_integer(3), expr_text("x"), expr_boolean(true)],
            }),
        );
    }

    #[test]
    fn test_expr_functions_nested() {
        use Expr::*;
        do_expr_ok_test(
            "consecutive(parenthesis())",
            Call(FunctionCallSpan {
                fref: VarRef::new("consecutive", VarType::Auto),
                args: vec![Call(FunctionCallSpan {
                    fref: VarRef::new("parenthesis", VarType::Auto),
                    args: vec![],
                })],
            }),
        );
        do_expr_ok_test(
            "outer?(1, inner1(2, 3), 4, inner2(), 5)",
            Call(FunctionCallSpan {
                fref: VarRef::new("outer", VarType::Boolean),
                args: vec![
                    expr_integer(1),
                    Call(FunctionCallSpan {
                        fref: VarRef::new("inner1", VarType::Auto),
                        args: vec![expr_integer(2), expr_integer(3)],
                    }),
                    expr_integer(4),
                    Call(FunctionCallSpan {
                        fref: VarRef::new("inner2", VarType::Auto),
                        args: vec![],
                    }),
                    expr_integer(5),
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
                lhs: expr_symbol(VarRef::new("b".to_owned(), VarType::Auto)),
                rhs: Call(FunctionCallSpan {
                    fref: VarRef::new("ask", VarType::Boolean),
                    args: vec![
                        Add(Box::from(BinaryOpSpan {
                            lhs: expr_integer(34),
                            rhs: expr_integer(15),
                        })),
                        Call(FunctionCallSpan {
                            fref: VarRef::new("ask", VarType::Auto),
                            args: vec![expr_integer(1), expr_boolean(false)],
                        }),
                        Negate(Box::from(UnaryOpSpan { expr: expr_integer(5) })),
                    ],
                }),
            })),
        );
    }

    #[test]
    fn test_expr_functions_not_confused_with_symbols() {
        use Expr::*;
        let iref = VarRef::new("i", VarType::Auto);
        let jref = VarRef::new("j", VarType::Auto);
        do_expr_ok_test(
            "i = 0 OR i = (j - 1)",
            Or(Box::from(BinaryOpSpan {
                lhs: Equal(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iref.clone()),
                    rhs: expr_integer(0),
                })),
                rhs: Equal(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iref),
                    rhs: Subtract(Box::from(BinaryOpSpan {
                        lhs: expr_symbol(jref),
                        rhs: expr_integer(1),
                    })),
                })),
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
        do_expr_error_test("(()", "1:8: Missing expression");
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
        do_expr_error_test("((), ())", "1:8: Missing expression");

        // TODO(jmmv): This succeeds because `PRINT` is interned as a `Token::Symbol` so the
        // expression parser sees it as a variable reference... but this should probably fail.
        // Would need to intern builtin call names as a separate token to catch this, but that
        // also means that the lexer must be aware of builtin call names upfront.
        use Expr::*;
        do_expr_ok_test(
            "1 + PRINT",
            Add(Box::from(BinaryOpSpan {
                lhs: expr_integer(1),
                rhs: expr_symbol(VarRef::new("PRINT", VarType::Auto)),
            })),
        );
    }

    #[test]
    fn test_expr_errors_due_to_keywords() {
        for kw in &[
            "AS", "BOOLEAN", "DIM", "DOUBLE", "ELSE", "ELSEIF", "END", "FOR", "IF", "INTEGER",
            "NEXT", "STRING", "WHILE",
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
                branches: vec![IfBranchSpan { guard: expr_integer(1), body: vec![] }],
            })],
        );
        do_ok_test(
            "IF 1 THEN\nREM Some comment to skip over\n\nEND IF",
            &[Statement::If(IfSpan {
                branches: vec![IfBranchSpan { guard: expr_integer(1), body: vec![] }],
            })],
        );
        do_ok_test(
            "IF 1 THEN\nELSEIF 2 THEN\nEND IF",
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan { guard: expr_integer(1), body: vec![] },
                    IfBranchSpan { guard: expr_integer(2), body: vec![] },
                ],
            })],
        );
        do_ok_test(
            "IF 1 THEN\nELSEIF 2 THEN\nELSE\nEND IF",
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan { guard: expr_integer(1), body: vec![] },
                    IfBranchSpan { guard: expr_integer(2), body: vec![] },
                    IfBranchSpan { guard: expr_boolean(true), body: vec![] },
                ],
            })],
        );
        do_ok_test(
            "IF 1 THEN\nELSE\nEND IF",
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan { guard: expr_integer(1), body: vec![] },
                    IfBranchSpan { guard: expr_boolean(true), body: vec![] },
                ],
            })],
        );
    }

    /// Helper to instantiate a trivial `Statement::BuiltinCall` that has no arguments.
    fn make_bare_builtin_call(name: &str) -> Statement {
        Statement::BuiltinCall(BuiltinCallSpan { name: name.to_owned(), args: vec![] })
    }

    #[test]
    fn test_if_with_one_statement_or_empty_lines() {
        do_ok_test(
            "IF 1 THEN\nPRINT\nEND IF",
            &[Statement::If(IfSpan {
                branches: vec![IfBranchSpan {
                    guard: expr_integer(1),
                    body: vec![make_bare_builtin_call("PRINT")],
                }],
            })],
        );
        do_ok_test(
            "IF 1 THEN\nREM foo\nELSEIF 2 THEN\nPRINT\nEND IF",
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan { guard: expr_integer(1), body: vec![] },
                    IfBranchSpan {
                        guard: expr_integer(2),
                        body: vec![make_bare_builtin_call("PRINT")],
                    },
                ],
            })],
        );
        do_ok_test(
            "IF 1 THEN\nELSEIF 2 THEN\nELSE\n\nPRINT\nEND IF",
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan { guard: expr_integer(1), body: vec![] },
                    IfBranchSpan { guard: expr_integer(2), body: vec![] },
                    IfBranchSpan {
                        guard: expr_boolean(true),
                        body: vec![make_bare_builtin_call("PRINT")],
                    },
                ],
            })],
        );
        do_ok_test(
            "IF 1 THEN\n\n\nELSE\nPRINT\nEND IF",
            &[Statement::If(IfSpan {
                branches: vec![
                    IfBranchSpan { guard: expr_integer(1), body: vec![] },
                    IfBranchSpan {
                        guard: expr_boolean(true),
                        body: vec![make_bare_builtin_call("PRINT")],
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
                        guard: expr_integer(1),
                        body: vec![make_bare_builtin_call("A"), make_bare_builtin_call("B")],
                    },
                    IfBranchSpan {
                        guard: expr_integer(2),
                        body: vec![make_bare_builtin_call("C"), make_bare_builtin_call("D")],
                    },
                    IfBranchSpan {
                        guard: expr_integer(3),
                        body: vec![make_bare_builtin_call("E"), make_bare_builtin_call("F")],
                    },
                    IfBranchSpan {
                        guard: expr_boolean(true),
                        body: vec![make_bare_builtin_call("G"), make_bare_builtin_call("H")],
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
                        guard: expr_integer(1),
                        body: vec![make_bare_builtin_call("A")],
                    },
                    IfBranchSpan {
                        guard: expr_integer(2),
                        body: vec![Statement::If(IfSpan {
                            branches: vec![IfBranchSpan {
                                guard: expr_integer(3),
                                body: vec![make_bare_builtin_call("B")],
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
        do_error_test("IF 3 + 1 THEN", "1:14: Expecting newline after THEN");

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

        do_error_test(
            "IF 1 THEN\nELSE\nELSEIF 2 THEN\nEND IF",
            "3:1: Unexpected ELSEIF after ELSE",
        );
        do_error_test("IF 1 THEN\nELSE\nELSE\nEND IF", "3:1: Duplicate ELSE after ELSE");

        do_error_test_no_reset("ELSEIF 1 THEN\nEND IF", "1:1: Unexpected ELSEIF in statement");
        do_error_test_no_reset("ELSE 1\nEND IF", "1:1: Unexpected ELSE in statement");
    }

    #[test]
    fn test_for_empty() {
        let auto_iter = VarRef::new("i", VarType::Auto);
        do_ok_test(
            "FOR i = 1 TO 10\nNEXT",
            &[Statement::For(ForSpan {
                iter: auto_iter.clone(),
                start: expr_integer(1),
                end: Expr::LessEqual(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(auto_iter.clone()),
                    rhs: expr_integer(10),
                })),
                next: Expr::Add(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(auto_iter),
                    rhs: expr_integer(1),
                })),
                body: vec![],
            })],
        );

        let typed_iter = VarRef::new("i", VarType::Integer);
        do_ok_test(
            "FOR i% = 1 TO 10\nREM Nothing to do\nNEXT",
            &[Statement::For(ForSpan {
                iter: typed_iter.clone(),
                start: expr_integer(1),
                end: Expr::LessEqual(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(typed_iter.clone()),
                    rhs: expr_integer(10),
                })),
                next: Expr::Add(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(typed_iter),
                    rhs: expr_integer(1),
                })),
                body: vec![],
            })],
        );
    }

    #[test]
    fn test_for_incrementing() {
        let iter = VarRef::new("i", VarType::Auto);
        do_ok_test(
            "FOR i = 0 TO 5\nA\nB\nNEXT",
            &[Statement::For(ForSpan {
                iter: iter.clone(),
                start: expr_integer(0),
                end: Expr::LessEqual(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iter.clone()),
                    rhs: expr_integer(5),
                })),
                next: Expr::Add(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iter),
                    rhs: expr_integer(1),
                })),
                body: vec![make_bare_builtin_call("A"), make_bare_builtin_call("B")],
            })],
        );
    }

    #[test]
    fn test_for_incrementing_with_step() {
        let iter = VarRef::new("i", VarType::Auto);
        do_ok_test(
            "FOR i = 0 TO 5 STEP 2\nA\nNEXT",
            &[Statement::For(ForSpan {
                iter: iter.clone(),
                start: expr_integer(0),
                end: Expr::LessEqual(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iter.clone()),
                    rhs: expr_integer(5),
                })),
                next: Expr::Add(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iter),
                    rhs: expr_integer(2),
                })),
                body: vec![make_bare_builtin_call("A")],
            })],
        );
    }

    #[test]
    fn test_for_decrementing_with_step() {
        let iter = VarRef::new("i", VarType::Auto);
        do_ok_test(
            "FOR i = 5 TO 0 STEP -1\nA\nNEXT",
            &[Statement::For(ForSpan {
                iter: iter.clone(),
                start: expr_integer(5),
                end: Expr::GreaterEqual(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iter.clone()),
                    rhs: expr_integer(0),
                })),
                next: Expr::Add(Box::from(BinaryOpSpan {
                    lhs: expr_symbol(iter),
                    rhs: expr_integer(-1),
                })),
                body: vec![make_bare_builtin_call("A")],
            })],
        );
    }

    #[test]
    fn test_for_errors() {
        do_error_test("FOR\n", "1:4: No iterator name in FOR statement");
        do_error_test("FOR =\n", "1:5: No iterator name in FOR statement");
        do_error_test(
            "FOR a$\n",
            "1:5: Iterator name in FOR statement must be an integer reference",
        );
        do_error_test(
            "FOR d#\n",
            "1:5: Iterator name in FOR statement must be an integer reference",
        );

        do_error_test("FOR i 3\n", "1:7: No equal sign in FOR statement");
        do_error_test("FOR i = TO\n", "1:9: No start expression in FOR statement");
        do_error_test("FOR i = NEXT\n", "1:9: Unexpected keyword in expression");

        do_error_test("FOR i = 3 STEP\n", "1:11: No TO in FOR statement");
        do_error_test("FOR i = 3 TO STEP\n", "1:14: No end expression in FOR statement");
        do_error_test("FOR i = 3 TO NEXT\n", "1:14: Unexpected keyword in expression");

        do_error_test("FOR i = 3 TO 1 STEP a\n", "1:21: STEP needs an integer");
        do_error_test("FOR i = 3 TO 1 STEP -a\n", "1:22: STEP needs an integer");
        do_error_test("FOR i = 3 TO 1 STEP NEXT\n", "1:21: STEP needs an integer");
        do_error_test("FOR i = 3 TO 1 STEP 0\n", "1:21: Infinite FOR loop; STEP cannot be 0");

        do_error_test("FOR i = 3 TO 1", "1:15: Expecting newline after FOR");
        do_error_test("FOR i = 1 TO 3 STEP 1", "1:22: Expecting newline after FOR");
        do_error_test("FOR i = 3 TO 1 STEP -1", "1:23: Expecting newline after FOR");

        do_error_test("    FOR i = 0 TO 10\nPRINT i\n", "1:5: FOR without NEXT");
    }

    #[test]
    fn test_goto_ok() {
        do_ok_test("GOTO @foo", &[Statement::Goto(GotoSpan { target: "foo".to_owned() })]);
    }

    #[test]
    fn test_goto_errors() {
        do_error_test("GOTO\n", "1:5: Expected label name after GOTO");
        do_error_test("GOTO 3\n", "1:6: Expected label name after GOTO");
        do_error_test("GOTO foo\n", "1:6: Expected label name after GOTO");
        do_error_test("GOTO \"foo\"\n", "1:6: Expected label name after GOTO");
        do_error_test("GOTO @foo, @bar\n", "1:10: Expected newline but found ,");
        do_error_test("GOTO @foo, 3\n", "1:10: Expected newline but found ,");
    }

    #[test]
    fn test_label_ok() {
        do_ok_test("@foo", &[Statement::Label(LabelSpan { name: "foo".to_owned() })]);
    }

    #[test]
    fn test_label_errors() {
        do_error_test("@foo PRINT", "1:6: Expected newline but found PRINT");
        do_error_test("@foo+", "1:5: Expected newline but found +");
    }

    #[test]
    fn test_while_empty() {
        do_ok_test(
            "WHILE 2 + 3\nWEND",
            &[Statement::While(WhileSpan {
                expr: Expr::Add(Box::from(BinaryOpSpan {
                    lhs: expr_integer(2),
                    rhs: expr_integer(3),
                })),
                body: vec![],
            })],
        );
        do_ok_test(
            "WHILE 5\n\nREM foo\n\nWEND\n",
            &[Statement::While(WhileSpan { expr: expr_integer(5), body: vec![] })],
        );
    }

    #[test]
    fn test_while_loops() {
        do_ok_test(
            "WHILE TRUE\nA\nB\nWEND",
            &[Statement::While(WhileSpan {
                expr: expr_boolean(true),
                body: vec![make_bare_builtin_call("A"), make_bare_builtin_call("B")],
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
                expr: expr_boolean(true),
                body: vec![
                    make_bare_builtin_call("A"),
                    Statement::While(WhileSpan {
                        expr: expr_boolean(false),
                        body: vec![make_bare_builtin_call("B")],
                    }),
                    make_bare_builtin_call("C"),
                ],
            })],
        );
    }

    #[test]
    fn test_while_errors() {
        do_error_test("WHILE\n", "1:6: No expression in WHILE statement");
        do_error_test("WHILE TRUE", "1:11: Expecting newline after WHILE");
        do_error_test("\n\nWHILE TRUE\n", "3:1: WHILE without WEND");
        do_error_test("WHILE TRUE\nEND", "2:1: Unexpected END in statement");
        do_error_test("WHILE TRUE\nEND\n", "2:1: Unexpected END in statement");
        do_error_test("WHILE TRUE\nEND WHILE\n", "2:1: Unexpected END in statement");

        do_error_test("WHILE ,\nWEND", "1:7: No expression in WHILE statement");
    }
}
