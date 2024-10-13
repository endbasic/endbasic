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

//! Tokenizer for the EndBASIC language.

use crate::ast::{ExprType, VarRef};
use crate::reader::{CharReader, CharSpan, LineCol};
use std::{fmt, io};

/// Result type for the public methods of this module.
type Result<T> = std::result::Result<T, (LineCol, io::Error)>;

/// Collection of valid tokens.
///
/// Of special interest are the `Eof` and `Bad` tokens, both of which denote exceptional
/// conditions and require special care.  `Eof` indicates that there are no more tokens.
/// `Bad` indicates that a token was bad and contains the reason behind the problem, but the
/// stream remains valid for extraction of further tokens.
#[derive(Clone, PartialEq)]
#[cfg_attr(test, derive(Debug))]
pub enum Token {
    Eof,
    Eol,
    Bad(String),

    Boolean(bool),
    Double(f64),
    Integer(i32),
    Text(String),
    Symbol(VarRef),

    Label(String),

    Comma,
    Semicolon,
    LeftParen,
    RightParen,

    Plus,
    Minus,
    Multiply,
    Divide,
    Modulo,
    Exponent,

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

    Case,
    Data,
    Do,
    Else,
    Elseif,
    End,
    Error,
    Exit,
    For,
    Function,
    Gosub,
    Goto,
    If,
    Is,
    Loop,
    Next,
    On,
    Resume,
    Return,
    Select,
    Sub,
    Step,
    Then,
    To,
    Until,
    Wend,
    While,

    Dim,
    Shared,
    As,
    BooleanName,
    DoubleName,
    IntegerName,
    TextName,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // This implementation of Display returns the "canonical format" of a token.  We could
        // instead capture the original text that was in the input stream and store it in the
        // TokenSpan and return that.  However, most BASIC implementations make input canonical
        // so this helps achieve that goal.
        match self {
            Token::Eof => write!(f, "<<EOF>>"),
            Token::Eol => write!(f, "<<NEWLINE>>"),
            Token::Bad(s) => write!(f, "<<{}>>", s),

            Token::Boolean(false) => write!(f, "FALSE"),
            Token::Boolean(true) => write!(f, "TRUE"),
            Token::Double(d) => write!(f, "{}", d),
            Token::Integer(i) => write!(f, "{}", i),
            Token::Text(t) => write!(f, "{}", t),
            Token::Symbol(vref) => write!(f, "{}", vref),

            Token::Label(l) => write!(f, "@{}", l),

            Token::Comma => write!(f, ","),
            Token::Semicolon => write!(f, ";"),
            Token::LeftParen => write!(f, "("),
            Token::RightParen => write!(f, ")"),

            Token::Plus => write!(f, "+"),
            Token::Minus => write!(f, "-"),
            Token::Multiply => write!(f, "*"),
            Token::Divide => write!(f, "/"),
            Token::Modulo => write!(f, "MOD"),
            Token::Exponent => write!(f, "^"),

            Token::Equal => write!(f, "="),
            Token::NotEqual => write!(f, "<>"),
            Token::Less => write!(f, "<"),
            Token::LessEqual => write!(f, "<="),
            Token::Greater => write!(f, ">"),
            Token::GreaterEqual => write!(f, ">="),

            Token::And => write!(f, "AND"),
            Token::Not => write!(f, "NOT"),
            Token::Or => write!(f, "OR"),
            Token::Xor => write!(f, "XOR"),

            Token::ShiftLeft => write!(f, "<<"),
            Token::ShiftRight => write!(f, ">>"),

            Token::Case => write!(f, "CASE"),
            Token::Data => write!(f, "DATA"),
            Token::Do => write!(f, "DO"),
            Token::Else => write!(f, "ELSE"),
            Token::Elseif => write!(f, "ELSEIF"),
            Token::End => write!(f, "END"),
            Token::Error => write!(f, "ERROR"),
            Token::Exit => write!(f, "EXIT"),
            Token::For => write!(f, "FOR"),
            Token::Function => write!(f, "FUNCTION"),
            Token::Gosub => write!(f, "GOSUB"),
            Token::Goto => write!(f, "GOTO"),
            Token::If => write!(f, "IF"),
            Token::Is => write!(f, "IS"),
            Token::Loop => write!(f, "LOOP"),
            Token::Next => write!(f, "NEXT"),
            Token::On => write!(f, "ON"),
            Token::Resume => write!(f, "RESUME"),
            Token::Return => write!(f, "RETURN"),
            Token::Select => write!(f, "SELECT"),
            Token::Sub => write!(f, "SUB"),
            Token::Step => write!(f, "STEP"),
            Token::Then => write!(f, "THEN"),
            Token::To => write!(f, "TO"),
            Token::Until => write!(f, "UNTIL"),
            Token::Wend => write!(f, "WEND"),
            Token::While => write!(f, "WHILE"),

            Token::Dim => write!(f, "DIM"),
            Token::Shared => write!(f, "SHARED"),
            Token::As => write!(f, "AS"),
            Token::BooleanName => write!(f, "BOOLEAN"),
            Token::DoubleName => write!(f, "DOUBLE"),
            Token::IntegerName => write!(f, "INTEGER"),
            Token::TextName => write!(f, "STRING"),
        }
    }
}

/// Extra operations to test properties of a `char` based on the language semantics.
trait CharOps {
    /// Returns true if the current character should be considered as finishing a previous token.
    fn is_separator(&self) -> bool;

    /// Returns true if the character is a space.
    ///
    /// Use this instead of `is_whitespace`, which accounts for newlines but we need to handle
    /// those explicitly.
    fn is_space(&self) -> bool;

    /// Returns true if the character can be part of an identifier.
    fn is_word(&self) -> bool;
}

impl CharOps for char {
    fn is_separator(&self) -> bool {
        match *self {
            '\n' | ':' | '(' | ')' | '\'' | '=' | '<' | '>' | ';' | ',' | '+' | '-' | '*' | '/'
            | '^' => true,
            ch => ch.is_space(),
        }
    }

    fn is_space(&self) -> bool {
        // TODO(jmmv): This is probably not correct regarding UTF-8 when comparing this function to
        // the `is_whitespace` builtin.  Figure out if that's true and what to do about it.
        matches!(*self, ' ' | '\t' | '\r')
    }

    fn is_word(&self) -> bool {
        match *self {
            '_' => true,
            ch => ch.is_alphanumeric(),
        }
    }
}

/// Container for a token and its context.
///
/// Note that the "context" is not truly available for some tokens such as `Token::Eof`, but we can
/// synthesize one for simplicity.  Otherwise, we would need to extend the `Token` enum so that
/// every possible token contains extra fields, and that would be too complex.
#[cfg_attr(test, derive(PartialEq))]
pub struct TokenSpan {
    /// The token itself.
    pub(crate) token: Token,

    /// Start position of the token.
    pub(crate) pos: LineCol,

    /// Length of the token in characters.
    #[allow(unused)] // TODO(jmmv): Use this in the parser.
    length: usize,
}

impl TokenSpan {
    /// Creates a new `TokenSpan` from its parts.
    fn new(token: Token, pos: LineCol, length: usize) -> Self {
        Self { token, pos, length }
    }
}

/// Iterator over the tokens of the language.
pub struct Lexer<'a> {
    /// Peekable iterator over the characters to scan.
    input: CharReader<'a>,
}

impl<'a> Lexer<'a> {
    /// Creates a new lexer from the given readable.
    pub fn from(input: &'a mut dyn io::Read) -> Self {
        Self { input: CharReader::from(input) }
    }

    /// Handles an `input.next()` call that returned an unexpected character.
    ///
    /// This returns a `Token::Bad` with the provided `msg` and skips characters in the input
    /// stream until a field separator is found.
    fn handle_bad_read<S: Into<String>>(
        &mut self,
        msg: S,
        first_pos: LineCol,
    ) -> io::Result<TokenSpan> {
        let mut len = 1;
        loop {
            match self.input.peek() {
                Some(Ok(ch_span)) if ch_span.ch.is_separator() => break,
                Some(Ok(_)) => {
                    self.input.next().unwrap()?;
                    len += 1;
                }
                Some(Err(_)) => return Err(self.input.next().unwrap().unwrap_err()),
                None => break,
            }
        }
        Ok(TokenSpan::new(Token::Bad(msg.into()), first_pos, len))
    }

    /// Consumes the number at the current position, whose first digit is `first`.
    fn consume_number(&mut self, first: CharSpan) -> io::Result<TokenSpan> {
        let mut s = String::new();
        let mut found_dot = false;
        s.push(first.ch);
        loop {
            match self.input.peek() {
                Some(Ok(ch_span)) => match ch_span.ch {
                    '.' => {
                        if found_dot {
                            self.input.next().unwrap()?;
                            return self
                                .handle_bad_read("Too many dots in numeric literal", first.pos);
                        }
                        s.push(self.input.next().unwrap()?.ch);
                        found_dot = true;
                    }
                    ch if ch.is_ascii_digit() => s.push(self.input.next().unwrap()?.ch),
                    ch if ch.is_separator() => break,
                    ch => {
                        self.input.next().unwrap()?;
                        let msg = format!("Unexpected character in numeric literal: {}", ch);
                        return self.handle_bad_read(msg, first.pos);
                    }
                },
                Some(Err(_)) => return Err(self.input.next().unwrap().unwrap_err()),
                None => break,
            }
        }
        if found_dot {
            if s.ends_with('.') {
                // TODO(jmmv): Reconsider supporting double literals with a . that is not prefixed
                // by a number or not followed by a number.  For now, mimic the error we get when
                // we encounter a dot not prefixed by a number.
                return self.handle_bad_read("Unknown character: .", first.pos);
            }
            match s.parse::<f64>() {
                Ok(d) => Ok(TokenSpan::new(Token::Double(d), first.pos, s.len())),
                Err(e) => self.handle_bad_read(format!("Bad double {}: {}", s, e), first.pos),
            }
        } else {
            match s.parse::<i32>() {
                Ok(i) => Ok(TokenSpan::new(Token::Integer(i), first.pos, s.len())),
                Err(e) => self.handle_bad_read(format!("Bad integer {}: {}", s, e), first.pos),
            }
        }
    }

    /// Consumes the integer at the current position, whose first digit is `first` and which is
    /// expected to be expressed in the given `base`.  `prefix_len` indicates how many characters
    /// were already consumed for this token, without counting `first`.
    fn consume_integer(
        &mut self,
        base: u8,
        pos: LineCol,
        prefix_len: usize,
    ) -> io::Result<TokenSpan> {
        let mut s = String::new();
        loop {
            match self.input.peek() {
                Some(Ok(ch_span)) => match ch_span.ch {
                    '.' => {
                        self.input.next().unwrap()?;
                        return self
                            .handle_bad_read("Numbers in base syntax must be integers", pos);
                    }
                    ch if ch.is_ascii_digit() => s.push(self.input.next().unwrap()?.ch),
                    'a'..='f' | 'A'..='F' => s.push(self.input.next().unwrap()?.ch),
                    ch if ch.is_separator() => break,
                    ch => {
                        self.input.next().unwrap()?;
                        let msg = format!("Unexpected character in numeric literal: {}", ch);
                        return self.handle_bad_read(msg, pos);
                    }
                },
                Some(Err(_)) => return Err(self.input.next().unwrap().unwrap_err()),
                None => break,
            }
        }
        if s.is_empty() {
            return self.handle_bad_read("No digits in integer literal", pos);
        }

        match u32::from_str_radix(&s, u32::from(base)) {
            Ok(i) => Ok(TokenSpan::new(Token::Integer(i as i32), pos, s.len() + prefix_len)),
            Err(e) => self.handle_bad_read(format!("Bad integer {}: {}", s, e), pos),
        }
    }

    /// Consumes the integer at the current position `pos`.
    fn consume_integer_with_base(&mut self, pos: LineCol) -> io::Result<TokenSpan> {
        let mut prefix_len = 1; // Count '&'.

        let base = match self.input.peek() {
            Some(Ok(ch_span)) => {
                let base = match ch_span.ch {
                    'b' | 'B' => 2,
                    'd' | 'D' => 10,
                    'o' | 'O' => 8,
                    'x' | 'X' => 16,
                    ch if ch.is_separator() => {
                        return self.handle_bad_read("Missing base in integer literal", pos);
                    }
                    _ => {
                        let ch_span = self.input.next().unwrap()?;
                        return self.handle_bad_read(
                            format!("Unknown base {} in integer literal", ch_span.ch),
                            pos,
                        );
                    }
                };
                self.input.next().unwrap()?;
                base
            }
            Some(Err(_)) => return Err(self.input.next().unwrap().unwrap_err()),
            None => {
                return self.handle_bad_read("Incomplete integer due to EOF", pos);
            }
        };
        prefix_len += 1; // Count the base.

        match self.input.peek() {
            Some(Ok(ch_span)) if ch_span.ch == '_' => {
                self.input.next().unwrap().unwrap();
                prefix_len += 1; // Count the '_'.
            }
            Some(Ok(_ch_span)) => (),
            Some(Err(_)) => return Err(self.input.next().unwrap().unwrap_err()),
            None => return self.handle_bad_read("Incomplete integer due to EOF", pos),
        }

        self.consume_integer(base, pos, prefix_len)
    }

    /// Consumes the operator at the current position, whose first character is `first`.
    fn consume_operator(&mut self, first: CharSpan) -> io::Result<TokenSpan> {
        match (first.ch, self.input.peek()) {
            (_, Some(Err(_))) => Err(self.input.next().unwrap().unwrap_err()),

            ('<', Some(Ok(ch_span))) if ch_span.ch == '>' => {
                self.input.next().unwrap()?;
                Ok(TokenSpan::new(Token::NotEqual, first.pos, 2))
            }

            ('<', Some(Ok(ch_span))) if ch_span.ch == '=' => {
                self.input.next().unwrap()?;
                Ok(TokenSpan::new(Token::LessEqual, first.pos, 2))
            }
            ('<', Some(Ok(ch_span))) if ch_span.ch == '<' => {
                self.input.next().unwrap()?;
                Ok(TokenSpan::new(Token::ShiftLeft, first.pos, 2))
            }
            ('<', _) => Ok(TokenSpan::new(Token::Less, first.pos, 1)),

            ('>', Some(Ok(ch_span))) if ch_span.ch == '=' => {
                self.input.next().unwrap()?;
                Ok(TokenSpan::new(Token::GreaterEqual, first.pos, 2))
            }
            ('>', Some(Ok(ch_span))) if ch_span.ch == '>' => {
                self.input.next().unwrap()?;
                Ok(TokenSpan::new(Token::ShiftRight, first.pos, 2))
            }
            ('>', _) => Ok(TokenSpan::new(Token::Greater, first.pos, 1)),

            (_, _) => panic!("Should not have been called"),
        }
    }

    /// Consumes the symbol or keyword at the current position, whose first letter is `first`.
    ///
    /// The symbol may be a bare name, but it may also contain an optional type annotation.
    fn consume_symbol(&mut self, first: CharSpan) -> io::Result<TokenSpan> {
        let mut s = String::new();
        s.push(first.ch);
        let mut vtype = None;
        let mut token_len = 0;
        loop {
            match self.input.peek() {
                Some(Ok(ch_span)) => match ch_span.ch {
                    ch if ch.is_word() => s.push(self.input.next().unwrap()?.ch),
                    ch if ch.is_separator() => break,
                    '?' => {
                        vtype = Some(ExprType::Boolean);
                        self.input.next().unwrap()?;
                        token_len += 1;
                        break;
                    }
                    '#' => {
                        vtype = Some(ExprType::Double);
                        self.input.next().unwrap()?;
                        token_len += 1;
                        break;
                    }
                    '%' => {
                        vtype = Some(ExprType::Integer);
                        self.input.next().unwrap()?;
                        token_len += 1;
                        break;
                    }
                    '$' => {
                        vtype = Some(ExprType::Text);
                        self.input.next().unwrap()?;
                        token_len += 1;
                        break;
                    }
                    ch => {
                        self.input.next().unwrap()?;
                        let msg = format!("Unexpected character in symbol: {}", ch);
                        return self.handle_bad_read(msg, first.pos);
                    }
                },
                Some(Err(_)) => return Err(self.input.next().unwrap().unwrap_err()),
                None => break,
            }
        }
        debug_assert!(token_len <= 1);

        token_len += s.len();
        let token = match s.to_uppercase().as_str() {
            "AND" => Token::And,
            "AS" => Token::As,
            "BOOLEAN" => Token::BooleanName,
            "CASE" => Token::Case,
            "DATA" => Token::Data,
            "DIM" => Token::Dim,
            "DO" => Token::Do,
            "DOUBLE" => Token::DoubleName,
            "ELSE" => Token::Else,
            "ELSEIF" => Token::Elseif,
            "END" => Token::End,
            "ERROR" => Token::Error,
            "EXIT" => Token::Exit,
            "FALSE" => Token::Boolean(false),
            "FOR" => Token::For,
            "FUNCTION" => Token::Function,
            "GOSUB" => Token::Gosub,
            "GOTO" => Token::Goto,
            "IF" => Token::If,
            "IS" => Token::Is,
            "INTEGER" => Token::IntegerName,
            "LOOP" => Token::Loop,
            "MOD" => Token::Modulo,
            "NEXT" => Token::Next,
            "NOT" => Token::Not,
            "ON" => Token::On,
            "OR" => Token::Or,
            "REM" => return self.consume_rest_of_line(),
            "RESUME" => Token::Resume,
            "RETURN" => Token::Return,
            "SELECT" => Token::Select,
            "SHARED" => Token::Shared,
            "STEP" => Token::Step,
            "STRING" => Token::TextName,
            "SUB" => Token::Sub,
            "THEN" => Token::Then,
            "TO" => Token::To,
            "TRUE" => Token::Boolean(true),
            "UNTIL" => Token::Until,
            "WEND" => Token::Wend,
            "WHILE" => Token::While,
            "XOR" => Token::Xor,
            _ => Token::Symbol(VarRef::new(s, vtype)),
        };
        Ok(TokenSpan::new(token, first.pos, token_len))
    }

    /// Consumes the string at the current position, which was has to end with the same opening
    /// character as specified by `delim`.
    ///
    /// This handles quoted characters within the string.
    fn consume_text(&mut self, delim: CharSpan) -> io::Result<TokenSpan> {
        let mut s = String::new();
        let mut escaping = false;
        loop {
            match self.input.peek() {
                Some(Ok(ch_span)) => {
                    if escaping {
                        s.push(self.input.next().unwrap()?.ch);
                        escaping = false;
                    } else if ch_span.ch == '\\' {
                        self.input.next().unwrap()?;
                        escaping = true;
                    } else if ch_span.ch == delim.ch {
                        self.input.next().unwrap()?;
                        break;
                    } else {
                        s.push(self.input.next().unwrap()?.ch);
                    }
                }
                Some(Err(_)) => return Err(self.input.next().unwrap().unwrap_err()),
                None => {
                    return self.handle_bad_read(
                        format!("Incomplete string due to EOF: {}", s),
                        delim.pos,
                    );
                }
            }
        }
        let token_len = s.len() + 2;
        Ok(TokenSpan::new(Token::Text(s), delim.pos, token_len))
    }

    /// Consumes the label definition at the current position.
    fn consume_label(&mut self, first: CharSpan) -> io::Result<TokenSpan> {
        let mut s = String::new();

        match self.input.peek() {
            Some(Ok(ch_span)) => match ch_span.ch {
                ch if ch.is_word() && !ch.is_numeric() => s.push(self.input.next().unwrap()?.ch),
                _ch => (),
            },
            Some(Err(_)) => return Err(self.input.next().unwrap().unwrap_err()),
            None => (),
        }
        if s.is_empty() {
            return Ok(TokenSpan::new(Token::Bad("Empty label name".to_owned()), first.pos, 1));
        }

        loop {
            match self.input.peek() {
                Some(Ok(ch_span)) => match ch_span.ch {
                    ch if ch.is_word() => s.push(self.input.next().unwrap()?.ch),
                    ch if ch.is_separator() => break,
                    ch => {
                        let msg = format!("Unexpected character in label: {}", ch);
                        return self.handle_bad_read(msg, first.pos);
                    }
                },
                Some(Err(_)) => return Err(self.input.next().unwrap().unwrap_err()),
                None => break,
            }
        }

        let token_len = s.len() + 1;
        Ok(TokenSpan::new(Token::Label(s), first.pos, token_len))
    }

    /// Consumes the remainder of the line and returns the token that was encountered at the end
    /// (which may be EOF or end of line).
    fn consume_rest_of_line(&mut self) -> io::Result<TokenSpan> {
        loop {
            match self.input.next() {
                None => {
                    let last_pos = self.input.next_pos();
                    return Ok(TokenSpan::new(Token::Eof, last_pos, 0));
                }
                Some(Ok(ch_span)) if ch_span.ch == '\n' => {
                    return Ok(TokenSpan::new(Token::Eol, ch_span.pos, 1))
                }
                Some(Err(e)) => return Err(e),
                Some(Ok(_)) => (),
            }
        }
    }

    /// Skips whitespace until it finds the beginning of the next token, and returns its first
    /// character.
    fn advance_and_read_next(&mut self) -> io::Result<Option<CharSpan>> {
        loop {
            match self.input.next() {
                Some(Ok(ch_span)) if ch_span.ch.is_space() => (),
                Some(Ok(ch_span)) => return Ok(Some(ch_span)),
                Some(Err(e)) => return Err(e),
                None => return Ok(None),
            }
        }
    }

    /// Reads the next token from the input stream.
    ///
    /// Note that this returns errors only on fatal I/O conditions.  EOF and malformed tokens are
    /// both returned as the special token types `Token::Eof` and `Token::Bad` respectively.
    pub fn read(&mut self) -> io::Result<TokenSpan> {
        let ch_span = self.advance_and_read_next()?;
        if ch_span.is_none() {
            let last_pos = self.input.next_pos();
            return Ok(TokenSpan::new(Token::Eof, last_pos, 0));
        }
        let ch_span = ch_span.unwrap();
        match ch_span.ch {
            '\n' | ':' => Ok(TokenSpan::new(Token::Eol, ch_span.pos, 1)),
            '\'' => self.consume_rest_of_line(),

            '"' => self.consume_text(ch_span),

            ';' => Ok(TokenSpan::new(Token::Semicolon, ch_span.pos, 1)),
            ',' => Ok(TokenSpan::new(Token::Comma, ch_span.pos, 1)),

            '(' => Ok(TokenSpan::new(Token::LeftParen, ch_span.pos, 1)),
            ')' => Ok(TokenSpan::new(Token::RightParen, ch_span.pos, 1)),

            '+' => Ok(TokenSpan::new(Token::Plus, ch_span.pos, 1)),
            '-' => Ok(TokenSpan::new(Token::Minus, ch_span.pos, 1)),
            '*' => Ok(TokenSpan::new(Token::Multiply, ch_span.pos, 1)),
            '/' => Ok(TokenSpan::new(Token::Divide, ch_span.pos, 1)),
            '^' => Ok(TokenSpan::new(Token::Exponent, ch_span.pos, 1)),

            '=' => Ok(TokenSpan::new(Token::Equal, ch_span.pos, 1)),
            '<' | '>' => self.consume_operator(ch_span),

            '@' => self.consume_label(ch_span),

            '&' => self.consume_integer_with_base(ch_span.pos),

            ch if ch.is_ascii_digit() => self.consume_number(ch_span),
            ch if ch.is_word() => self.consume_symbol(ch_span),
            ch => self.handle_bad_read(format!("Unknown character: {}", ch), ch_span.pos),
        }
    }

    /// Returns a peekable adaptor for this lexer.
    pub fn peekable(self) -> PeekableLexer<'a> {
        PeekableLexer { lexer: self, peeked: None }
    }
}

/// Wraps a `Lexer` and offers peeking abilities.
///
/// Ideally, the `Lexer` would be an `Iterator` which would give us access to the standard
/// `Peekable` interface, but the ergonomics of that when dealing with a `Fallible` are less than
/// optimal.  Hence we implement our own.
pub struct PeekableLexer<'a> {
    /// The wrapped lexer instance.
    lexer: Lexer<'a>,

    /// If not none, contains the character read by `peek`, which will be consumed by the next call
    /// to `read` or `consume_peeked`.
    peeked: Option<TokenSpan>,
}

impl<'a> PeekableLexer<'a> {
    /// Reads the previously-peeked token.
    ///
    /// Because `peek` reports read errors, this assumes that the caller already handled those
    /// errors and is thus not going to call this when an error is present.
    pub fn consume_peeked(&mut self) -> TokenSpan {
        assert!(self.peeked.is_some());
        self.peeked.take().unwrap()
    }

    /// Peeks the upcoming token.
    ///
    /// It is OK to call this function several times on the same token before extracting it from
    /// the lexer.
    pub fn peek(&mut self) -> Result<&TokenSpan> {
        if self.peeked.is_none() {
            let span = self.read()?;
            self.peeked.replace(span);
        }
        Ok(self.peeked.as_ref().unwrap())
    }

    /// Reads the next token.
    ///
    /// If the next token is invalid and results in a read error, the stream will remain valid and
    /// further tokens can be obtained with subsequent calls.
    pub fn read(&mut self) -> Result<TokenSpan> {
        match self.peeked.take() {
            Some(t) => Ok(t),
            None => match self.lexer.read() {
                Ok(span) => Ok(span),
                Err(e) => Err((self.lexer.input.next_pos(), e)),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fmt;

    /// Syntactic sugar to instantiate a `TokenSpan` for testing.
    fn ts(token: Token, line: usize, col: usize, length: usize) -> TokenSpan {
        TokenSpan::new(token, LineCol { line, col }, length)
    }

    impl fmt::Debug for TokenSpan {
        /// Mimic the way we write the tests with the `ts` helper in `TokenSpan` dumps.
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                f,
                "ts(Token::{:?}, {}, {}, {})",
                self.token, self.pos.line, self.pos.col, self.length
            )
        }
    }

    /// Runs the lexer on the given `input` and expects the returned tokens to match
    /// `exp_token_spans`.
    fn do_ok_test(input: &str, exp_token_spans: &[TokenSpan]) {
        let mut input = input.as_bytes();
        let mut lexer = Lexer::from(&mut input);

        let mut token_spans: Vec<TokenSpan> = vec![];
        let mut eof = false;
        while !eof {
            let token_span = lexer.read().expect("Lexing failed");
            eof = token_span.token == Token::Eof;
            token_spans.push(token_span);
        }

        assert_eq!(exp_token_spans, token_spans.as_slice());
    }

    #[test]
    fn test_empty() {
        let mut input = b"".as_ref();
        let mut lexer = Lexer::from(&mut input);
        assert_eq!(Token::Eof, lexer.read().unwrap().token);
        assert_eq!(Token::Eof, lexer.read().unwrap().token);
    }

    #[test]
    fn test_read_past_eof() {
        do_ok_test("", &[ts(Token::Eof, 1, 1, 0)]);
    }

    #[test]
    fn test_whitespace_only() {
        do_ok_test("   \t  ", &[ts(Token::Eof, 1, 11, 0)]);
    }

    #[test]
    fn test_multiple_lines() {
        do_ok_test(
            "   \n \t   \n  ",
            &[ts(Token::Eol, 1, 4, 1), ts(Token::Eol, 2, 12, 1), ts(Token::Eof, 3, 3, 0)],
        );
        do_ok_test(
            "   : \t   :  ",
            &[ts(Token::Eol, 1, 4, 1), ts(Token::Eol, 1, 12, 1), ts(Token::Eof, 1, 15, 0)],
        );
    }

    #[test]
    fn test_tabs() {
        do_ok_test("\t33", &[ts(Token::Integer(33), 1, 9, 2), ts(Token::Eof, 1, 11, 0)]);
        do_ok_test(
            "1234567\t8",
            &[
                ts(Token::Integer(1234567), 1, 1, 7),
                ts(Token::Integer(8), 1, 9, 1),
                ts(Token::Eof, 1, 10, 0),
            ],
        );
    }

    /// Syntactic sugar to instantiate a `VarRef` without an explicit type annotation.
    fn new_auto_symbol(name: &str) -> Token {
        Token::Symbol(VarRef::new(name, None))
    }

    #[test]
    fn test_some_tokens() {
        do_ok_test(
            "123 45 \n 6 3.012 abc a38z: a=3 with_underscores_1=_2",
            &[
                ts(Token::Integer(123), 1, 1, 3),
                ts(Token::Integer(45), 1, 5, 2),
                ts(Token::Eol, 1, 8, 1),
                ts(Token::Integer(6), 2, 2, 1),
                ts(Token::Double(3.012), 2, 4, 5),
                ts(new_auto_symbol("abc"), 2, 10, 3),
                ts(new_auto_symbol("a38z"), 2, 14, 4),
                ts(Token::Eol, 2, 18, 1),
                ts(new_auto_symbol("a"), 2, 20, 1),
                ts(Token::Equal, 2, 21, 1),
                ts(Token::Integer(3), 2, 22, 1),
                ts(new_auto_symbol("with_underscores_1"), 2, 24, 18),
                ts(Token::Equal, 2, 42, 1),
                ts(new_auto_symbol("_2"), 2, 43, 2),
                ts(Token::Eof, 2, 45, 0),
            ],
        );
    }

    #[test]
    fn test_boolean_literals() {
        do_ok_test(
            "true TRUE yes YES y false FALSE no NO n",
            &[
                ts(Token::Boolean(true), 1, 1, 4),
                ts(Token::Boolean(true), 1, 6, 4),
                ts(new_auto_symbol("yes"), 1, 11, 3),
                ts(new_auto_symbol("YES"), 1, 15, 3),
                ts(new_auto_symbol("y"), 1, 19, 1),
                ts(Token::Boolean(false), 1, 21, 5),
                ts(Token::Boolean(false), 1, 27, 5),
                ts(new_auto_symbol("no"), 1, 33, 2),
                ts(new_auto_symbol("NO"), 1, 36, 2),
                ts(new_auto_symbol("n"), 1, 39, 1),
                ts(Token::Eof, 1, 40, 0),
            ],
        );
    }

    #[test]
    fn test_integer_literals() {
        do_ok_test(
            "&b10 &B_10 &D10 &d_10 &o_10 &O_10 &X10 &x_10 &xabcdef &x0ABCDEF0 &x7a1",
            &[
                ts(Token::Integer(2), 1, 1, 4),
                ts(Token::Integer(2), 1, 6, 5),
                ts(Token::Integer(10), 1, 12, 4),
                ts(Token::Integer(10), 1, 17, 5),
                ts(Token::Integer(8), 1, 23, 5),
                ts(Token::Integer(8), 1, 29, 5),
                ts(Token::Integer(16), 1, 35, 4),
                ts(Token::Integer(16), 1, 40, 5),
                ts(Token::Integer(11259375), 1, 46, 8),
                ts(Token::Integer(180150000), 1, 55, 10),
                ts(Token::Integer(1953), 1, 66, 5),
                ts(Token::Eof, 1, 71, 0),
            ],
        );

        do_ok_test(
            "&b11111111111111111111111111111111 &xf0000000 &xffffffff",
            &[
                ts(Token::Integer(-1), 1, 1, 34),
                ts(Token::Integer(-268435456), 1, 36, 10),
                ts(Token::Integer(-1), 1, 47, 10),
                ts(Token::Eof, 1, 57, 0),
            ],
        );

        do_ok_test(
            "& &_ &__ &i10 &i_10 &d &d10.1 &b2 &da &o8 &xg",
            &[
                ts(Token::Bad("Missing base in integer literal".to_owned()), 1, 1, 1),
                ts(Token::Bad("Unknown base _ in integer literal".to_owned()), 1, 3, 1),
                ts(Token::Bad("Unknown base _ in integer literal".to_owned()), 1, 6, 2),
                ts(Token::Bad("Unknown base i in integer literal".to_owned()), 1, 10, 3),
                ts(Token::Bad("Unknown base i in integer literal".to_owned()), 1, 15, 4),
                ts(Token::Bad("No digits in integer literal".to_owned()), 1, 21, 1),
                ts(Token::Bad("Numbers in base syntax must be integers".to_owned()), 1, 24, 2),
                ts(Token::Bad("Bad integer 2: invalid digit found in string".to_owned()), 1, 31, 1),
                ts(Token::Bad("Bad integer a: invalid digit found in string".to_owned()), 1, 35, 1),
                ts(Token::Bad("Bad integer 8: invalid digit found in string".to_owned()), 1, 39, 1),
                ts(Token::Bad("Unexpected character in numeric literal: g".to_owned()), 1, 43, 1),
                ts(Token::Eof, 1, 46, 0),
            ],
        );

        do_ok_test(
            ">&< >&_< >&__< >&i10< >&i_10< >&d< >&d10.1<",
            &[
                ts(Token::Greater, 1, 1, 1),
                ts(Token::Bad("Missing base in integer literal".to_owned()), 1, 2, 1),
                ts(Token::Less, 1, 3, 1),
                // -
                ts(Token::Greater, 1, 5, 1),
                ts(Token::Bad("Unknown base _ in integer literal".to_owned()), 1, 6, 1),
                ts(Token::Less, 1, 8, 1),
                // -
                ts(Token::Greater, 1, 10, 1),
                ts(Token::Bad("Unknown base _ in integer literal".to_owned()), 1, 11, 2),
                ts(Token::Less, 1, 14, 1),
                // -
                ts(Token::Greater, 1, 16, 1),
                ts(Token::Bad("Unknown base i in integer literal".to_owned()), 1, 17, 3),
                ts(Token::Less, 1, 21, 1),
                // -
                ts(Token::Greater, 1, 23, 1),
                ts(Token::Bad("Unknown base i in integer literal".to_owned()), 1, 24, 4),
                ts(Token::Less, 1, 29, 1),
                // -
                ts(Token::Greater, 1, 31, 1),
                ts(Token::Bad("No digits in integer literal".to_owned()), 1, 32, 1),
                ts(Token::Less, 1, 34, 1),
                // -
                ts(Token::Greater, 1, 36, 1),
                ts(Token::Bad("Numbers in base syntax must be integers".to_owned()), 1, 37, 2),
                ts(Token::Less, 1, 43, 1),
                // -
                ts(Token::Eof, 1, 44, 0),
            ],
        );
    }

    #[test]
    fn test_utf8() {
        do_ok_test(
            "가 나=7 a다b \"라 마\"",
            &[
                ts(new_auto_symbol("가"), 1, 1, 3),
                ts(new_auto_symbol("나"), 1, 3, 3),
                ts(Token::Equal, 1, 4, 1),
                ts(Token::Integer(7), 1, 5, 1),
                ts(new_auto_symbol("a다b"), 1, 7, 5),
                ts(Token::Text("라 마".to_owned()), 1, 11, 9),
                ts(Token::Eof, 1, 16, 0),
            ],
        );
    }

    #[test]
    fn test_remarks() {
        do_ok_test(
            "REM This is a comment\nNOT 'This is another comment\n",
            &[
                ts(Token::Eol, 1, 22, 1),
                ts(Token::Not, 2, 1, 3),
                ts(Token::Eol, 2, 29, 1),
                ts(Token::Eof, 3, 1, 0),
            ],
        );

        do_ok_test(
            "REM This is a comment: and the colon doesn't yield Eol\nNOT 'Another: comment\n",
            &[
                ts(Token::Eol, 1, 55, 1),
                ts(Token::Not, 2, 1, 3),
                ts(Token::Eol, 2, 22, 1),
                ts(Token::Eof, 3, 1, 0),
            ],
        );
    }

    #[test]
    fn test_var_types() {
        do_ok_test(
            "a b? d# i% s$",
            &[
                ts(new_auto_symbol("a"), 1, 1, 1),
                ts(Token::Symbol(VarRef::new("b", Some(ExprType::Boolean))), 1, 3, 2),
                ts(Token::Symbol(VarRef::new("d", Some(ExprType::Double))), 1, 6, 2),
                ts(Token::Symbol(VarRef::new("i", Some(ExprType::Integer))), 1, 9, 2),
                ts(Token::Symbol(VarRef::new("s", Some(ExprType::Text))), 1, 12, 2),
                ts(Token::Eof, 1, 14, 0),
            ],
        );
    }

    #[test]
    fn test_strings() {
        do_ok_test(
            " \"this is a string\"  3",
            &[
                ts(Token::Text("this is a string".to_owned()), 1, 2, 18),
                ts(Token::Integer(3), 1, 22, 1),
                ts(Token::Eof, 1, 23, 0),
            ],
        );

        do_ok_test(
            " \"this is a string with ; special : characters in it\"",
            &[
                ts(
                    Token::Text("this is a string with ; special : characters in it".to_owned()),
                    1,
                    2,
                    52,
                ),
                ts(Token::Eof, 1, 54, 0),
            ],
        );

        do_ok_test(
            "\"this \\\"is escaped\\\" \\\\ \\a\" 1",
            &[
                ts(Token::Text("this \"is escaped\" \\ a".to_owned()), 1, 1, 23),
                ts(Token::Integer(1), 1, 29, 1),
                ts(Token::Eof, 1, 30, 0),
            ],
        );
    }

    #[test]
    fn test_data() {
        do_ok_test("DATA", &[ts(Token::Data, 1, 1, 4), ts(Token::Eof, 1, 5, 0)]);

        do_ok_test("data", &[ts(Token::Data, 1, 1, 4), ts(Token::Eof, 1, 5, 0)]);

        // Common BASIC interprets things like "2 + foo" as a single string but we interpret
        // separate tokens.  "Fixing" this to read data in the same way requires entering a
        // separate lexing mode just for DATA statements, which is not very interesting.  We can
        // ask for strings to always be double-quoted.
        do_ok_test(
            "DATA 2 + foo",
            &[
                ts(Token::Data, 1, 1, 4),
                ts(Token::Integer(2), 1, 6, 1),
                ts(Token::Plus, 1, 8, 1),
                ts(new_auto_symbol("foo"), 1, 10, 3),
                ts(Token::Eof, 1, 13, 0),
            ],
        );
    }

    #[test]
    fn test_dim() {
        do_ok_test(
            "DIM SHARED AS",
            &[
                ts(Token::Dim, 1, 1, 3),
                ts(Token::Shared, 1, 5, 6),
                ts(Token::As, 1, 12, 2),
                ts(Token::Eof, 1, 14, 0),
            ],
        );
        do_ok_test(
            "BOOLEAN DOUBLE INTEGER STRING",
            &[
                ts(Token::BooleanName, 1, 1, 7),
                ts(Token::DoubleName, 1, 9, 6),
                ts(Token::IntegerName, 1, 16, 7),
                ts(Token::TextName, 1, 24, 6),
                ts(Token::Eof, 1, 30, 0),
            ],
        );

        do_ok_test(
            "dim shared as",
            &[
                ts(Token::Dim, 1, 1, 3),
                ts(Token::Shared, 1, 5, 6),
                ts(Token::As, 1, 12, 2),
                ts(Token::Eof, 1, 14, 0),
            ],
        );
        do_ok_test(
            "boolean double integer string",
            &[
                ts(Token::BooleanName, 1, 1, 7),
                ts(Token::DoubleName, 1, 9, 6),
                ts(Token::IntegerName, 1, 16, 7),
                ts(Token::TextName, 1, 24, 6),
                ts(Token::Eof, 1, 30, 0),
            ],
        );
    }

    #[test]
    fn test_do() {
        do_ok_test(
            "DO UNTIL WHILE EXIT LOOP",
            &[
                ts(Token::Do, 1, 1, 2),
                ts(Token::Until, 1, 4, 5),
                ts(Token::While, 1, 10, 5),
                ts(Token::Exit, 1, 16, 4),
                ts(Token::Loop, 1, 21, 4),
                ts(Token::Eof, 1, 25, 0),
            ],
        );

        do_ok_test(
            "do until while exit loop",
            &[
                ts(Token::Do, 1, 1, 2),
                ts(Token::Until, 1, 4, 5),
                ts(Token::While, 1, 10, 5),
                ts(Token::Exit, 1, 16, 4),
                ts(Token::Loop, 1, 21, 4),
                ts(Token::Eof, 1, 25, 0),
            ],
        );
    }

    #[test]
    fn test_if() {
        do_ok_test(
            "IF THEN ELSEIF ELSE END IF",
            &[
                ts(Token::If, 1, 1, 2),
                ts(Token::Then, 1, 4, 4),
                ts(Token::Elseif, 1, 9, 6),
                ts(Token::Else, 1, 16, 4),
                ts(Token::End, 1, 21, 3),
                ts(Token::If, 1, 25, 2),
                ts(Token::Eof, 1, 27, 0),
            ],
        );

        do_ok_test(
            "if then elseif else end if",
            &[
                ts(Token::If, 1, 1, 2),
                ts(Token::Then, 1, 4, 4),
                ts(Token::Elseif, 1, 9, 6),
                ts(Token::Else, 1, 16, 4),
                ts(Token::End, 1, 21, 3),
                ts(Token::If, 1, 25, 2),
                ts(Token::Eof, 1, 27, 0),
            ],
        );
    }

    #[test]
    fn test_for() {
        do_ok_test(
            "FOR TO STEP NEXT",
            &[
                ts(Token::For, 1, 1, 3),
                ts(Token::To, 1, 5, 2),
                ts(Token::Step, 1, 8, 4),
                ts(Token::Next, 1, 13, 4),
                ts(Token::Eof, 1, 17, 0),
            ],
        );

        do_ok_test(
            "for to step next",
            &[
                ts(Token::For, 1, 1, 3),
                ts(Token::To, 1, 5, 2),
                ts(Token::Step, 1, 8, 4),
                ts(Token::Next, 1, 13, 4),
                ts(Token::Eof, 1, 17, 0),
            ],
        );
    }

    #[test]
    fn test_function() {
        do_ok_test(
            "FUNCTION FOO END FUNCTION",
            &[
                ts(Token::Function, 1, 1, 8),
                ts(Token::Symbol(VarRef::new("FOO", None)), 1, 10, 3),
                ts(Token::End, 1, 14, 3),
                ts(Token::Function, 1, 18, 8),
                ts(Token::Eof, 1, 26, 0),
            ],
        );

        do_ok_test(
            "function foo end function",
            &[
                ts(Token::Function, 1, 1, 8),
                ts(Token::Symbol(VarRef::new("foo", None)), 1, 10, 3),
                ts(Token::End, 1, 14, 3),
                ts(Token::Function, 1, 18, 8),
                ts(Token::Eof, 1, 26, 0),
            ],
        );
    }

    #[test]
    fn test_gosub() {
        do_ok_test("GOSUB", &[ts(Token::Gosub, 1, 1, 5), ts(Token::Eof, 1, 6, 0)]);

        do_ok_test("gosub", &[ts(Token::Gosub, 1, 1, 5), ts(Token::Eof, 1, 6, 0)]);
    }

    #[test]
    fn test_goto() {
        do_ok_test("GOTO", &[ts(Token::Goto, 1, 1, 4), ts(Token::Eof, 1, 5, 0)]);

        do_ok_test("goto", &[ts(Token::Goto, 1, 1, 4), ts(Token::Eof, 1, 5, 0)]);
    }

    #[test]
    fn test_label() {
        do_ok_test(
            "@Foo123 @a @Z @_ok",
            &[
                ts(Token::Label("Foo123".to_owned()), 1, 1, 7),
                ts(Token::Label("a".to_owned()), 1, 9, 2),
                ts(Token::Label("Z".to_owned()), 1, 12, 2),
                ts(Token::Label("_ok".to_owned()), 1, 15, 4),
                ts(Token::Eof, 1, 19, 0),
            ],
        );
    }

    #[test]
    fn test_on_error() {
        for s in ["ON ERROR GOTO @foo", "on error goto @foo"] {
            do_ok_test(
                s,
                &[
                    ts(Token::On, 1, 1, 2),
                    ts(Token::Error, 1, 4, 5),
                    ts(Token::Goto, 1, 10, 4),
                    ts(Token::Label("foo".to_owned()), 1, 15, 4),
                    ts(Token::Eof, 1, 19, 0),
                ],
            );
        }

        for s in ["ON ERROR RESUME NEXT", "on error resume next"] {
            do_ok_test(
                s,
                &[
                    ts(Token::On, 1, 1, 2),
                    ts(Token::Error, 1, 4, 5),
                    ts(Token::Resume, 1, 10, 6),
                    ts(Token::Next, 1, 17, 4),
                    ts(Token::Eof, 1, 21, 0),
                ],
            );
        }
    }

    #[test]
    fn test_return() {
        do_ok_test("RETURN", &[ts(Token::Return, 1, 1, 6), ts(Token::Eof, 1, 7, 0)]);

        do_ok_test("return", &[ts(Token::Return, 1, 1, 6), ts(Token::Eof, 1, 7, 0)]);
    }

    #[test]
    fn test_select() {
        do_ok_test(
            "SELECT CASE IS ELSE END",
            &[
                ts(Token::Select, 1, 1, 6),
                ts(Token::Case, 1, 8, 4),
                ts(Token::Is, 1, 13, 2),
                ts(Token::Else, 1, 16, 4),
                ts(Token::End, 1, 21, 3),
                ts(Token::Eof, 1, 24, 0),
            ],
        );

        do_ok_test(
            "select case is else end",
            &[
                ts(Token::Select, 1, 1, 6),
                ts(Token::Case, 1, 8, 4),
                ts(Token::Is, 1, 13, 2),
                ts(Token::Else, 1, 16, 4),
                ts(Token::End, 1, 21, 3),
                ts(Token::Eof, 1, 24, 0),
            ],
        );
    }

    #[test]
    fn test_sub() {
        do_ok_test(
            "SUB FOO END SUB",
            &[
                ts(Token::Sub, 1, 1, 3),
                ts(Token::Symbol(VarRef::new("FOO", None)), 1, 5, 3),
                ts(Token::End, 1, 9, 3),
                ts(Token::Sub, 1, 13, 3),
                ts(Token::Eof, 1, 16, 0),
            ],
        );

        do_ok_test(
            "sub foo end sub",
            &[
                ts(Token::Sub, 1, 1, 3),
                ts(Token::Symbol(VarRef::new("foo", None)), 1, 5, 3),
                ts(Token::End, 1, 9, 3),
                ts(Token::Sub, 1, 13, 3),
                ts(Token::Eof, 1, 16, 0),
            ],
        );
    }

    #[test]
    fn test_while() {
        do_ok_test(
            "WHILE WEND",
            &[ts(Token::While, 1, 1, 5), ts(Token::Wend, 1, 7, 4), ts(Token::Eof, 1, 11, 0)],
        );

        do_ok_test(
            "while wend",
            &[ts(Token::While, 1, 1, 5), ts(Token::Wend, 1, 7, 4), ts(Token::Eof, 1, 11, 0)],
        );
    }

    /// Syntactic sugar to instantiate a test that verifies the parsing of a binary operator.
    fn do_binary_operator_test(op: &str, t: Token) {
        do_ok_test(
            format!("a {} 2", op).as_ref(),
            &[
                ts(new_auto_symbol("a"), 1, 1, 1),
                ts(t, 1, 3, op.len()),
                ts(Token::Integer(2), 1, 4 + op.len(), 1),
                ts(Token::Eof, 1, 5 + op.len(), 0),
            ],
        );
    }

    /// Syntactic sugar to instantiate a test that verifies the parsing of a unary operator.
    fn do_unary_operator_test(op: &str, t: Token) {
        do_ok_test(
            format!("{} 2", op).as_ref(),
            &[
                ts(t, 1, 1, op.len()),
                ts(Token::Integer(2), 1, 2 + op.len(), 1),
                ts(Token::Eof, 1, 3 + op.len(), 0),
            ],
        );
    }

    #[test]
    fn test_operator_relational_ops() {
        do_binary_operator_test("=", Token::Equal);
        do_binary_operator_test("<>", Token::NotEqual);
        do_binary_operator_test("<", Token::Less);
        do_binary_operator_test("<=", Token::LessEqual);
        do_binary_operator_test(">", Token::Greater);
        do_binary_operator_test(">=", Token::GreaterEqual);
    }

    #[test]
    fn test_operator_arithmetic_ops() {
        do_binary_operator_test("+", Token::Plus);
        do_binary_operator_test("-", Token::Minus);
        do_binary_operator_test("*", Token::Multiply);
        do_binary_operator_test("/", Token::Divide);
        do_binary_operator_test("MOD", Token::Modulo);
        do_binary_operator_test("mod", Token::Modulo);
        do_binary_operator_test("^", Token::Exponent);
        do_unary_operator_test("-", Token::Minus);
    }

    #[test]
    fn test_operator_logical_bitwise_ops() {
        do_binary_operator_test("AND", Token::And);
        do_binary_operator_test("OR", Token::Or);
        do_binary_operator_test("XOR", Token::Xor);
        do_unary_operator_test("NOT", Token::Not);

        do_binary_operator_test("<<", Token::ShiftLeft);
        do_binary_operator_test(">>", Token::ShiftRight);
    }

    #[test]
    fn test_operator_no_spaces() {
        do_ok_test(
            "z=2 654<>a32 3.1<0.1 8^7",
            &[
                ts(new_auto_symbol("z"), 1, 1, 1),
                ts(Token::Equal, 1, 2, 1),
                ts(Token::Integer(2), 1, 3, 1),
                ts(Token::Integer(654), 1, 5, 3),
                ts(Token::NotEqual, 1, 8, 2),
                ts(new_auto_symbol("a32"), 1, 10, 3),
                ts(Token::Double(3.1), 1, 14, 3),
                ts(Token::Less, 1, 17, 1),
                ts(Token::Double(0.1), 1, 18, 3),
                ts(Token::Integer(8), 1, 22, 1),
                ts(Token::Exponent, 1, 23, 1),
                ts(Token::Integer(7), 1, 24, 1),
                ts(Token::Eof, 1, 25, 0),
            ],
        );
    }

    #[test]
    fn test_parenthesis() {
        do_ok_test(
            "(a) (\"foo\") (3)",
            &[
                ts(Token::LeftParen, 1, 1, 1),
                ts(new_auto_symbol("a"), 1, 2, 1),
                ts(Token::RightParen, 1, 3, 1),
                ts(Token::LeftParen, 1, 5, 1),
                ts(Token::Text("foo".to_owned()), 1, 6, 5),
                ts(Token::RightParen, 1, 11, 1),
                ts(Token::LeftParen, 1, 13, 1),
                ts(Token::Integer(3), 1, 14, 1),
                ts(Token::RightParen, 1, 15, 1),
                ts(Token::Eof, 1, 16, 0),
            ],
        );
    }

    #[test]
    fn test_peekable_lexer() {
        let mut input = b"a b 123".as_ref();
        let mut lexer = Lexer::from(&mut input).peekable();
        assert_eq!(new_auto_symbol("a"), lexer.peek().unwrap().token);
        assert_eq!(new_auto_symbol("a"), lexer.peek().unwrap().token);
        assert_eq!(new_auto_symbol("a"), lexer.read().unwrap().token);
        assert_eq!(new_auto_symbol("b"), lexer.read().unwrap().token);
        assert_eq!(Token::Integer(123), lexer.peek().unwrap().token);
        assert_eq!(Token::Integer(123), lexer.read().unwrap().token);
        assert_eq!(Token::Eof, lexer.peek().unwrap().token);
        assert_eq!(Token::Eof, lexer.read().unwrap().token);
    }

    #[test]
    fn test_recoverable_errors() {
        do_ok_test(
            "0.1.28+5",
            &[
                ts(Token::Bad("Too many dots in numeric literal".to_owned()), 1, 1, 3),
                ts(Token::Plus, 1, 7, 1),
                ts(Token::Integer(5), 1, 8, 1),
                ts(Token::Eof, 1, 9, 0),
            ],
        );

        do_ok_test(
            "1 .3",
            &[
                ts(Token::Integer(1), 1, 1, 1),
                ts(Token::Bad("Unknown character: .".to_owned()), 1, 3, 2),
                ts(Token::Eof, 1, 5, 0),
            ],
        );

        do_ok_test(
            "1 3. 2",
            &[
                ts(Token::Integer(1), 1, 1, 1),
                ts(Token::Bad("Unknown character: .".to_owned()), 1, 3, 1),
                ts(Token::Integer(2), 1, 6, 1),
                ts(Token::Eof, 1, 7, 0),
            ],
        );

        do_ok_test(
            "9999999999+5",
            &[
                ts(
                    Token::Bad(
                        "Bad integer 9999999999: number too large to fit in target type".to_owned(),
                    ),
                    1,
                    1,
                    1,
                ),
                ts(Token::Plus, 1, 11, 1),
                ts(Token::Integer(5), 1, 12, 1),
                ts(Token::Eof, 1, 13, 0),
            ],
        );

        do_ok_test(
            "\n3!2 1",
            &[
                ts(Token::Eol, 1, 1, 1),
                ts(Token::Bad("Unexpected character in numeric literal: !".to_owned()), 2, 1, 2),
                ts(Token::Integer(1), 2, 5, 1),
                ts(Token::Eof, 2, 6, 0),
            ],
        );

        do_ok_test(
            "a b|d 5",
            &[
                ts(new_auto_symbol("a"), 1, 1, 1),
                ts(Token::Bad("Unexpected character in symbol: |".to_owned()), 1, 3, 2),
                ts(Token::Integer(5), 1, 7, 1),
                ts(Token::Eof, 1, 8, 0),
            ],
        );

        do_ok_test(
            "( \"this is incomplete",
            &[
                ts(Token::LeftParen, 1, 1, 1),
                ts(
                    Token::Bad("Incomplete string due to EOF: this is incomplete".to_owned()),
                    1,
                    3,
                    1,
                ),
                ts(Token::Eof, 1, 22, 0),
            ],
        );

        do_ok_test(
            "+ - ! * / MOD ^",
            &[
                ts(Token::Plus, 1, 1, 1),
                ts(Token::Minus, 1, 3, 1),
                ts(Token::Bad("Unknown character: !".to_owned()), 1, 5, 1),
                ts(Token::Multiply, 1, 7, 1),
                ts(Token::Divide, 1, 9, 1),
                ts(Token::Modulo, 1, 11, 3),
                ts(Token::Exponent, 1, 15, 1),
                ts(Token::Eof, 1, 16, 0),
            ],
        );

        do_ok_test(
            "@+",
            &[
                ts(Token::Bad("Empty label name".to_owned()), 1, 1, 1),
                ts(Token::Plus, 1, 2, 1),
                ts(Token::Eof, 1, 3, 0),
            ],
        );

        do_ok_test(
            "@123",
            &[
                ts(Token::Bad("Empty label name".to_owned()), 1, 1, 1),
                ts(Token::Integer(123), 1, 2, 3),
                ts(Token::Eof, 1, 5, 0),
            ],
        );
    }

    /// A reader that generates an error on the second read.
    ///
    /// Assumes that the buffered data in `good` is read in one go.
    struct FaultyReader {
        good: Option<Vec<u8>>,
    }

    impl FaultyReader {
        /// Creates a new faulty read with the given input data.
        ///
        /// `good` must be newline-terminated to prevent the caller from reading too much in one go.
        fn new(good: &str) -> Self {
            assert!(good.ends_with('\n'));
            Self { good: Some(good.as_bytes().to_owned()) }
        }
    }

    impl io::Read for FaultyReader {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            // This assumes that the good data fits within one read operation of the lexer.
            if let Some(good) = self.good.take() {
                assert!(buf.len() > good.len());
                buf[0..good.len()].clone_from_slice(&good[..]);
                Ok(good.len())
            } else {
                Err(io::Error::from(io::ErrorKind::InvalidData))
            }
        }
    }

    #[test]
    fn test_unrecoverable_io_error() {
        let mut reader = FaultyReader::new("3 + 5\n");
        let mut lexer = Lexer::from(&mut reader);

        assert_eq!(Token::Integer(3), lexer.read().unwrap().token);
        assert_eq!(Token::Plus, lexer.read().unwrap().token);
        assert_eq!(Token::Integer(5), lexer.read().unwrap().token);
        assert_eq!(Token::Eol, lexer.read().unwrap().token);
        let e = lexer.read().unwrap_err();
        assert_eq!(io::ErrorKind::InvalidData, e.kind());
        let e = lexer.read().unwrap_err();
        assert_eq!(io::ErrorKind::Other, e.kind());
    }
}
