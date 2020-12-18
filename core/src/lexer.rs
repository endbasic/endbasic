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

use crate::ast::{VarRef, VarType};
use crate::reader::CharReader;
use std::io;
use std::iter::Peekable;

/// Collection of valid tokens.
///
/// Of special interest are the `Eof` and `Bad` tokens, both of which denote exceptional
/// conditions and require special care.  `Eof` indicates that there are no more tokens.
/// `Bad` indicates that a token was bad and contains the reason behind the problem, but the
/// stream remains valid for extraction of further tokens.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Token {
    Eof,
    Eol,
    Bad(String),

    Boolean(bool),
    Integer(i32),
    Text(String),
    Symbol(VarRef),

    Comma,
    Semicolon,
    LeftParen,
    RightParen,

    Plus,
    Minus,
    Multiply,
    Divide,
    Modulo,

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

    Else,
    Elseif,
    End,
    For,
    If,
    Next,
    Step,
    Then,
    To,
    While,
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
            '\n' | ':' | '(' | ')' | '\'' | '=' | '<' | '>' | ';' | ',' | '+' | '-' | '*' | '/' => {
                true
            }
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

/// Iterator over the tokens of the language.
pub struct Lexer<'a> {
    /// Peekable iterator over the characters to scan.
    input: Peekable<CharReader<'a>>,
}

impl<'a> Lexer<'a> {
    /// Creates a new lexer from the given readable.
    pub fn from(input: &'a mut dyn io::Read) -> Self {
        Self { input: CharReader::from(input).peekable() }
    }

    /// Handles a `input.read()` call that returned an unexpected character.
    ///
    /// This returns a `Token::Bad` with the provided `msg` and skips characters in the input
    /// stream until a field separator is found.
    fn handle_bad_read<S: Into<String>>(&mut self, msg: S) -> io::Result<Token> {
        loop {
            match self.input.peek() {
                Some(Ok(ch)) if ch.is_separator() => break,
                Some(Ok(_)) => {
                    self.input.next().unwrap()?;
                }
                Some(Err(_)) => return Err(self.input.next().unwrap().unwrap_err()),
                None => break,
            }
        }
        Ok(Token::Bad(msg.into()))
    }

    /// Handles a `input.peek()` call that returned an unexpected character.
    ///
    /// This returns a `Token::Bad` with the provided `msg`, consumes the peeked character, and
    /// then skips characters in the input stream until a field separator is found.
    fn handle_bad_peek<S: Into<String>>(&mut self, msg: S) -> io::Result<Token> {
        self.input.next();
        self.handle_bad_read(msg)
    }

    /// Consumes the integer at the current position, whose first digit is `first`.
    fn consume_integer(&mut self, first: char) -> io::Result<Token> {
        let mut s = String::new();
        s.push(first);
        loop {
            match self.input.peek() {
                Some(Ok(ch)) if ch.is_digit(10) => s.push(self.input.next().unwrap()?),
                Some(Ok(ch)) if ch.is_separator() => break,
                Some(Ok(ch)) => {
                    let msg = format!("Unexpected character in integer: {}", ch);
                    return self.handle_bad_peek(msg);
                }
                Some(Err(_)) => return Err(self.input.next().unwrap().unwrap_err()),
                None => break,
            }
        }
        match s.parse::<i32>() {
            Ok(i) => Ok(Token::Integer(i)),
            Err(e) => self.handle_bad_read(format!("Bad integer {}: {}", s, e)),
        }
    }

    /// Consumes the operator at the current position, whose first character is `first`.
    fn consume_operator(&mut self, first: char) -> io::Result<Token> {
        match (first, self.input.peek()) {
            (_, Some(Err(_))) => Err(self.input.next().unwrap().unwrap_err()),

            ('<', Some(Ok('>'))) => {
                self.input.next().unwrap()?;
                Ok(Token::NotEqual)
            }

            ('<', Some(Ok('='))) => {
                self.input.next().unwrap()?;
                Ok(Token::LessEqual)
            }
            ('<', _) => Ok(Token::Less),

            ('>', Some(Ok('='))) => {
                self.input.next().unwrap()?;
                Ok(Token::GreaterEqual)
            }
            ('>', _) => Ok(Token::Greater),

            (_, _) => panic!("Should not have been called"),
        }
    }

    /// Consumes the symbol or keyword at the current position, whose first letter is `first`.
    ///
    /// The symbol may be a bare name, but it may also contain an optional type annotation.
    fn consume_symbol(&mut self, first: char) -> io::Result<Token> {
        let mut s = String::new();
        s.push(first);
        let mut vtype = VarType::Auto;
        loop {
            match self.input.peek() {
                Some(Ok(ch)) if ch.is_word() => s.push(self.input.next().unwrap()?),
                Some(Ok(ch)) if ch.is_separator() => break,
                Some(Ok('?')) => {
                    vtype = VarType::Boolean;
                    self.input.next().unwrap()?;
                    break;
                }
                Some(Ok('%')) => {
                    vtype = VarType::Integer;
                    self.input.next().unwrap()?;
                    break;
                }
                Some(Ok('$')) => {
                    vtype = VarType::Text;
                    self.input.next().unwrap()?;
                    break;
                }
                Some(Ok(ch)) => {
                    let msg = format!("Unexpected character in symbol: {}", ch);
                    return self.handle_bad_peek(msg);
                }
                Some(Err(_)) => return Err(self.input.next().unwrap().unwrap_err()),
                None => break,
            }
        }
        match s.to_uppercase().as_str() {
            "AND" => Ok(Token::And),
            "ELSE" => Ok(Token::Else),
            "ELSEIF" => Ok(Token::Elseif),
            "END" => Ok(Token::End),
            "FALSE" => Ok(Token::Boolean(false)),
            "FOR" => Ok(Token::For),
            "IF" => Ok(Token::If),
            "MOD" => Ok(Token::Modulo),
            "NEXT" => Ok(Token::Next),
            "NOT" => Ok(Token::Not),
            "OR" => Ok(Token::Or),
            "REM" => self.consume_rest_of_line(),
            "STEP" => Ok(Token::Step),
            "THEN" => Ok(Token::Then),
            "TO" => Ok(Token::To),
            "TRUE" => Ok(Token::Boolean(true)),
            "WHILE" => Ok(Token::While),
            "XOR" => Ok(Token::Xor),
            _ => Ok(Token::Symbol(VarRef::new(s, vtype))),
        }
    }

    /// Consumes the string at the current position, which was has to end with `delim`.
    ///
    /// This handles quoted characters within the string.
    fn consume_text(&mut self, delim: char) -> io::Result<Token> {
        let mut s = String::new();
        let mut escaping = false;
        loop {
            match self.input.peek() {
                Some(Ok(ch)) => {
                    if escaping {
                        s.push(self.input.next().unwrap()?);
                        escaping = false;
                    } else if *ch == '\\' {
                        self.input.next().unwrap()?;
                        escaping = true;
                    } else if *ch == delim {
                        self.input.next().unwrap()?;
                        break;
                    } else {
                        s.push(self.input.next().unwrap()?);
                    }
                }
                Some(Err(_)) => return Err(self.input.next().unwrap().unwrap_err()),
                None => {
                    return self.handle_bad_peek(format!("Incomplete string due to EOF: {}", s))
                }
            }
        }
        Ok(Token::Text(s))
    }

    /// Consumes the remainder of the line and returns the token that was encountered at the end
    /// (which may be EOF or end of line).
    fn consume_rest_of_line(&mut self) -> io::Result<Token> {
        loop {
            match self.input.next() {
                None => return Ok(Token::Eof),
                Some(Ok('\n')) => return Ok(Token::Eol),
                Some(Err(e)) => return Err(e),
                Some(Ok(_)) => (),
            }
        }
    }

    /// Skips whitespace until it finds the beginning of the next token, and returns its first
    /// character.
    fn advance_and_read_next(&mut self) -> io::Result<Option<char>> {
        loop {
            match self.input.next() {
                Some(Ok(ch)) if ch.is_space() => (),
                Some(Ok(ch)) => return Ok(Some(ch)),
                Some(Err(e)) => return Err(e),
                None => return Ok(None),
            }
        }
    }

    /// Reads the next token from the input stream.
    ///
    /// Note that this returns errors only on fatal I/O conditions.  EOF and malformed tokens are
    /// both returned as the special token types `Token::Eof` and `Token::Bad` respectively.
    pub fn read(&mut self) -> io::Result<Token> {
        let ch = self.advance_and_read_next()?;
        if ch.is_none() {
            return Ok(Token::Eof);
        }
        let ch = ch.unwrap();
        match ch {
            '\n' | ':' => Ok(Token::Eol),
            '\'' => self.consume_rest_of_line(),

            '"' => self.consume_text('"'),

            ';' => Ok(Token::Semicolon),
            ',' => Ok(Token::Comma),

            '(' => Ok(Token::LeftParen),
            ')' => Ok(Token::RightParen),

            '+' => Ok(Token::Plus),
            '-' => Ok(Token::Minus),
            '*' => Ok(Token::Multiply),
            '/' => Ok(Token::Divide),

            '=' => Ok(Token::Equal),
            '<' | '>' => self.consume_operator(ch),

            ch if ch.is_digit(10) => self.consume_integer(ch),
            ch if ch.is_word() => self.consume_symbol(ch),
            ch => self.handle_bad_read(format!("Unknown character: {}", ch)),
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
    peeked: Option<Token>,
}

impl<'a> PeekableLexer<'a> {
    /// Reads the previously-peeked token.
    ///
    /// Because `peek` reports read errors, this assumes that the caller already handled those
    /// errors and is thus not going to call this when an error is present.
    pub fn consume_peeked(&mut self) -> Token {
        assert!(self.peeked.is_some());
        self.peeked.take().unwrap()
    }

    /// Peeks the upcoming token.
    ///
    /// It is OK to call this function several times on the same token before extracting it from
    /// the lexer.
    pub fn peek(&mut self) -> io::Result<&Token> {
        if self.peeked.is_none() {
            let n = self.read()?;
            self.peeked.replace(n);
        }
        Ok(self.peeked.as_ref().unwrap())
    }

    /// Reads the next token.
    ///
    /// If the next token is invalid and results in a read error, the stream will remain valid and
    /// further tokens can be obtained with subsequent calls.
    pub fn read(&mut self) -> io::Result<Token> {
        match self.peeked.take() {
            Some(t) => Ok(t),
            None => self.lexer.read(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Runs the lexer on the given `input` and expects the returned tokens to match `exp_tokens`.
    ///
    /// `Token::Eof` should not be provided in `exp_tokens` as this explicitly waits for that.
    fn do_ok_test(input: &str, exp_tokens: &[Token]) {
        let mut input = input.as_bytes();
        let mut lexer = Lexer::from(&mut input);

        let mut tokens = vec![];
        loop {
            let token = lexer.read().expect("Lexing failed");
            if token == Token::Eof {
                break;
            }
            tokens.push(token);
        }

        assert_eq!(exp_tokens, tokens.as_slice());
    }

    #[test]
    fn test_empty() {
        let mut input = b"".as_ref();
        let mut lexer = Lexer::from(&mut input);
        assert_eq!(Token::Eof, lexer.read().unwrap());
        assert_eq!(Token::Eof, lexer.read().unwrap());
    }

    #[test]
    fn test_read_past_eof() {
        do_ok_test("", &[]);
    }

    #[test]
    fn test_whitespace_only() {
        do_ok_test("   \t  ", &[]);
    }

    #[test]
    fn test_multiple_lines() {
        do_ok_test("   \n \t   \n  ", &[Token::Eol, Token::Eol]);
        do_ok_test("   : \t   :  ", &[Token::Eol, Token::Eol]);
    }

    /// Syntactic sugar to instantiate a `VarRef` without an explicity type annotation.
    fn new_auto_symbol(name: &str) -> Token {
        Token::Symbol(VarRef::new(name, VarType::Auto))
    }

    #[test]
    fn test_some_tokens() {
        do_ok_test(
            "123 45 \n 6 abc a38z: a=3 with_underscores_1=_2",
            &[
                Token::Integer(123),
                Token::Integer(45),
                Token::Eol,
                Token::Integer(6),
                new_auto_symbol("abc"),
                new_auto_symbol("a38z"),
                Token::Eol,
                new_auto_symbol("a"),
                Token::Equal,
                Token::Integer(3),
                new_auto_symbol("with_underscores_1"),
                Token::Equal,
                new_auto_symbol("_2"),
            ],
        );
    }

    #[test]
    fn test_boolean_literals() {
        do_ok_test(
            "true TRUE yes YES y false FALSE no NO n",
            &[
                Token::Boolean(true),
                Token::Boolean(true),
                new_auto_symbol("yes"),
                new_auto_symbol("YES"),
                new_auto_symbol("y"),
                Token::Boolean(false),
                Token::Boolean(false),
                new_auto_symbol("no"),
                new_auto_symbol("NO"),
                new_auto_symbol("n"),
            ],
        );
    }

    #[test]
    fn test_utf8() {
        do_ok_test(
            "가 나=7 a다b \"라 마\"",
            &[
                new_auto_symbol("가"),
                new_auto_symbol("나"),
                Token::Equal,
                Token::Integer(7),
                new_auto_symbol("a다b"),
                Token::Text("라 마".to_owned()),
            ],
        );
    }

    #[test]
    fn test_remarks() {
        do_ok_test(
            "REM This is a comment\nNOT 'This is another comment\n",
            &[Token::Eol, Token::Not, Token::Eol],
        );

        do_ok_test(
            "REM This is a comment: and the colon doesn't yield Eol\nNOT 'Another: comment\n",
            &[Token::Eol, Token::Not, Token::Eol],
        );
    }

    #[test]
    fn test_var_types() {
        do_ok_test(
            "a b? i% s$",
            &[
                new_auto_symbol("a"),
                Token::Symbol(VarRef::new("b", VarType::Boolean)),
                Token::Symbol(VarRef::new("i", VarType::Integer)),
                Token::Symbol(VarRef::new("s", VarType::Text)),
            ],
        );
    }

    #[test]
    fn test_strings() {
        do_ok_test(
            " \"this is a string\"  3",
            &[Token::Text("this is a string".to_owned()), Token::Integer(3)],
        );

        do_ok_test(
            " \"this is a string with ; special : characters in it\"",
            &[Token::Text("this is a string with ; special : characters in it".to_owned())],
        );

        do_ok_test(
            "\"this \\\"is escaped\\\" \\\\ \\a\" 1",
            &[Token::Text("this \"is escaped\" \\ a".to_owned()), Token::Integer(1)],
        );
    }

    #[test]
    fn test_if() {
        do_ok_test(
            "IF THEN ELSEIF ELSE END IF",
            &[Token::If, Token::Then, Token::Elseif, Token::Else, Token::End, Token::If],
        );

        do_ok_test(
            "if then elseif else end if",
            &[Token::If, Token::Then, Token::Elseif, Token::Else, Token::End, Token::If],
        );
    }

    #[test]
    fn test_for() {
        do_ok_test("FOR TO STEP NEXT", &[Token::For, Token::To, Token::Step, Token::Next]);

        do_ok_test("for to step next", &[Token::For, Token::To, Token::Step, Token::Next]);
    }

    #[test]
    fn test_while() {
        do_ok_test("WHILE END WHILE", &[Token::While, Token::End, Token::While]);

        do_ok_test("while end while", &[Token::While, Token::End, Token::While]);
    }

    /// Syntactic sugar to instantiate a test that verifies the parsing of an operator.
    fn do_operator_test(op: &str, t: Token) {
        do_ok_test(format!("a {} 2", op).as_ref(), &[new_auto_symbol("a"), t, Token::Integer(2)]);
    }

    #[test]
    fn test_operator_relational_ops() {
        do_operator_test("=", Token::Equal);
        do_operator_test("<>", Token::NotEqual);
        do_operator_test("<", Token::Less);
        do_operator_test("<=", Token::LessEqual);
        do_operator_test(">", Token::Greater);
        do_operator_test(">=", Token::GreaterEqual);
    }

    #[test]
    fn test_operator_arithmetic_ops() {
        do_operator_test("+", Token::Plus);
        do_operator_test("-", Token::Minus);
        do_operator_test("*", Token::Multiply);
        do_operator_test("/", Token::Divide);
        do_operator_test("MOD", Token::Modulo);
        do_operator_test("mod", Token::Modulo);
    }

    #[test]
    fn test_operator_no_spaces() {
        do_ok_test(
            "z=2 654<>a32",
            &[
                new_auto_symbol("z"),
                Token::Equal,
                Token::Integer(2),
                Token::Integer(654),
                Token::NotEqual,
                new_auto_symbol("a32"),
            ],
        );
    }

    #[test]
    fn test_parenthesis() {
        do_ok_test(
            "(a) (\"foo\") (3)",
            &[
                Token::LeftParen,
                new_auto_symbol("a"),
                Token::RightParen,
                Token::LeftParen,
                Token::Text("foo".to_owned()),
                Token::RightParen,
                Token::LeftParen,
                Token::Integer(3),
                Token::RightParen,
            ],
        );
    }

    #[test]
    fn test_peekable_lexer() {
        let mut input = b"a b 123".as_ref();
        let mut lexer = Lexer::from(&mut input).peekable();
        assert_eq!(&new_auto_symbol("a"), lexer.peek().unwrap());
        assert_eq!(&new_auto_symbol("a"), lexer.peek().unwrap());
        assert_eq!(new_auto_symbol("a"), lexer.read().unwrap());
        assert_eq!(new_auto_symbol("b"), lexer.read().unwrap());
        assert_eq!(&Token::Integer(123), lexer.peek().unwrap());
        assert_eq!(Token::Integer(123), lexer.read().unwrap());
        assert_eq!(&Token::Eof, lexer.peek().unwrap());
        assert_eq!(Token::Eof, lexer.read().unwrap());
    }

    #[test]
    fn test_recoverable_errors() {
        do_ok_test(
            "9999999999+5",
            &[
                Token::Bad(
                    "Bad integer 9999999999: number too large to fit in target type".to_owned(),
                ),
                Token::Plus,
                Token::Integer(5),
            ],
        );

        do_ok_test(
            "\n3!2 1",
            &[
                Token::Eol,
                Token::Bad("Unexpected character in integer: !".to_owned()),
                Token::Integer(1),
            ],
        );

        do_ok_test(
            "a b|d 5",
            &[
                new_auto_symbol("a"),
                Token::Bad("Unexpected character in symbol: |".to_owned()),
                Token::Integer(5),
            ],
        );

        do_ok_test(
            "( \"this is incomplete",
            &[
                Token::LeftParen,
                Token::Bad("Incomplete string due to EOF: this is incomplete".to_owned()),
            ],
        );

        do_ok_test(
            "+ - ! * /",
            &[
                Token::Plus,
                Token::Minus,
                Token::Bad("Unknown character: !".to_owned()),
                Token::Multiply,
                Token::Divide,
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
        assert_eq!(Token::Integer(3), lexer.read().unwrap());
        assert_eq!(Token::Plus, lexer.read().unwrap());
        assert_eq!(Token::Integer(5), lexer.read().unwrap());
        assert_eq!(Token::Eol, lexer.read().unwrap());
        let e = lexer.read().unwrap_err();
        assert_eq!(io::ErrorKind::InvalidData, e.kind());
        let e = lexer.read().unwrap_err();
        assert_eq!(io::ErrorKind::Other, e.kind());
    }
}
