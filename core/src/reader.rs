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

//! Character-based reader for an input stream with position tracking.

use std::cell::RefCell;
use std::char;
use std::io::{self, BufRead};
use std::rc::Rc;

/// Tab length used to compute the current position within a line when encountering a tab character.
const TAB_LENGTH: usize = 8;

/// Representation of a position within a stream.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LineCol {
    /// Line number.
    pub(crate) line: usize,

    /// Column number.
    pub(crate) col: usize,
}

#[derive(Debug)]
#[cfg_attr(test, derive(Eq, PartialEq))]
pub struct CharSpan {
    /// Character in this span.
    pub(crate) ch: char,

    /// Position where this character starts.
    pub(crate) pos: LineCol,
}

/// Possible types of buffered data in the reader.
enum Pending {
    /// Initial state of the reader where no data has been buffered yet.
    Unknown,

    /// Intermediate state where the reader holds a line of text, broken down by character, and an
    /// index to the character to return on the next read.
    Chars(Vec<char>, usize),

    /// Terminal state of the reader due to an EOF condition.
    Eof,

    /// Terminal state of the reader due to an error.  If not `None`, this contains the original
    /// error that caused the problem.  Otherwise, that error was already consumed (and thus
    /// reaching this case indicates a problem in the caller) so we return an invalid state.
    Error(Option<io::Error>),
}

/// Wraps `io::Read` to offer an iterator over characters.
pub struct CharReader<'a> {
    /// The wrapper reader from which to reach characters.
    reader: io::BufReader<&'a mut dyn io::Read>,

    /// Current state of any buffered data.
    pending: Pending,

    /// Line and column number of the next character to be read.
    next_pos: Rc<RefCell<LineCol>>,
}

impl<'a> CharReader<'a> {
    /// Constructs a new character reader from an `io::Read`.
    pub fn from(reader: &'a mut dyn io::Read) -> Self {
        Self {
            reader: io::BufReader::new(reader),
            pending: Pending::Unknown,
            next_pos: Rc::from(RefCell::from(LineCol { line: 1, col: 1 })),
        }
    }

    /// Replenishes `pending` with the next line to process.
    fn refill_and_next(&mut self) -> Option<io::Result<CharSpan>> {
        self.pending = {
            let mut line = String::new();
            match self.reader.read_line(&mut line) {
                Ok(0) => Pending::Eof,
                Ok(_) => Pending::Chars(line.chars().collect(), 0),
                Err(e) => Pending::Error(Some(e)),
            }
        };
        self.next()
    }

    /// Obtains a view of the next position observed by this reader, which is necessary to compute
    /// the location of EOF when the iterator is fully consumed.
    pub(crate) fn next_pos_watcher(&self) -> Rc<RefCell<LineCol>> {
        self.next_pos.clone()
    }
}

impl<'a> Iterator for CharReader<'a> {
    type Item = io::Result<CharSpan>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.pending {
            Pending::Unknown => self.refill_and_next(),
            Pending::Eof => None,
            Pending::Chars(chars, last) => {
                if *last == chars.len() {
                    self.refill_and_next()
                } else {
                    let ch = chars[*last];
                    *last += 1;

                    let mut next_pos = self.next_pos.borrow_mut();
                    let pos = *next_pos;
                    match ch {
                        '\n' => {
                            next_pos.line += 1;
                            next_pos.col = 1;
                        }
                        '\t' => {
                            next_pos.col =
                                (next_pos.col - 1 + TAB_LENGTH) / TAB_LENGTH * TAB_LENGTH + 1;
                        }
                        _ => {
                            next_pos.col += 1;
                        }
                    }

                    Some(Ok(CharSpan { ch, pos }))
                }
            }
            Pending::Error(e) => match e.take() {
                Some(e) => Some(Err(e)),
                None => Some(Err(io::Error::new(
                    io::ErrorKind::Other,
                    "Invalid state; error already consumed",
                ))),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Syntactic sugar to instantiate a `CharSpan` for testing.
    fn cs(ch: char, line: usize, col: usize) -> CharSpan {
        CharSpan { ch, pos: LineCol { line, col } }
    }

    #[test]
    fn test_empty() {
        let mut input = b"".as_ref();
        let mut reader = CharReader::from(&mut input);
        assert!(reader.next().is_none());
    }

    #[test]
    fn test_multibyte_chars() {
        let mut input = "Hi 훌리오".as_bytes();
        let mut reader = CharReader::from(&mut input);
        assert_eq!(cs('H', 1, 1), reader.next().unwrap().unwrap());
        assert_eq!(cs('i', 1, 2), reader.next().unwrap().unwrap());
        assert_eq!(cs(' ', 1, 3), reader.next().unwrap().unwrap());
        assert_eq!(cs('훌', 1, 4), reader.next().unwrap().unwrap());
        assert_eq!(cs('리', 1, 5), reader.next().unwrap().unwrap());
        assert_eq!(cs('오', 1, 6), reader.next().unwrap().unwrap());
        assert!(reader.next().is_none());
    }

    #[test]
    fn test_consecutive_newlines() {
        let mut input = b"a\n\nbc\n".as_ref();
        let mut reader = CharReader::from(&mut input);
        assert_eq!(cs('a', 1, 1), reader.next().unwrap().unwrap());
        assert_eq!(cs('\n', 1, 2), reader.next().unwrap().unwrap());
        assert_eq!(cs('\n', 2, 1), reader.next().unwrap().unwrap());
        assert_eq!(cs('b', 3, 1), reader.next().unwrap().unwrap());
        assert_eq!(cs('c', 3, 2), reader.next().unwrap().unwrap());
        assert_eq!(cs('\n', 3, 3), reader.next().unwrap().unwrap());
        assert!(reader.next().is_none());
    }

    #[test]
    fn test_tabs() {
        let mut input = "1\t9\n1234567\t8\n12345678\t9".as_bytes();
        let mut reader = CharReader::from(&mut input);
        assert_eq!(cs('1', 1, 1), reader.next().unwrap().unwrap());
        assert_eq!(cs('\t', 1, 2), reader.next().unwrap().unwrap());
        assert_eq!(cs('9', 1, 9), reader.next().unwrap().unwrap());
        assert_eq!(cs('\n', 1, 10), reader.next().unwrap().unwrap());
        assert_eq!(cs('1', 2, 1), reader.next().unwrap().unwrap());
        assert_eq!(cs('2', 2, 2), reader.next().unwrap().unwrap());
        assert_eq!(cs('3', 2, 3), reader.next().unwrap().unwrap());
        assert_eq!(cs('4', 2, 4), reader.next().unwrap().unwrap());
        assert_eq!(cs('5', 2, 5), reader.next().unwrap().unwrap());
        assert_eq!(cs('6', 2, 6), reader.next().unwrap().unwrap());
        assert_eq!(cs('7', 2, 7), reader.next().unwrap().unwrap());
        assert_eq!(cs('\t', 2, 8), reader.next().unwrap().unwrap());
        assert_eq!(cs('8', 2, 9), reader.next().unwrap().unwrap());
        assert_eq!(cs('\n', 2, 10), reader.next().unwrap().unwrap());
        assert_eq!(cs('1', 3, 1), reader.next().unwrap().unwrap());
        assert_eq!(cs('2', 3, 2), reader.next().unwrap().unwrap());
        assert_eq!(cs('3', 3, 3), reader.next().unwrap().unwrap());
        assert_eq!(cs('4', 3, 4), reader.next().unwrap().unwrap());
        assert_eq!(cs('5', 3, 5), reader.next().unwrap().unwrap());
        assert_eq!(cs('6', 3, 6), reader.next().unwrap().unwrap());
        assert_eq!(cs('7', 3, 7), reader.next().unwrap().unwrap());
        assert_eq!(cs('8', 3, 8), reader.next().unwrap().unwrap());
        assert_eq!(cs('\t', 3, 9), reader.next().unwrap().unwrap());
        assert_eq!(cs('9', 3, 17), reader.next().unwrap().unwrap());
        assert!(reader.next().is_none());
    }

    #[test]
    fn test_crlf() {
        let mut input = b"a\r\nb".as_ref();
        let mut reader = CharReader::from(&mut input);
        assert_eq!(cs('a', 1, 1), reader.next().unwrap().unwrap());
        assert_eq!(cs('\r', 1, 2), reader.next().unwrap().unwrap());
        assert_eq!(cs('\n', 1, 3), reader.next().unwrap().unwrap());
        assert_eq!(cs('b', 2, 1), reader.next().unwrap().unwrap());
        assert!(reader.next().is_none());
    }

    #[test]
    fn test_past_eof_returns_eof() {
        let mut input = b"a".as_ref();
        let mut reader = CharReader::from(&mut input);
        assert_eq!(cs('a', 1, 1), reader.next().unwrap().unwrap());
        assert!(reader.next().is_none());
        assert!(reader.next().is_none());
    }

    #[test]
    fn test_next_pos_watcher() {
        let mut input = "Hi".as_bytes();
        let mut reader = CharReader::from(&mut input);
        let next_pos_watcher = reader.next_pos_watcher();
        assert_eq!(LineCol { line: 1, col: 1 }, *next_pos_watcher.borrow());
        assert_eq!(cs('H', 1, 1), reader.next().unwrap().unwrap());
        assert_eq!(LineCol { line: 1, col: 2 }, *next_pos_watcher.borrow());
        assert_eq!(cs('i', 1, 2), reader.next().unwrap().unwrap());
        assert_eq!(LineCol { line: 1, col: 3 }, *next_pos_watcher.borrow());
        assert!(reader.next().is_none());
        assert_eq!(LineCol { line: 1, col: 3 }, *next_pos_watcher.borrow());
    }

    /// A reader that generates an error only on the Nth read operation.
    ///
    /// All other reads return a line with a single character in them with the assumption that the
    /// `CharReader` issues a single read per line.  If that assumption changes, the tests here may
    /// start failing.
    struct FaultyReader {
        current_read: usize,
        fail_at_read: usize,
    }

    impl FaultyReader {
        /// Creates a new reader that will fail at the `fail_at_read`th operation.
        fn new(fail_at_read: usize) -> Self {
            let current_read = 0;
            FaultyReader { current_read, fail_at_read }
        }
    }

    impl io::Read for FaultyReader {
        #[allow(clippy::branches_sharing_code)]
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            if self.current_read == self.fail_at_read {
                self.current_read += 1;
                Err(io::Error::from(io::ErrorKind::InvalidInput))
            } else {
                self.current_read += 1;
                buf[0] = b'1';
                buf[1] = b'\n';
                Ok(2)
            }
        }
    }

    #[test]
    fn test_errors_prevent_further_reads() {
        let mut reader = FaultyReader::new(2);
        let mut reader = CharReader::from(&mut reader);
        assert_eq!(cs('1', 1, 1), reader.next().unwrap().unwrap());
        assert_eq!(cs('\n', 1, 2), reader.next().unwrap().unwrap());
        assert_eq!(cs('1', 2, 1), reader.next().unwrap().unwrap());
        assert_eq!(cs('\n', 2, 2), reader.next().unwrap().unwrap());
        assert_eq!(io::ErrorKind::InvalidInput, reader.next().unwrap().unwrap_err().kind());
        assert_eq!(io::ErrorKind::Other, reader.next().unwrap().unwrap_err().kind());
        assert_eq!(io::ErrorKind::Other, reader.next().unwrap().unwrap_err().kind());
    }
}
