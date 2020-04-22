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

//! Character-based reader for an input stream.

use std::char;
use std::io::{self, BufRead};

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
}

impl<'a> CharReader<'a> {
    /// Constructs a new character reader from an `io::Read`.
    pub fn from(reader: &'a mut dyn io::Read) -> Self {
        Self {
            reader: io::BufReader::new(reader),
            pending: Pending::Unknown,
        }
    }

    /// Replenishes `pending` with the next line to process.
    fn refill_and_next(&mut self) -> Option<io::Result<char>> {
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
}

impl<'a> Iterator for CharReader<'a> {
    type Item = io::Result<char>;

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
                    Some(Ok(ch))
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

    #[test]
    fn test_empty() {
        let mut cursor = io::Cursor::new(b"");
        let mut reader = CharReader::from(&mut cursor);
        assert!(reader.next().is_none());
    }

    #[test]
    fn test_multibyte_chars() {
        let mut cursor = io::Cursor::new("Hi 훌리오".as_bytes());
        let mut reader = CharReader::from(&mut cursor);
        assert_eq!('H', reader.next().unwrap().unwrap());
        assert_eq!('i', reader.next().unwrap().unwrap());
        assert_eq!(' ', reader.next().unwrap().unwrap());
        assert_eq!('훌', reader.next().unwrap().unwrap());
        assert_eq!('리', reader.next().unwrap().unwrap());
        assert_eq!('오', reader.next().unwrap().unwrap());
        assert!(reader.next().is_none());
    }

    #[test]
    fn test_consecutive_newlines() {
        let mut cursor = io::Cursor::new(b"a\n\nbc\n");
        let mut reader = CharReader::from(&mut cursor);
        assert_eq!('a', reader.next().unwrap().unwrap());
        assert_eq!('\n', reader.next().unwrap().unwrap());
        assert_eq!('\n', reader.next().unwrap().unwrap());
        assert_eq!('b', reader.next().unwrap().unwrap());
        assert_eq!('c', reader.next().unwrap().unwrap());
        assert_eq!('\n', reader.next().unwrap().unwrap());
        assert!(reader.next().is_none());
    }

    #[test]
    fn test_past_eof_returns_eof() {
        let mut cursor = io::Cursor::new(b"a");
        let mut reader = CharReader::from(&mut cursor);
        assert_eq!('a', reader.next().unwrap().unwrap());
        assert!(reader.next().is_none());
        assert!(reader.next().is_none());
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
            FaultyReader {
                current_read,
                fail_at_read,
            }
        }
    }

    impl io::Read for FaultyReader {
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
        assert_eq!('1', reader.next().unwrap().unwrap());
        assert_eq!('\n', reader.next().unwrap().unwrap());
        assert_eq!('1', reader.next().unwrap().unwrap());
        assert_eq!('\n', reader.next().unwrap().unwrap());
        assert_eq!(
            io::ErrorKind::InvalidInput,
            reader.next().unwrap().unwrap_err().kind()
        );
        assert_eq!(
            io::ErrorKind::Other,
            reader.next().unwrap().unwrap_err().kind()
        );
        assert_eq!(
            io::ErrorKind::Other,
            reader.next().unwrap().unwrap_err().kind()
        );
    }
}
