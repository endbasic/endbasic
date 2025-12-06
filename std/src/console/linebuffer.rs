// EndBASIC
// Copyright 2022 Philippe GASSMANN
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

//! String buffer used to manipulate strings at the UTF-8 code point level instead of at the byte
//! level.

use std::fmt::Display;
use std::iter;
use std::str::Chars;

#[derive(Default, Debug)]
/// Abstraction over a string to handle manipulation operations at char boundaries.
///
/// This exists because Rust strings are indexed by bytes and manipulating string bytes is
/// complicated.
///
/// TODO(zenria): The current implementation of the buffer is using `String::chars`.  Should be
/// converted to using graphemes instead.
pub struct LineBuffer {
    line: String,
}

impl LineBuffer {
    /// Creates an empty `LineBuffer` with an allocated `capacity`.
    pub fn with_capacity(capacity: usize) -> Self {
        Self { line: String::with_capacity(capacity) }
    }

    /// Returns the logical `LineBuffer` length (in UTF-8 code point count and not in bytes).
    pub fn len(&self) -> usize {
        self.line.chars().count()
    }

    /// Gets and iterator over buffer chars.
    pub fn chars(&self) -> Chars<'_> {
        self.line.chars()
    }

    /// Returns the end of the string starting at `start_pos`, or an empty string if `start_pos` is
    /// after the string's end.
    pub fn end(&self, start_pos: usize) -> String {
        self.chars().skip(start_pos).collect()
    }

    /// Returns the characters from the start of the string to `end_pos`, excluding `end_pos`.
    ///
    /// Calling this with `end_pos` set to 0 will return an empty string, and a 1-char string if
    /// `end_pos` is 1 (if the string contains at least 1 character).
    pub fn start(&self, end_pos: usize) -> String {
        self.chars().take(end_pos).collect()
    }

    /// Extracts a range of characters from this buffer.
    pub fn range(&self, start_pos: usize, end_pos: usize) -> String {
        let count = end_pos.saturating_sub(start_pos);
        self.chars().skip(start_pos).take(count).collect()
    }

    /// Checks if this buffer is empty or not.
    pub fn is_empty(&self) -> bool {
        self.line.is_empty()
    }

    /// Gets a view on the underlying bytes held by this buffer.
    ///
    /// Warning: direct bytes manipulation may lead to undefined behavior.
    pub fn as_bytes(&self) -> &[u8] {
        self.line.as_bytes()
    }

    /// Removes a character from this buffer.
    ///
    /// If the given position if greater than the length of the buffer, this function does nothing.
    pub fn remove(&mut self, pos: usize) {
        self.line = self.line.chars().take(pos).chain(self.line.chars().skip(pos + 1)).collect();
    }

    /// Inserts a char at the given position.
    ///
    /// If the position is greater than the buffer length, the character will be appended at the
    /// end ot it.
    pub fn insert(&mut self, pos: usize, ch: char) {
        self.line = self
            .line
            .chars()
            .take(pos)
            .chain(iter::once(ch))
            .chain(self.line.chars().skip(pos))
            .collect();
    }

    /// Returns the underlying string.
    pub fn into_inner(self) -> String {
        self.line
    }

    /// Inserts the given string `s` into the buffer at `pos`.
    ///
    /// If `pos` is greater than the length of the buffer, `s` will be appended at the end of it.
    pub fn insert_str(&mut self, pos: usize, s: &str) {
        self.line = self
            .line
            .chars()
            .take(pos)
            .chain(s.chars())
            .chain(self.line.chars().skip(pos))
            .collect();
    }

    /// Appends the given string `s` to the buffer.
    pub fn push_str(&mut self, s: &LineBuffer) {
        self.line.push_str(&s.line);
    }

    /// Splits the buffer in two parts at the position `at`.
    ///
    /// Returns the remaining part of the buffer (same behavior as `String::split_off`).
    pub fn split_off(&mut self, at: usize) -> LineBuffer {
        let ret = LineBuffer::from(self.line.chars().skip(at).collect::<String>());
        self.line = self.line.chars().take(at).collect();
        ret
    }
}

impl From<&str> for LineBuffer {
    fn from(s: &str) -> Self {
        Self { line: String::from(s) }
    }
}

impl From<&String> for LineBuffer {
    fn from(s: &String) -> Self {
        Self::from(s.as_str())
    }
}
impl From<String> for LineBuffer {
    fn from(line: String) -> Self {
        Self { line }
    }
}

impl Display for LineBuffer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.line.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::LineBuffer;

    #[test]
    fn test_end() {
        let empty = LineBuffer::default();
        assert_eq!(empty.end(0), "");
        assert_eq!(empty.end(1), ""); // Should not panic even if the given position is invalid.
        let hw = LineBuffer::from("Hello, World");

        assert_eq!(hw.end(0), "Hello, World");
        assert_eq!(hw.end(7), "World");
        assert_eq!(hw.end(100), "");
    }

    #[test]
    fn test_start() {
        let empty = LineBuffer::default();
        assert_eq!(empty.start(0), "");
        assert_eq!(empty.start(1), ""); // Should not panic even if the given position is invalid.
        let hw = LineBuffer::from("Hello, World");

        assert_eq!(hw.start(0), "");
        assert_eq!(hw.start(7), "Hello, ");
        assert_eq!(hw.start(100), "Hello, World");
    }

    #[test]
    fn test_insert() {
        let mut buffer = LineBuffer::default();
        buffer.insert(0, 'c'); // c
        buffer.insert(0, 'é'); // éc

        // Insertion must happen after the 2-byte UTF-8 code point and not at byte 1.
        buffer.insert(1, 'à'); // éàc
        buffer.insert(100, 'd'); // Should not panic even if the given position is invalid.

        assert_eq!(buffer.into_inner(), "éàcd");
    }

    #[test]
    fn test_remove() {
        let mut empty = LineBuffer::default();
        empty.remove(0);
        empty.remove(5);
        assert_eq!(empty.into_inner(), "");

        let mut hello = LineBuffer::from("Hello");
        hello.remove(100); // Do nothing.
        hello.remove(1); // Remove the 'e'
        assert_eq!(hello.into_inner(), "Hllo");
    }

    #[test]
    fn test_insert_str() {
        let mut buffer = LineBuffer::default();
        buffer.insert_str(0, "Hello");
        assert_eq!(buffer.end(0), "Hello");
        buffer.insert_str(100, "World"); // pos > len will insert at the end.
        assert_eq!(buffer.end(0), "HelloWorld");
        buffer.insert_str(5, ", ");
        assert_eq!(buffer.end(0), "Hello, World");
    }

    #[test]
    fn test_range() {
        let mut buffer = LineBuffer::default();

        assert_eq!(buffer.range(0, 0), "");
        assert_eq!(buffer.range(0, 10), "");
        assert_eq!(buffer.range(0, 10), "");
        assert_eq!(buffer.range(10, 0), ""); // Should not panic even with bad indexes.

        buffer.insert_str(0, "Hello, World");
        assert_eq!(buffer.range(0, 5), "Hello");
        assert_eq!(buffer.range(7, 10), "Wor");
        assert_eq!(buffer.range(7, 100), "World");
        assert_eq!(buffer.range(10, 0), ""); // Should not panic even with bad indexes.
    }

    #[test]
    fn test_is_empty() {
        assert!(LineBuffer::default().is_empty());
        assert!(LineBuffer::from("").is_empty());
        assert!(!LineBuffer::from("This is not empty").is_empty());
    }

    #[test]
    fn test_split_off() {
        let mut buffer = LineBuffer::from("Hello, World");
        let world = buffer.split_off(7);
        assert_eq!(buffer.into_inner(), "Hello, ");
        assert_eq!(world.into_inner(), "World");
    }
}
