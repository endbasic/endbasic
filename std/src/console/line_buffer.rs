//! String buffer used to manipulate String at the UTF-8 code point level
//! instead of Rust String byte level manipulation

use std::{fmt::Display, str::Chars};

#[derive(Default, Debug)]
/// Handle string manipulation like inserting a char at a specified char position.
///
/// This exists because Rust String is indexed by bytes and manipulating string bytes is
/// complicated.
///
/// The current implementation of the line buffer is using String::chars .
///
/// TODO: use graphemes instead.
pub struct LineBuffer {
    line: String,
}

impl LineBuffer {
    /// Create an empty LineBuffer
    pub fn new() -> Self {
        Default::default()
    }

    /// Create an empty LineBuffer with the allocated capacity
    pub fn with_capacity(capacity: usize) -> Self {
        Self { line: String::with_capacity(capacity) }
    }

    /// Return the logical LineBuffer length (in UTF-8 code point count and not in bytes)
    pub fn len(&self) -> usize {
        self.line.chars().count()
    }

    /// Iterator over buffer chars.
    pub fn chars(&self) -> Chars {
        self.line.chars()
    }

    /// return the end of the string starting at the given position ; an empty string is
    /// returned if start_pos > self.len()
    pub fn end(&self, start_pos: usize) -> String {
        self.chars().skip(start_pos).collect()
    }

    /// Return the characters from the start if the string to the given position, excluding the position
    ///
    /// Calling it with 0 will return an empty string, 1, will return a 1-char String (is the string
    /// contains at least 1 char)
    pub fn start(&self, end_pos: usize) -> String {
        self.chars().take(end_pos).collect()
    }

    /// Extract a range of chars from this buffer.
    pub fn range(&self, start_pos: usize, end_pos: usize) -> String {
        let count = if start_pos > end_pos { 0 } else { end_pos - start_pos };
        self.chars().skip(start_pos).take(count).collect()
    }

    /// Is this buffer empty?
    pub fn is_empty(&self) -> bool {
        self.line.is_empty()
    }

    /// Get a view on the underlying bytes hold by this buffer.
    ///
    /// Warning: direct bytes manipulation may lead to undefined behavior
    pub fn as_bytes(&self) -> &[u8] {
        self.line.as_bytes()
    }

    /// Remove a char from this buffer.
    ///
    /// If the given position if greater than the length of the buffer, this function will do nothing.
    pub fn remove(&mut self, pos: usize) {
        self.line = self.line.chars().take(pos).chain(self.line.chars().skip(pos + 1)).collect();
    }

    /// Insert a char at the given position.
    ///
    /// If the position is greater than the buffer length, the char will be appended at the end ot it
    pub fn insert(&mut self, pos: usize, ch: char) {
        self.line = self
            .line
            .chars()
            .take(pos)
            .chain(std::iter::once(ch))
            .chain(self.line.chars().skip(pos))
            .collect();
    }

    /// Return the underlying String
    pub fn into_inner(self) -> String {
        self.line
    }

    /// Insert the given string into the buffer at the given position.
    ///
    /// If the position is greater than the length of the buffer, the string will be appened at the end
    /// of it.
    pub fn insert_str(&mut self, pos: usize, s: &str) {
        self.line = self
            .line
            .chars()
            .take(pos)
            .chain(s.chars())
            .chain(self.line.chars().skip(pos))
            .collect();
    }

    /// Append the given string to the buffer.
    pub fn push_str(&mut self, s: &LineBuffer) {
        self.line.push_str(&s.line);
    }

    /// Split the buffer in two parts at the given position.
    ///
    /// Return the remaining part of the buffer (same behavior as String::split_off)
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
        let empty = LineBuffer::from("");
        assert_eq!(empty.end(0), "");
        assert_eq!(empty.end(1), ""); // it won't panic even is the given position does not make any sense.
        let hw = LineBuffer::from("Hello, World");

        assert_eq!(hw.end(0), "Hello, World");
        assert_eq!(hw.end(7), "World");
        assert_eq!(hw.end(100), "");
    }

    #[test]
    fn test_start() {
        let empty = LineBuffer::from("");
        assert_eq!(empty.start(0), "");
        assert_eq!(empty.start(1), ""); // it won't panic even is the given position does not make any sense.
        let hw = LineBuffer::from("Hello, World");

        assert_eq!(hw.start(0), "");
        assert_eq!(hw.start(7), "Hello, ");
        assert_eq!(hw.start(100), "Hello, World");
    }

    #[test]
    fn test_insert() {
        let mut buffer = LineBuffer::from("");
        buffer.insert(0, 'c'); // c
        buffer.insert(0, 'é'); // éc

        // insertion must happen after the 2-bytes utf-8 code point and not the byte 1:
        buffer.insert(1, 'à'); // éàc
        buffer.insert(100, 'd'); // éàcd dumb position will not make insert panic.

        assert_eq!(buffer.into_inner(), "éàcd");
    }

    #[test]
    fn test_remove() {
        let mut empty = LineBuffer::from("");
        empty.remove(0);
        empty.remove(5);
        assert_eq!(empty.into_inner(), "");

        let mut hello = LineBuffer::from("Hello");
        hello.remove(100); // do nothing
        hello.remove(1); // remove the 'e'
        assert_eq!(hello.into_inner(), "Hllo");
    }

    #[test]
    fn test_insert_str() {
        let mut buffer = LineBuffer::from("");
        buffer.insert_str(0, "Hello");
        assert_eq!(buffer.end(0), "Hello");
        buffer.insert_str(100, "World"); // pos>len will insert at the end.
        assert_eq!(buffer.end(0), "HelloWorld");
        buffer.insert_str(5, ", ");
        assert_eq!(buffer.end(0), "Hello, World");
    }

    #[test]
    fn test_range() {
        let mut buffer = LineBuffer::new();

        assert_eq!(buffer.range(0, 0), "");
        assert_eq!(buffer.range(0, 10), "");
        assert_eq!(buffer.range(0, 10), "");
        assert_eq!(buffer.range(10, 0), ""); // do not panic on stupid indexes

        buffer.insert_str(0, "Hello, World");
        assert_eq!(buffer.range(0, 5), "Hello");
        assert_eq!(buffer.range(7, 10), "Wor");
        assert_eq!(buffer.range(7, 100), "World");
        assert_eq!(buffer.range(10, 0), ""); // do not panic on stupid indexes
    }

    #[test]
    fn test_is_empty() {
        assert!(LineBuffer::new().is_empty());
        assert!(LineBuffer::new().is_empty());
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
