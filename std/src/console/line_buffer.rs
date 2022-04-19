//! Handle string manipulation like inserting a char at a specified char position.
//!
//! This exists because Rust String is indexed by bytes and manipulating string bytes is
//! complicated!
//!
//! The current implementation of the line buffer is using String::chars && String::char_indices.
//!
//! TODO: use graphemes instead.

use std::{fmt::Display, str::Chars};

#[derive(Default, Debug)]
pub struct LineBuffer {
    line: String,
}

impl LineBuffer {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self { line: String::with_capacity(capacity) }
    }

    pub fn len(&self) -> usize {
        self.line.chars().count()
    }

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

    pub fn range(&self, start_pos: usize, end_pos: usize) -> String {
        let count = if start_pos > end_pos { 0 } else { end_pos - start_pos };
        self.chars().skip(start_pos).take(count).collect()
    }

    pub fn is_empty(&self) -> bool {
        self.line.is_empty()
    }

    pub fn as_bytes(&self) -> &[u8] {
        self.line.as_bytes()
    }

    pub fn remove(&mut self, pos: usize) {
        self.line = self.line.chars().take(pos).chain(self.line.chars().skip(pos + 1)).collect();
    }

    pub fn insert(&mut self, pos: usize, ch: char) {
        self.line = self
            .line
            .chars()
            .take(pos)
            .chain(std::iter::once(ch))
            .chain(self.line.chars().skip(pos))
            .collect();
    }

    pub fn into_inner(self) -> String {
        self.line
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

impl Display for LineBuffer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.line.fmt(f)
    }
}
