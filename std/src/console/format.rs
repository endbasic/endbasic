// EndBASIC
// Copyright 2021 Julio Merino
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

//! Utilities to format text.

use super::Pager;
use crate::console::Console;
use std::io;

/// Refills a paragraph to fit within a maximum width, returning the formatted lines.
///
/// This does not cut words half-way, which means that it may be impossible to fit certain words in
/// the specified width.  If that happens, lines will overflow.
fn refill(paragraph: &str, width: usize) -> Vec<String> {
    if paragraph.is_empty() {
        return vec!["".to_owned()];
    }

    let mut lines = vec![];

    let mut line = String::new();
    for word in paragraph.split_whitespace() {
        if !line.is_empty() {
            // Determine how many spaces to inject after a period.  We want 2 spaces to separate
            // different sentences and 1 otherwise.  The heuristic here isn't great and it'd be
            // better to respect the original spacing of the paragraph.
            let spaces = if line.ends_with('.') {
                let first = word.chars().next().expect("Words cannot be empty");
                if first == first.to_ascii_uppercase() { 2 } else { 1 }
            } else {
                1
            };

            if (line.len() + word.len() + spaces) >= width {
                lines.push(line);
                line = String::new();
            } else {
                for _ in 0..spaces {
                    line.push(' ');
                }
            }
        }
        line.push_str(word);
    }
    if !line.is_empty() {
        lines.push(line);
    }

    lines
}

/// Refills a collection of paragraphs, prefixing them with an optional `indent`.
fn refill_many<S: AsRef<str>, P: IntoIterator<Item = S>>(
    paragraphs: P,
    indent: &str,
    width: usize,
) -> Vec<String> {
    let mut formatted = vec![];

    let mut first = true;
    for paragraph in paragraphs {
        let paragraph = paragraph.as_ref();

        if !first {
            formatted.push(String::new());
        }
        first = false;

        let mut extra_indent = String::new();
        for ch in paragraph.chars() {
            // TODO(jmmv): It'd be nice to recognize '*' prefixes so that continuation lines in
            // lists look nicer.
            if ch.is_whitespace() {
                extra_indent.push(' ');
            } else {
                break;
            }
        }

        let lines = refill(paragraph, width - 4 - indent.len() - extra_indent.len());
        for line in lines {
            if line.is_empty() {
                formatted.push(String::new());
            } else {
                formatted.push(format!("{}{}{}", indent, extra_indent, line));
            }
        }
    }

    formatted
}

/// Same as `refill` but prints the lines of each paragraph to the console instead of returning
/// them and prefixes them with an optional `indent`.
///
/// The width is automatically determined from the console's size.
pub fn refill_and_print<S: AsRef<str>, P: IntoIterator<Item = S>>(
    console: &mut dyn Console,
    paragraphs: P,
    indent: &str,
) -> io::Result<()> {
    // TODO(jmmv): This queries the size on every print, which is not very efficient.  Should
    // reuse this across calls, maybe by having a wrapper over Console and using it throughout.
    let size = console.size_chars()?;
    for line in refill_many(paragraphs, indent, usize::from(size.x)) {
        console.print(&line)?;
    }
    Ok(())
}

/// Same as `refill` but prints the lines of each paragraph to a pager instead of returning
/// them and prefixes them with an optional `indent`.
///
/// The width is automatically determined from the console's size.
pub(crate) async fn refill_and_page<S: AsRef<str>, P: IntoIterator<Item = S>>(
    pager: &mut Pager<'_>,
    paragraphs: P,
    indent: &str,
) -> io::Result<()> {
    for line in refill_many(paragraphs, indent, usize::from(pager.columns())) {
        pager.print(&line).await?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::console::CharsXY;
    use crate::testutils::{CapturedOut, MockConsole};

    #[test]
    fn test_refill_empty() {
        assert_eq!(&[""], refill("", 0).as_slice());
        assert_eq!(&[""], refill("", 10).as_slice());
    }

    #[test]
    fn test_refill_nothing_fits() {
        assert_eq!(&["this", "is", "some", "text"], refill("this is some text", 0).as_slice());
        assert_eq!(&["this", "is", "some", "text"], refill("this is some text", 1).as_slice());
    }

    #[test]
    fn test_refill_some_lines() {
        assert_eq!(
            &["this is a piece", "of text with", "a-fictitious-very-long-word", "within it"],
            refill("this is a piece of text with a-fictitious-very-long-word within it", 16)
                .as_slice()
        );
    }

    #[test]
    fn test_refill_reformats_periods() {
        assert_eq!(&["foo. bar. baz."], refill("foo. bar.    baz.", 100).as_slice());
        assert_eq!(&["foo.  Bar. baz."], refill("foo. Bar.    baz.", 100).as_slice());
        assert_eq!(&["[some .. range]"], refill("[some .. range]", 100).as_slice());
    }

    #[test]
    fn test_refill_and_print_empty() {
        let mut console = MockConsole::default();
        let paragraphs: &[&str] = &[];
        refill_and_print(&mut console, paragraphs, "    ").unwrap();
        assert!(console.captured_out().is_empty());
    }

    #[test]
    fn test_refill_and_print_one() {
        let mut console = MockConsole::default();
        let paragraphs = &["First    paragraph"];
        refill_and_print(&mut console, paragraphs, "    ").unwrap();
        assert_eq!(&[CapturedOut::Print("    First paragraph".to_owned())], console.captured_out());
    }

    #[test]
    fn test_refill_and_print_multiple() {
        let mut console = MockConsole::default();
        let paragraphs = &["First    paragraph", "Second", "Third. The. end."];
        refill_and_print(&mut console, paragraphs, "    ").unwrap();
        assert_eq!(
            &[
                CapturedOut::Print("    First paragraph".to_owned()),
                CapturedOut::Print("".to_owned()),
                CapturedOut::Print("    Second".to_owned()),
                CapturedOut::Print("".to_owned()),
                CapturedOut::Print("    Third.  The. end.".to_owned()),
            ],
            console.captured_out()
        );
    }

    #[test]
    fn test_refill_and_print_multiple_with_extra_indent() {
        let mut console = MockConsole::default();
        console.set_size_chars(CharsXY { x: 30, y: 30 });
        let paragraphs = &[
            "First    paragraph that is somewhat long",
            "  The second paragraph contains an extra indent",
            "Third. The. end.",
        ];
        refill_and_print(&mut console, paragraphs, "    ").unwrap();
        assert_eq!(
            &[
                CapturedOut::Print("    First paragraph that".to_owned()),
                CapturedOut::Print("    is somewhat long".to_owned()),
                CapturedOut::Print("".to_owned()),
                CapturedOut::Print("      The second".to_owned()),
                CapturedOut::Print("      paragraph contains".to_owned()),
                CapturedOut::Print("      an extra indent".to_owned()),
                CapturedOut::Print("".to_owned()),
                CapturedOut::Print("    Third.  The. end.".to_owned()),
            ],
            console.captured_out()
        );
    }
}
