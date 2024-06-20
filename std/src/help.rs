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

//! Interactive help support.

use crate::console::{refill_and_print, AnsiColor, Console};
use crate::exec::CATEGORY;
use async_trait::async_trait;
use endbasic_core::ast::{ExprType, Value, VarType};
use endbasic_core::compiler::{ArgSepSyntax, RequiredValueSyntax, SingularArgSyntax};
use endbasic_core::exec::{Machine, Scope};
use endbasic_core::syms::{
    CallError, CallResult, Callable, CallableMetadata, CallableMetadataBuilder, Symbols,
};
use endbasic_core::LineCol;
use radix_trie::{Trie, TrieCommon};
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::io;
use std::rc::Rc;

/// Raw text for the language reference.
const LANG_MD: &str = include_str!("lang.md");

/// Color for titles.
const TITLE_COLOR: u8 = AnsiColor::BrightYellow as u8;

/// Color for references to other topics.
const LINK_COLOR: u8 = AnsiColor::BrightCyan as u8;

/// Returns the header for the help summary.
fn header() -> Vec<String> {
    vec![
        "".to_owned(),
        format!("    This is EndBASIC {}.", env!("CARGO_PKG_VERSION")),
        "".to_owned(),
        format!("    Project page at <{}>", env!("CARGO_PKG_HOMEPAGE")),
        "    License Apache Version 2.0 <http://www.apache.org/licenses/LICENSE-2.0>".to_owned(),
    ]
}

/// Handler for a specific help topic.
trait Topic {
    /// Returns the name of the topic.
    fn name(&self) -> &str;

    /// Returns the human-readable, one-line description of this topic.
    fn title(&self) -> &str;

    /// Indicates whether this topic shows up in the topics summary or not.
    fn show_in_summary(&self) -> bool;

    /// Dumps the contents of this topic to the `_console`.
    fn describe(&self, _console: &mut dyn Console) -> io::Result<()>;
}

/// A help topic to describe a callable.
struct CallableTopic {
    name: String,
    metadata: CallableMetadata,
}

impl Topic for CallableTopic {
    fn name(&self) -> &str {
        &self.name
    }

    fn title(&self) -> &str {
        self.metadata.description().next().unwrap()
    }

    fn show_in_summary(&self) -> bool {
        false
    }

    fn describe(&self, console: &mut dyn Console) -> io::Result<()> {
        console.print("")?;
        let previous = console.color();
        console.set_color(Some(TITLE_COLOR), previous.1)?;
        if self.metadata.return_type() == VarType::Void {
            if self.metadata.syntax().is_empty() {
                refill_and_print(console, [self.metadata.name()], "    ")?;
            } else {
                refill_and_print(
                    console,
                    [&format!("{} {}", self.metadata.name(), self.metadata.syntax())],
                    "    ",
                )?;
            }
        } else {
            if self.metadata.is_argless() {
                debug_assert!(self.metadata.syntax().is_empty());
                refill_and_print(
                    console,
                    [&format!(
                        "{}{}",
                        self.metadata.name(),
                        self.metadata.return_type().annotation(),
                    )],
                    "    ",
                )?;
            } else {
                refill_and_print(
                    console,
                    [&format!(
                        "{}{}({})",
                        self.metadata.name(),
                        self.metadata.return_type().annotation(),
                        self.metadata.syntax(),
                    )],
                    "    ",
                )?;
            }
        }
        console.set_color(previous.0, previous.1)?;
        if !self.metadata.description().count() > 0 {
            console.print("")?;
            refill_and_print(console, self.metadata.description(), "    ")?;
        }
        console.print("")?;
        Ok(())
    }
}

/// Generates the index for a collection of `CallableMetadata`s to use in a `CategoryTopic`.
fn callables_to_index(metadatas: &[CallableMetadata]) -> BTreeMap<String, &'static str> {
    let category = metadatas.first().expect("Must have at least one symbol").category();

    let mut index = BTreeMap::default();
    for metadata in metadatas {
        debug_assert_eq!(
            category,
            metadata.category(),
            "All commands registered in this category must be equivalent"
        );
        let name = format!("{}{}", metadata.name(), metadata.return_type().annotation());
        let blurb = metadata.description().next().unwrap();
        let previous = index.insert(name, blurb);
        assert!(previous.is_none(), "Names should have been unique");
    }
    index
}

/// A help topic to describe a category of callables.
struct CategoryTopic {
    name: &'static str,
    description: &'static str,
    index: BTreeMap<String, &'static str>,
}

impl Topic for CategoryTopic {
    fn name(&self) -> &str {
        self.name
    }

    fn title(&self) -> &str {
        self.name
    }

    fn show_in_summary(&self) -> bool {
        true
    }

    fn describe(&self, console: &mut dyn Console) -> io::Result<()> {
        let max_length = self
            .index
            .keys()
            .map(|k| k.len())
            .reduce(|a, k| if a > k { a } else { k })
            .expect("Must have at least one item in the index");

        let previous = console.color();

        let mut lines = self.description.lines().peekable();
        console.print("")?;
        console.set_color(Some(TITLE_COLOR), previous.1)?;
        refill_and_print(console, lines.next(), "    ")?;
        console.set_color(previous.0, previous.1)?;
        if lines.peek().is_some() {
            console.print("")?;
        }
        refill_and_print(console, lines, "    ")?;
        console.print("")?;

        for (name, blurb) in self.index.iter() {
            let filler = " ".repeat(max_length - name.len());
            // TODO(jmmv): Should use refill_and_print but continuation lines need special handling
            // to be indented properly.
            console.write("    >> ")?;
            console.set_color(Some(LINK_COLOR), previous.1)?;
            console.write(&format!("{}{}", name, filler))?;
            console.set_color(previous.0, previous.1)?;
            console.print(&format!("    {}", blurb))?;
        }
        console.print("")?;
        refill_and_print(
            console,
            ["Type HELP followed by the name of a topic for details."],
            "    ",
        )?;
        console.print("")?;
        Ok(())
    }
}

/// A help topic to describe a non-callable help topic.
struct LanguageTopic {
    name: &'static str,
    text: &'static str,
}

impl Topic for LanguageTopic {
    fn name(&self) -> &str {
        self.name
    }

    fn title(&self) -> &str {
        self.text.lines().next().unwrap()
    }

    fn show_in_summary(&self) -> bool {
        false
    }

    fn describe(&self, console: &mut dyn Console) -> io::Result<()> {
        let previous = console.color();

        let mut lines = self.text.lines();

        console.print("")?;
        console.set_color(Some(TITLE_COLOR), previous.1)?;
        refill_and_print(console, [lines.next().expect("Must have at least one line")], "    ")?;
        console.set_color(previous.0, previous.1)?;
        for line in lines {
            if line.is_empty() {
                console.print("")?;
            } else {
                refill_and_print(console, [line], "    ")?;
            }
        }
        console.print("")?;
        Ok(())
    }
}

/// Parses the `lang.md` file and extracts a mapping of language reference topics to their
/// descriptions.
///
/// Note that, even if the input looks like Markdown, we do *not* implement a Markdown parser here.
/// The structure of the file is strict and well-known in advance, so this will panic if there are
/// problems in the input data.
fn parse_lang_reference(lang_md: &'static str) -> Vec<(&'static str, &'static str)> {
    let mut topics = vec![];

    // Cope with Windows checkouts.  It's tempting to make this a build-time conditional on the OS
    // name, but we don't know how the files are checked out.  Assume CRLF delimiters if we see at
    // least one of them.
    let line_end;
    let section_start;
    let body_start;
    if lang_md.contains("\r\n") {
        line_end = "\r\n";
        section_start = "\r\n\r\n# ";
        body_start = "\r\n\r\n";
    } else {
        line_end = "\n";
        section_start = "\n\n# ";
        body_start = "\n\n";
    }

    for (start, _match) in lang_md.match_indices(section_start) {
        let section = &lang_md[start + section_start.len()..];

        let title_end = section.find(body_start).expect("Hardcoded text must be valid");
        let title = &section[..title_end];
        let section = &section[title_end + body_start.len()..];

        let end = section.find(section_start).unwrap_or_else(|| {
            if section.ends_with(line_end) {
                section.len() - line_end.len()
            } else {
                section.len()
            }
        });
        let content = &section[..end];
        topics.push((title, content));
    }

    topics
}

/// Maintains the collection of topics as a trie indexed by their name.
struct Topics(Trie<String, Box<dyn Topic>>);

impl Topics {
    /// Builds an index of the given `symbols` and returns a new collection of help topics.
    fn new(symbols: &Symbols) -> Self {
        fn insert(topics: &mut Trie<String, Box<dyn Topic>>, topic: Box<dyn Topic>) {
            let key = topic.name().to_ascii_uppercase();
            topics.insert(key, topic);
        }

        let mut topics = Trie::default();

        {
            let mut index = BTreeMap::default();

            for (title, content) in parse_lang_reference(LANG_MD) {
                let topic = LanguageTopic { name: title, text: content };
                index.insert(topic.name.to_owned(), topic.text.lines().next().unwrap());
                insert(&mut topics, Box::from(topic));
            }

            insert(
                &mut topics,
                Box::from(CategoryTopic {
                    name: "Language reference",
                    description: "General language topics",
                    index,
                }),
            );
        }

        let mut categories = HashMap::new();
        for (name, symbol) in symbols.as_hashmap().iter() {
            if let Some(metadata) = symbol.metadata() {
                let category_title = metadata.category().lines().next().unwrap();
                categories
                    .entry(category_title)
                    .or_insert_with(Vec::default)
                    .push(metadata.clone());

                insert(
                    &mut topics,
                    Box::from(CallableTopic {
                        name: format!("{}{}", name, metadata.return_type().annotation()),
                        metadata: metadata.clone(),
                    }),
                );
            }
        }
        for (name, metadatas) in categories.into_iter() {
            let description = metadatas.first().expect("Must have at least one symbol").category();
            let index = callables_to_index(&metadatas);
            insert(&mut topics, Box::from(CategoryTopic { name, description, index }));
        }

        Self(topics)
    }

    /// Returns the given topic named `name`, where `name` can be a prefix.
    ///
    /// If `name` is not long enough to uniquely identify a topic or if the topic does not exist,
    /// returns an error.
    fn find(&self, name: &str, pos: LineCol) -> Result<&dyn Topic, CallError> {
        let key = name.to_ascii_uppercase();

        if let Some(topic) = self.0.get(&key) {
            return Ok(topic.as_ref());
        }

        match self.0.get_raw_descendant(&key) {
            Some(subtrie) => {
                let children: Vec<(&String, &Box<dyn Topic>)> = subtrie.iter().collect();
                match children[..] {
                    [(_name, topic)] => Ok(topic.as_ref()),
                    _ => {
                        let completions: Vec<String> =
                            children.iter().map(|(name, _topic)| (*name).to_owned()).collect();
                        Err(CallError::ArgumentError(
                            pos,
                            format!(
                                "Ambiguous help topic {}; candidates are: {}",
                                name,
                                completions.join(", ")
                            ),
                        ))
                    }
                }
            }
            None => Err(CallError::ArgumentError(pos, format!("Unknown help topic {}", name))),
        }
    }

    /// Returns an iterator over all the topics.
    fn values(&self) -> radix_trie::iter::Values<String, Box<dyn Topic>> {
        self.0.values()
    }
}

/// The `HELP` command.
pub struct HelpCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl HelpCommand {
    /// Creates a new command that writes help messages to `output`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("HELP", VarType::Void)
                .with_syntax(&[
                    (&[], None),
                    (
                        &[SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax { name: "topic", vtype: ExprType::Text },
                            ArgSepSyntax::End,
                        )],
                        None,
                    ),
                ])
                .with_category(CATEGORY)
                .with_description(
                    "Prints interactive help.
Without arguments, shows a summary of all available top-level help topics.
With a single argument, which must be a string, shows detailed information about the given help \
topic, command, or function.
Topic names are case-insensitive and can be specified as prefixes, in which case the topic whose \
name starts with the prefix will be shown.  For example, the following invocations are all \
equivalent: HELP \"CON\", HELP \"console\", HELP \"Console manipulation\".",
                )
                .build(),
            console,
        })
    }

    /// Prints a summary of all available help topics.
    fn summary(&self, topics: &Topics, console: &mut dyn Console) -> io::Result<()> {
        for line in header() {
            refill_and_print(&mut *console, [&line], "")?;
        }

        let previous = console.color();

        console.print("")?;
        console.set_color(Some(TITLE_COLOR), previous.1)?;
        refill_and_print(&mut *console, ["Top-level help topics"], "    ")?;
        console.set_color(previous.0, previous.1)?;
        console.print("")?;
        for topic in topics.values() {
            if topic.show_in_summary() {
                // TODO(jmmv): Should use refill_and_print but continuation lines need special
                // handling to be indented properly.
                console.write("    >> ")?;
                console.set_color(Some(LINK_COLOR), previous.1)?;
                console.print(topic.title())?;
                console.set_color(previous.0, previous.1)?;
            }
        }
        console.print("")?;
        refill_and_print(
            &mut *console,
            ["Type HELP followed by the name of a topic for details."],
            "    ",
        )?;
        refill_and_print(
            &mut *console,
            ["Type HELP \"HELP\" for details on how to specify topic names."],
            "    ",
        )?;
        refill_and_print(
            &mut *console,
            [r#"Type LOAD "DEMOS:/TOUR.BAS": RUN for a guided tour."#],
            "    ",
        )?;
        refill_and_print(&mut *console, [r#"Type END or press CTRL+D to exit."#], "    ")?;
        console.print("")?;

        Ok(())
    }
}

#[async_trait(?Send)]
impl Callable for HelpCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, mut scope: Scope<'_>, machine: &mut Machine) -> CallResult {
        let topics = Topics::new(machine.get_symbols());

        if scope.nargs() == 0 {
            let mut console = self.console.borrow_mut();
            let previous = console.set_sync(false)?;
            let result = self.summary(&topics, &mut *console);
            console.set_sync(previous)?;
            result?;
        } else {
            debug_assert_eq!(1, scope.nargs());
            let (t, pos) = scope.pop_string_with_pos();

            let topic = topics.find(&t, pos)?;
            let mut console = self.console.borrow_mut();
            let previous = console.set_sync(false)?;
            let result = topic.describe(&mut *console);
            console.set_sync(previous)?;
            result?;
        }

        Ok(Value::Void)
    }
}

/// Adds all help-related commands to the `machine` and makes them write to `console`.
pub fn add_all(machine: &mut Machine, console: Rc<RefCell<dyn Console>>) {
    machine.add_callable(HelpCommand::new(console));
}

#[cfg(test)]
pub(crate) mod testutils {
    use super::*;
    use endbasic_core::ast::Value;
    use endbasic_core::syms::{CallResult, Callable, CallableMetadata, CallableMetadataBuilder};

    /// A command that does nothing.
    pub(crate) struct DoNothingCommand {
        metadata: CallableMetadata,
    }

    impl DoNothingCommand {
        /// Creates a new instance of the command with the name `DO_NOTHING`.
        pub(crate) fn new() -> Rc<Self> {
            DoNothingCommand::new_with_name("DO_NOTHING")
        }

        /// Creates a new instance of the command with a given `name`.
        pub fn new_with_name(name: &'static str) -> Rc<Self> {
            Rc::from(Self {
                metadata: CallableMetadataBuilder::new(name, VarType::Void)
                    .with_syntax(&[(
                        &[SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax { name: "sample", vtype: ExprType::Text },
                            ArgSepSyntax::End,
                        )],
                        None,
                    )])
                    .with_category(
                        "Testing
This is a sample category for testing.",
                    )
                    .with_description(
                        "This is the blurb.
First paragraph of the extended description.
Second paragraph of the extended description.",
                    )
                    .build(),
            })
        }
    }

    #[async_trait(?Send)]
    impl Callable for DoNothingCommand {
        fn metadata(&self) -> &CallableMetadata {
            &self.metadata
        }

        async fn exec(&self, _scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
            Ok(Value::Void)
        }
    }

    /// A function that does nothing that can take any name.
    pub(crate) struct EmptyFunction {
        metadata: CallableMetadata,
    }

    impl EmptyFunction {
        /// Creates a new instance of the function with the name `EMPTY`.
        pub(crate) fn new() -> Rc<Self> {
            EmptyFunction::new_with_name("EMPTY")
        }

        /// Creates a new instance of the function with a given `name`.
        pub(crate) fn new_with_name(name: &'static str) -> Rc<Self> {
            Rc::from(Self {
                metadata: CallableMetadataBuilder::new(name, VarType::Text)
                    .with_syntax(&[(
                        &[SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax { name: "sample", vtype: ExprType::Text },
                            ArgSepSyntax::End,
                        )],
                        None,
                    )])
                    .with_category(
                        "Testing
This is a sample category for testing.",
                    )
                    .with_description(
                        "This is the blurb.
First paragraph of the extended description.
Second paragraph of the extended description.",
                    )
                    .build(),
            })
        }
    }

    #[async_trait(?Send)]
    impl Callable for EmptyFunction {
        fn metadata(&self) -> &CallableMetadata {
            &self.metadata
        }

        async fn exec(&self, _scope: Scope<'_>, _machine: &mut Machine) -> CallResult {
            Ok(Value::Text("irrelevant".to_owned()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::testutils::*;
    use super::*;
    use crate::testutils::*;

    #[test]
    fn test_parse_lang_reference_empty() {
        let content = parse_lang_reference("");
        assert!(content.is_empty());
    }

    #[test]
    fn test_parse_lang_reference_junk_only() {
        let content = parse_lang_reference(
            "# foo
# bar
baz",
        );
        assert!(content.is_empty());
    }

    #[test]
    fn test_parse_lang_reference_one() {
        let content = parse_lang_reference(
            "

# First

This is the first and only topic with
a couple of lines.
",
        );
        let exp_content =
            vec![("First", "This is the first and only topic with\na couple of lines.")];
        assert_eq!(exp_content, content);
    }

    #[test]
    fn test_parse_lang_reference_many() {
        let content = parse_lang_reference(
            "

# First

This is the first topic with
a couple of lines.

# Second

This is the second topic with just one line.

# Third

And this is the last one without EOF.",
        );
        let exp_content = vec![
            ("First", "This is the first topic with\na couple of lines."),
            ("Second", "This is the second topic with just one line."),
            ("Third", "And this is the last one without EOF."),
        ];
        assert_eq!(exp_content, content);
    }

    #[test]
    fn test_parse_lang_reference_ignore_header() {
        let content = parse_lang_reference(
            "This should be ignored.
And this.
#And also this.

# First

This is the first and only topic with just one line.
",
        );
        let exp_content = vec![("First", "This is the first and only topic with just one line.")];
        assert_eq!(exp_content, content);
    }

    fn tester() -> Tester {
        let tester = Tester::empty();
        let console = tester.get_console();
        tester.add_callable(HelpCommand::new(console))
    }

    #[test]
    fn test_help_summarize_symbols() {
        let mut t =
            tester().add_callable(DoNothingCommand::new()).add_callable(EmptyFunction::new());
        t.get_console().borrow_mut().set_color(Some(100), Some(200)).unwrap();
        t.run("HELP")
            .expect_output([
                CapturedOut::SetColor(Some(100), Some(200)),
                CapturedOut::SetSync(false),
            ])
            .expect_prints(header())
            .expect_prints([""])
            .expect_output([
                CapturedOut::SetColor(Some(TITLE_COLOR), Some(200)),
                CapturedOut::Print("    Top-level help topics".to_owned()),
                CapturedOut::SetColor(Some(100), Some(200)),
            ])
            .expect_prints([""])
            .expect_output([
                CapturedOut::Write("    >> ".to_owned()),
                CapturedOut::SetColor(Some(LINK_COLOR), Some(200)),
                CapturedOut::Print("Interpreter".to_owned()),
                CapturedOut::SetColor(Some(100), Some(200)),
            ])
            .expect_output([
                CapturedOut::Write("    >> ".to_owned()),
                CapturedOut::SetColor(Some(LINK_COLOR), Some(200)),
                CapturedOut::Print("Language reference".to_owned()),
                CapturedOut::SetColor(Some(100), Some(200)),
            ])
            .expect_output([
                CapturedOut::Write("    >> ".to_owned()),
                CapturedOut::SetColor(Some(LINK_COLOR), Some(200)),
                CapturedOut::Print("Testing".to_owned()),
                CapturedOut::SetColor(Some(100), Some(200)),
            ])
            .expect_prints([
                "",
                "    Type HELP followed by the name of a topic for details.",
                "    Type HELP \"HELP\" for details on how to specify topic names.",
                "    Type LOAD \"DEMOS:/TOUR.BAS\": RUN for a guided tour.",
                "    Type END or press CTRL+D to exit.",
                "",
            ])
            .expect_output([CapturedOut::SetSync(true)])
            .check();
    }

    #[test]
    fn test_help_describe_callables_topic() {
        let mut t =
            tester().add_callable(DoNothingCommand::new()).add_callable(EmptyFunction::new());
        t.get_console().borrow_mut().set_color(Some(70), Some(50)).unwrap();
        t.run(r#"help "testing""#)
            .expect_output([CapturedOut::SetColor(Some(70), Some(50)), CapturedOut::SetSync(false)])
            .expect_prints([""])
            .expect_output([
                CapturedOut::SetColor(Some(TITLE_COLOR), Some(50)),
                CapturedOut::Print("    Testing".to_owned()),
                CapturedOut::SetColor(Some(70), Some(50)),
            ])
            .expect_prints(["", "    This is a sample category for testing.", ""])
            .expect_output([
                CapturedOut::Write("    >> ".to_owned()),
                CapturedOut::SetColor(Some(LINK_COLOR), Some(50)),
                CapturedOut::Write("DO_NOTHING".to_owned()),
                CapturedOut::SetColor(Some(70), Some(50)),
                CapturedOut::Print("    This is the blurb.".to_owned()),
            ])
            .expect_output([
                CapturedOut::Write("    >> ".to_owned()),
                CapturedOut::SetColor(Some(LINK_COLOR), Some(50)),
                CapturedOut::Write("EMPTY$    ".to_owned()),
                CapturedOut::SetColor(Some(70), Some(50)),
                CapturedOut::Print("    This is the blurb.".to_owned()),
            ])
            .expect_prints(["", "    Type HELP followed by the name of a topic for details.", ""])
            .expect_output([CapturedOut::SetSync(true)])
            .check();
    }

    #[test]
    fn test_help_describe_command() {
        let mut t = tester().add_callable(DoNothingCommand::new());
        t.get_console().borrow_mut().set_color(Some(20), Some(21)).unwrap();
        t.run(r#"help "Do_Nothing""#)
            .expect_output([CapturedOut::SetColor(Some(20), Some(21)), CapturedOut::SetSync(false)])
            .expect_prints([""])
            .expect_output([
                CapturedOut::SetColor(Some(TITLE_COLOR), Some(21)),
                CapturedOut::Print("    DO_NOTHING sample$".to_owned()),
                CapturedOut::SetColor(Some(20), Some(21)),
            ])
            .expect_prints([
                "",
                "    This is the blurb.",
                "",
                "    First paragraph of the extended description.",
                "",
                "    Second paragraph of the extended description.",
                "",
            ])
            .expect_output([CapturedOut::SetSync(true)])
            .check();
    }

    fn do_help_describe_function_test(name: &str) {
        let mut t = tester().add_callable(EmptyFunction::new());
        t.get_console().borrow_mut().set_color(Some(30), Some(26)).unwrap();
        t.run(format!(r#"help "{}""#, name))
            .expect_output([CapturedOut::SetColor(Some(30), Some(26)), CapturedOut::SetSync(false)])
            .expect_prints([""])
            .expect_output([
                CapturedOut::SetColor(Some(TITLE_COLOR), Some(26)),
                CapturedOut::Print("    EMPTY$(sample$)".to_owned()),
                CapturedOut::SetColor(Some(30), Some(26)),
            ])
            .expect_prints([
                "",
                "    This is the blurb.",
                "",
                "    First paragraph of the extended description.",
                "",
                "    Second paragraph of the extended description.",
                "",
            ])
            .expect_output([CapturedOut::SetSync(true)])
            .check();
    }

    #[test]
    fn test_help_describe_function_without_annotation() {
        do_help_describe_function_test("Empty")
    }

    #[test]
    fn test_help_describe_function_with_annotation() {
        do_help_describe_function_test("EMPTY$")
    }

    #[test]
    fn test_help_eval_arg() {
        tester()
            .add_callable(DoNothingCommand::new())
            .run(r#"topic = "Do_Nothing": HELP topic"#)
            .expect_output([CapturedOut::SetSync(false)])
            .expect_prints([""])
            .expect_output([
                CapturedOut::SetColor(Some(TITLE_COLOR), None),
                CapturedOut::Print("    DO_NOTHING sample$".to_owned()),
                CapturedOut::SetColor(None, None),
            ])
            .expect_prints([
                "",
                "    This is the blurb.",
                "",
                "    First paragraph of the extended description.",
                "",
                "    Second paragraph of the extended description.",
                "",
            ])
            .expect_var("TOPIC", "Do_Nothing")
            .expect_output([CapturedOut::SetSync(true)])
            .check();
    }

    #[test]
    fn test_help_prefix_search() {
        fn exp_output(name: &str, is_function: bool) -> Vec<CapturedOut> {
            let spec = if is_function {
                format!("    {}(sample$)", name)
            } else {
                format!("    {} sample$", name)
            };
            vec![
                CapturedOut::SetSync(false),
                CapturedOut::Print("".to_owned()),
                CapturedOut::SetColor(Some(TITLE_COLOR), None),
                CapturedOut::Print(spec),
                CapturedOut::SetColor(None, None),
                CapturedOut::Print("".to_owned()),
                CapturedOut::Print("    This is the blurb.".to_owned()),
                CapturedOut::Print("".to_owned()),
                CapturedOut::Print("    First paragraph of the extended description.".to_owned()),
                CapturedOut::Print("".to_owned()),
                CapturedOut::Print("    Second paragraph of the extended description.".to_owned()),
                CapturedOut::Print("".to_owned()),
                CapturedOut::SetSync(true),
            ]
        }

        for cmd in &[r#"help "aa""#, r#"help "aab""#, r#"help "aabc""#] {
            tester()
                .add_callable(EmptyFunction::new_with_name("AABC"))
                .add_callable(EmptyFunction::new_with_name("ABC"))
                .add_callable(EmptyFunction::new_with_name("BC"))
                .run(*cmd)
                .expect_output(exp_output("AABC$", true))
                .check();
        }

        for cmd in &[r#"help "b""#, r#"help "bc""#] {
            tester()
                .add_callable(EmptyFunction::new_with_name("AABC"))
                .add_callable(EmptyFunction::new_with_name("ABC"))
                .add_callable(EmptyFunction::new_with_name("BC"))
                .run(*cmd)
                .expect_output(exp_output("BC$", true))
                .check();
        }

        tester()
            .add_callable(DoNothingCommand::new_with_name("AAAB"))
            .add_callable(DoNothingCommand::new_with_name("AAAA"))
            .add_callable(DoNothingCommand::new_with_name("AAAAA"))
            .run(r#"help "aaaa""#)
            .expect_output(exp_output("AAAA", false))
            .check();

        tester()
            .add_callable(DoNothingCommand::new_with_name("ZAB"))
            .add_callable(EmptyFunction::new_with_name("ZABC"))
            .add_callable(EmptyFunction::new_with_name("ZAABC"))
            .run(r#"help "za""#)
            .expect_err("1:1: In call to HELP: 1:6: Ambiguous help topic za; candidates are: ZAABC$, ZAB, ZABC$")
            .check();
    }

    #[test]
    fn test_help_errors() {
        let mut t =
            tester().add_callable(DoNothingCommand::new()).add_callable(EmptyFunction::new());

        t.run(r#"HELP foo bar"#)
            .expect_uncatchable_err("1:10: Unexpected value in expression")
            .check();
        t.run(r#"HELP foo"#)
            .expect_compilation_err("1:1: In call to HELP: 1:6: Undefined variable foo")
            .check();

        t.run(r#"HELP "foo", 3"#)
            .expect_compilation_err("1:1: In call to HELP: expected <> | <topic$>")
            .check();
        t.run(r#"HELP 3"#)
            .expect_compilation_err("1:1: In call to HELP: 1:6: INTEGER is not a STRING")
            .check();

        t.run(r#"HELP "lang%""#)
            .expect_err("1:1: In call to HELP: 1:6: Unknown help topic lang%")
            .check();

        t.run(r#"HELP "foo$""#)
            .expect_err("1:1: In call to HELP: 1:6: Unknown help topic foo$")
            .check();
        t.run(r#"HELP "foo""#)
            .expect_err("1:1: In call to HELP: 1:6: Unknown help topic foo")
            .check();

        t.run(r#"HELP "do_nothing$""#)
            .expect_err("1:1: In call to HELP: 1:6: Unknown help topic do_nothing$")
            .check();
        t.run(r#"HELP "empty?""#)
            .expect_err("1:1: In call to HELP: 1:6: Unknown help topic empty?")
            .check();

        t.run(r#"topic = "foo$": HELP topic$"#)
            .expect_err("1:17: In call to HELP: 1:22: Unknown help topic foo$")
            .expect_var("topic", "foo$")
            .check();

        let mut t = tester();
        t.run(r#"HELP "undoc""#)
            .expect_err("1:1: In call to HELP: 1:6: Unknown help topic undoc")
            .check();
        t.run(r#"undoc = 3: HELP "undoc""#)
            .expect_err("1:12: In call to HELP: 1:17: Unknown help topic undoc")
            .expect_var("undoc", 3)
            .check();

        let mut t = tester();
        t.run(r#"HELP "undoc""#)
            .expect_err("1:1: In call to HELP: 1:6: Unknown help topic undoc")
            .check();
        t.run(r#"DIM undoc(3): HELP "undoc""#)
            .expect_err("1:15: In call to HELP: 1:20: Unknown help topic undoc")
            .expect_array("undoc", VarType::Integer, &[3], vec![])
            .check();
    }
}
