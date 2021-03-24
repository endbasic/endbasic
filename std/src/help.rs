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

use crate::console::Console;
use async_trait::async_trait;
use endbasic_core::ast::{ArgSep, Expr, VarType};
use endbasic_core::exec::Machine;
use endbasic_core::syms::{
    CallError, CallableMetadata, CallableMetadataBuilder, Command, CommandResult, Symbols,
};
use radix_trie::{Trie, TrieCommon};
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::io;
use std::rc::Rc;

/// Cheat-sheet for the language syntax.
const LANG_REFERENCE: &str = r"
    Symbols (variable, array and function references):
        name?    Boolean (TRUE and FALSE).
        name#    Floating point (double).
        name%    Integer (32 bits).
        name$    String.
        name     Type determined by value or definition.

    Assignments and declarations:
        varref[(dim1[, ..., dimN])] = expr
        DIM varname[(dim1[, ..., dimN])] [AS BOOLEAN|DOUBLE|INTEGER|STRING]

    Expressions:
        a + b      a - b       a * b     a / b      a MOD b    -a
        a AND b    NOT a       a OR b    a XOR b
        a = b      a <> b      a < b     a <= b     a > b      a >= b
        (a)        varref
        arrayref(s1[, ..., sN])          funcref(a1[, ..., aN])

    Flow control:
        IF expr THEN: ...: ELSE IF expr THEN: ...: ELSE: ...: END IF
        FOR varref = expr TO expr [STEP int]: ...: NEXT
        WHILE expr: ...: WEND

    Misc:
        st1: st2    Separates statements (same as a newline).
        REM text    Comment until end of line.
        ' text      Comment until end of line.
        ,           Long separator for arguments to builtin call.
        ;           Short separator for arguments to builtin call.
";

/// Returns the header for the help summary.
fn header() -> Vec<String> {
    vec![
        "".to_owned(),
        format!("    EndBASIC {}", env!("CARGO_PKG_VERSION")),
        "    Copyright 2020-2021 Julio Merino".to_owned(),
        "".to_owned(),
        format!("    Project page at <{}>", env!("CARGO_PKG_HOMEPAGE")),
        "    License Apache Version 2.0 <http://www.apache.org/licenses/LICENSE-2.0>".to_owned(),
    ]
}

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
                if first == first.to_ascii_uppercase() {
                    2
                } else {
                    1
                }
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

/// Same as `refill` but prints the lines to the console instead of returning them.
///
/// The width is automatically determined from the console's size.
fn refill_and_print(console: &mut dyn Console, paragraph: &str) -> io::Result<()> {
    // TODO(jmmv): This queries the size on every print, which is not very efficient.  Should reuse
    // this across calls, maybe by having a wrapper over Console and using it throughout.
    let size = console.size()?;
    let lines = refill(paragraph, size.column - 8);
    for line in lines {
        if line.is_empty() {
            console.print("")?;
        } else {
            console.print(&format!("    {}", line))?;
        }
    }
    Ok(())
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
        if self.metadata.return_type() == VarType::Void {
            if self.metadata.syntax().is_empty() {
                refill_and_print(console, self.metadata.name())?
            } else {
                refill_and_print(
                    console,
                    &format!("{} {}", self.metadata.name(), self.metadata.syntax()),
                )?
            }
        } else {
            refill_and_print(
                console,
                &format!(
                    "{}{}({})",
                    self.metadata.name(),
                    self.metadata.return_type().annotation(),
                    self.metadata.syntax(),
                ),
            )?;
        }
        for paragraph in self.metadata.description() {
            console.print("")?;
            refill_and_print(console, paragraph)?;
        }
        console.print("")?;
        Ok(())
    }
}

/// A help topic to describe a category of callables.
struct CategoryTopic {
    name: &'static str,
    metadatas: Vec<CallableMetadata>,
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
        let mut index = BTreeMap::default();
        let mut max_length = 0;
        for metadata in &self.metadatas {
            let name = format!("{}{}", metadata.name(), metadata.return_type().annotation());
            if name.len() > max_length {
                max_length = name.len();
            }
            let blurb = metadata.description().next().unwrap();
            let previous = index.insert(name, blurb);
            assert!(previous.is_none(), "Names should have been unique");
        }

        // TODO(jmmv): Should use refill_and_print but continuation lines need special handling to
        // be indented properly.
        console.print("")?;
        console.print(&format!("    {}", self.name))?;
        console.print("")?;
        for (name, blurb) in index.iter() {
            let filler = " ".repeat(max_length - name.len());
            console.print(&format!("    >> {}{}    {}", name, filler, blurb))?;
        }
        console.print("")?;
        refill_and_print(console, "    Type HELP followed by the name of a symbol for details.")?;
        console.print("")?;
        Ok(())
    }
}

/// A help topic to describe the language's grammar.
struct LanguageTopic {}

impl Topic for LanguageTopic {
    fn name(&self) -> &str {
        "Language reference"
    }

    fn title(&self) -> &str {
        "Language reference"
    }

    fn show_in_summary(&self) -> bool {
        true
    }

    fn describe(&self, console: &mut dyn Console) -> io::Result<()> {
        for line in LANG_REFERENCE.lines() {
            // Print line by line to honor any possible differences in line feeds.
            console.print(line)?;
        }
        console.print("")?;
        Ok(())
    }
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

        insert(&mut topics, Box::from(LanguageTopic {}));

        let mut categories = HashMap::new();
        for (name, symbol) in symbols.as_hashmap().iter() {
            if let Some(metadata) = symbol.metadata() {
                categories
                    .entry(metadata.category())
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
            insert(&mut topics, Box::from(CategoryTopic { name, metadatas }));
        }

        Self(topics)
    }

    /// Returns the given topic named `name`, where `name` can be a prefix.
    ///
    /// If `name` is not long enough to uniquely identify a topic or if the topic does not exist,
    /// returns an error.
    fn find(&self, name: &str) -> Result<&dyn Topic, CallError> {
        let key = name.to_ascii_uppercase();

        match self.0.get_raw_descendant(&key) {
            Some(subtrie) => {
                let children: Vec<(&String, &Box<dyn Topic>)> = subtrie.iter().collect();
                match children[..] {
                    [(_name, topic)] => Ok(topic.as_ref()),
                    _ => {
                        let completions: Vec<String> =
                            children.iter().map(|(name, _topic)| (*name).to_owned()).collect();
                        Err(CallError::ArgumentError(format!(
                            "Ambiguous help topic {}; candidates are: {}",
                            name,
                            completions.join(", ")
                        )))
                    }
                }
            }
            None => Err(CallError::ArgumentError(format!("Unknown help topic {}", name))),
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
                .with_syntax("[topic]")
                .with_category("Interpreter manipulation")
                .with_description(
                    "Prints interactive help.
Without arguments, shows a summary of all available top-level help topics.
With a single argument, which may be a bare name or a string, shows detailed information about the \
given help topic, command, or function. Topic names with spaces in them must be double-quoted.
Topic names are case-insensitive and can be specified as prefixes, in which case the topic whose \
name starts with the prefix will be shown. For example, the following invocations are all \
equivalent: HELP CON, HELP console, HELP \"Console manipulation\".",
                )
                .build(),
            console,
        })
    }

    /// Prints a summary of all available help topics.
    fn summary(&self, topics: &Topics) -> io::Result<()> {
        let mut console = self.console.borrow_mut();
        for line in header() {
            refill_and_print(&mut *console, &line)?;
        }

        // TODO(jmmv): Should use refill_and_print but continuation lines need special handling to
        // be indented properly.
        console.print("")?;
        refill_and_print(&mut *console, "Top-level help topics:")?;
        console.print("")?;
        for topic in topics.values() {
            if topic.show_in_summary() {
                console.print(&format!("    >> {}", topic.title()))?;
            }
        }
        console.print("")?;
        refill_and_print(&mut *console, "Type HELP followed by the name of a topic for details.")?;
        refill_and_print(
            &mut *console,
            "Type HELP HELP for details on how to specify topic names.",
        )?;
        console.print("")?;

        Ok(())
    }
}

#[async_trait(?Send)]
impl Command for HelpCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        let topics = Topics::new(machine.get_symbols());

        match args {
            [] => {
                self.summary(&topics)?;
            }
            [(Some(Expr::Symbol(vref)), ArgSep::End)] => {
                let topic = topics.find(&format!("{}", vref))?;
                let mut console = self.console.borrow_mut();
                topic.describe(&mut *console)?;
            }
            [(Some(Expr::Text(name)), ArgSep::End)] => {
                let topic = topics.find(name)?;
                let mut console = self.console.borrow_mut();
                topic.describe(&mut *console)?;
            }
            _ => {
                return Err(CallError::ArgumentError(
                    "HELP takes zero or only one argument".to_owned(),
                ))
            }
        }
        Ok(())
    }
}

/// Adds all help-related commands to the `machine` and makes them write to `console`.
pub fn add_all(machine: &mut Machine, console: Rc<RefCell<dyn Console>>) {
    machine.add_command(HelpCommand::new(console));
}

#[cfg(test)]
pub(crate) mod testutils {
    use super::*;
    use endbasic_core::ast::Value;
    use endbasic_core::syms::{
        CallableMetadata, CallableMetadataBuilder, Function, FunctionResult,
    };

    /// A command that does nothing.
    pub(crate) struct DoNothingCommand {
        metadata: CallableMetadata,
    }

    impl DoNothingCommand {
        /// Creates a new instance of the command.
        pub fn new() -> Rc<Self> {
            Rc::from(Self {
                metadata: CallableMetadataBuilder::new("DO_NOTHING", VarType::Void)
                    .with_syntax("this [would] <be|the> syntax \"specification\"")
                    .with_category("Testing")
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
    impl Command for DoNothingCommand {
        fn metadata(&self) -> &CallableMetadata {
            &self.metadata
        }

        async fn exec(
            &self,
            _args: &[(Option<Expr>, ArgSep)],
            _machine: &mut Machine,
        ) -> CommandResult {
            Ok(())
        }
    }

    /// A function that does nothing that can take any name.
    pub(crate) struct EmptyFunction {
        metadata: CallableMetadata,
    }

    impl EmptyFunction {
        pub(crate) fn new() -> Rc<Self> {
            EmptyFunction::new_with_name("EMPTY")
        }

        pub(crate) fn new_with_name(name: &'static str) -> Rc<Self> {
            Rc::from(Self {
                metadata: CallableMetadataBuilder::new(name, VarType::Text)
                    .with_syntax("this [would] <be|the> syntax \"specification\"")
                    .with_category("Testing")
                    .with_description(
                        "This is the blurb.
First paragraph of the extended description.
Second paragraph of the extended description.",
                    )
                    .build(),
            })
        }
    }

    impl Function for EmptyFunction {
        fn metadata(&self) -> &CallableMetadata {
            &self.metadata
        }

        fn exec(&self, _args: Vec<Value>, _symbols: &mut Symbols) -> FunctionResult {
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

    fn tester() -> Tester {
        let tester = Tester::empty();
        let console = tester.get_console();
        tester.add_command(HelpCommand::new(console))
    }

    #[test]
    fn test_help_summarize_symbols() {
        tester()
            .add_command(DoNothingCommand::new())
            .add_function(EmptyFunction::new())
            .run("HELP")
            .expect_prints(header())
            .expect_prints([
                "",
                "    Top-level help topics:",
                "",
                "    >> Interpreter manipulation",
                "    >> Language reference",
                "    >> Testing",
                "",
                "    Type HELP followed by the name of a topic for details.",
                "    Type HELP HELP for details on how to specify topic names.",
                "",
            ])
            .check();
    }

    #[test]
    fn test_help_describe_callables_topic() {
        tester()
            .add_command(DoNothingCommand::new())
            .add_function(EmptyFunction::new())
            .run("help testing")
            .expect_prints([
                "",
                "    Testing",
                "",
                "    >> DO_NOTHING    This is the blurb.",
                "    >> EMPTY$        This is the blurb.",
                "",
                "    Type HELP followed by the name of a symbol for details.",
                "",
            ])
            .check();
    }

    #[test]
    fn test_help_describe_command() {
        tester()
            .add_command(DoNothingCommand::new())
            .run("help Do_Nothing")
            .expect_prints([
                "",
                "    DO_NOTHING this [would] <be|the> syntax \"specification\"",
                "",
                "    This is the blurb.",
                "",
                "    First paragraph of the extended description.",
                "",
                "    Second paragraph of the extended description.",
                "",
            ])
            .check();
    }

    fn do_help_describe_function_test(name: &str) {
        tester()
            .add_function(EmptyFunction::new())
            .run(format!("help {}", name))
            .expect_prints([
                "",
                "    EMPTY$(this [would] <be|the> syntax \"specification\")",
                "",
                "    This is the blurb.",
                "",
                "    First paragraph of the extended description.",
                "",
                "    Second paragraph of the extended description.",
                "",
            ])
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
    fn test_help_lang() {
        for cmd in &["help lang", "help language", r#"help "Language Reference""#] {
            tester()
                .run(*cmd)
                .expect_prints(LANG_REFERENCE.lines().collect::<Vec<&str>>())
                .expect_prints([""])
                .check();
        }
    }

    #[test]
    fn test_help_prefix_search() {
        fn exp_output(name: &str) -> Vec<String> {
            vec![
                "".to_owned(),
                format!("    {}$(this [would] <be|the> syntax \"specification\")", name),
                "".to_owned(),
                "    This is the blurb.".to_owned(),
                "".to_owned(),
                "    First paragraph of the extended description.".to_owned(),
                "".to_owned(),
                "    Second paragraph of the extended description.".to_owned(),
                "".to_owned(),
            ]
        }

        for cmd in &["help aa", "help aab", "help aabc"] {
            tester()
                .add_function(EmptyFunction::new_with_name("AABC"))
                .add_function(EmptyFunction::new_with_name("ABC"))
                .add_function(EmptyFunction::new_with_name("BC"))
                .run(*cmd)
                .expect_prints(exp_output("AABC"))
                .check();
        }

        for cmd in &["help b", "help bc"] {
            tester()
                .add_function(EmptyFunction::new_with_name("AABC"))
                .add_function(EmptyFunction::new_with_name("ABC"))
                .add_function(EmptyFunction::new_with_name("BC"))
                .run(*cmd)
                .expect_prints(exp_output("BC"))
                .check();
        }

        tester()
            .add_function(EmptyFunction::new_with_name("ABC"))
            .add_function(EmptyFunction::new_with_name("AABC"))
            .run("help a")
            .expect_err("Ambiguous help topic a; candidates are: AABC$, ABC$")
            .check();
    }

    #[test]
    fn test_help_errors() {
        let mut t =
            tester().add_command(DoNothingCommand::new()).add_function(EmptyFunction::new());

        t.run("HELP foo bar").expect_err("Unexpected value in expression").check();
        t.run("HELP foo, bar").expect_err("HELP takes zero or only one argument").check();

        t.run("HELP lang%").expect_err("Unknown help topic lang%").check();

        t.run("HELP foo$").expect_err("Unknown help topic foo$").check();
        t.run("HELP foo").expect_err("Unknown help topic foo").check();

        t.run("HELP do_nothing$").expect_err("Unknown help topic do_nothing$").check();
        t.run("HELP empty?").expect_err("Unknown help topic empty?").check();

        let mut t = tester();
        t.run("HELP undoc").expect_err("Unknown help topic undoc").check();
        t.run("undoc = 3: HELP undoc")
            .expect_err("Unknown help topic undoc")
            .expect_var("undoc", 3)
            .check();

        let mut t = tester();
        t.run("HELP undoc").expect_err("Unknown help topic undoc").check();
        t.run("DIM undoc(3): HELP undoc")
            .expect_err("Unknown help topic undoc")
            .expect_array("undoc", VarType::Integer, &[3], vec![])
            .check();
    }
}
