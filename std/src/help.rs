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
use std::cell::RefCell;
use std::collections::BTreeMap;
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

/// Builds the index of symbols needed to print the summary.
///
/// The return value is the index in the form of a (category name -> (name, blurb)) mapping,
/// followed by the length of the longest command name that was found.
fn build_index(
    symbols: &Symbols,
) -> (BTreeMap<&'static str, BTreeMap<String, &'static str>>, usize) {
    let mut index = BTreeMap::default();
    let mut max_length = 0;
    for symbol in symbols.as_hashmap().values() {
        if let Some(metadata) = symbol.metadata() {
            let name = format!("{}{}", metadata.name(), metadata.return_type().annotation());
            if name.len() > max_length {
                max_length = name.len();
            }
            let blurb = metadata.description().next().unwrap();
            index.entry(metadata.category()).or_insert_with(BTreeMap::default).insert(name, blurb);
        }
    }
    (index, max_length)
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
Without arguments, shows a summary of all available help topics.
With a single argument, shows detailed information about the given help topic, command, or \
function.",
                )
                .build(),
            console,
        })
    }

    /// Prints a summary of all available help topics.
    fn summary(&self, symbols: &Symbols) -> io::Result<()> {
        let (index, max_length) = build_index(symbols);

        let mut console = self.console.borrow_mut();
        for line in header() {
            console.print(&line)?;
        }

        for (category, by_name) in index.iter() {
            console.print("")?;
            console.print(&format!("    >> {} <<", category))?;
            for (name, blurb) in by_name.iter() {
                let filler = " ".repeat(max_length - name.len());
                console.print(&format!("    {}{}    {}", name, filler, blurb))?;
            }
        }

        console.print("")?;
        console.print("    Type HELP followed by a command or function name for details.")?;
        console.print("    Type HELP LANG for a quick reference guide about the language.")?;
        console.print("")?;
        Ok(())
    }

    /// Describes one command or function.
    fn describe_callable(&self, metadata: &CallableMetadata) -> io::Result<()> {
        let mut console = self.console.borrow_mut();
        console.print("")?;
        if metadata.return_type() == VarType::Void {
            if metadata.syntax().is_empty() {
                console.print(&format!("    {}", metadata.name()))?
            } else {
                console.print(&format!("    {} {}", metadata.name(), metadata.syntax()))?
            }
        } else {
            console.print(&format!(
                "    {}{}({})",
                metadata.name(),
                metadata.return_type().annotation(),
                metadata.syntax(),
            ))?;
        }
        for line in metadata.description() {
            console.print("")?;
            console.print(&format!("    {}", line))?;
        }
        console.print("")?;
        Ok(())
    }

    /// Prints a quick reference of the language syntax.
    fn describe_lang(&self) -> io::Result<()> {
        let mut console = self.console.borrow_mut();
        for line in LANG_REFERENCE.lines() {
            // Print line by line to honor any possible differences in line feeds.
            console.print(line)?;
        }
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
        match args {
            [] => self.summary(machine.get_symbols())?,
            [(Some(Expr::Symbol(vref)), ArgSep::End)] => {
                let name = vref.name().to_ascii_uppercase();
                if name == "LANG" {
                    if vref.ref_type() != VarType::Auto {
                        return Err(CallError::ArgumentError(
                            "Incompatible type annotation".to_owned(),
                        ));
                    }
                    self.describe_lang()?;
                } else {
                    match machine.get_symbols().get(vref)? {
                        Some(symbol) => match symbol.metadata() {
                            Some(metadata) => self.describe_callable(metadata)?,
                            None => {
                                return Err(CallError::ArgumentError(format!(
                                    "No help available for {}",
                                    name
                                )))
                            }
                        },
                        None => {
                            return Err(CallError::ArgumentError(format!(
                                "Cannot describe unknown command or function {}",
                                name
                            )))
                        }
                    }
                }
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

    /// A function that does nothing.
    pub(crate) struct EmptyFunction {
        metadata: CallableMetadata,
    }

    impl EmptyFunction {
        pub(crate) fn new() -> Rc<Self> {
            Rc::from(Self {
                metadata: CallableMetadataBuilder::new("EMPTY", VarType::Text)
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

    fn tester() -> Tester {
        let tester = Tester::from(Machine::default());
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
                "    >> Interpreter manipulation <<",
                "    HELP          Prints interactive help.",
                "",
                "    >> Testing <<",
                "    DO_NOTHING    This is the blurb.",
                "    EMPTY$        This is the blurb.",
                "",
                "    Type HELP followed by a command or function name for details.",
                "    Type HELP LANG for a quick reference guide about the language.",
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
        tester()
            .run("help lang")
            .expect_prints(LANG_REFERENCE.lines().collect::<Vec<&str>>())
            .expect_prints([""])
            .check();
    }

    #[test]
    fn test_help_errors() {
        let mut t =
            tester().add_command(DoNothingCommand::new()).add_function(EmptyFunction::new());

        t.run("HELP foo bar").expect_err("Unexpected value in expression").check();
        t.run("HELP foo, bar").expect_err("HELP takes zero or only one argument").check();

        t.run("HELP lang%").expect_err("Incompatible type annotation").check();

        t.run("HELP foo$").expect_err("Cannot describe unknown command or function FOO").check();
        t.run("HELP foo").expect_err("Cannot describe unknown command or function FOO").check();

        t.run("HELP do_nothing$").expect_err("Incompatible types in do_nothing$ reference").check();
        t.run("HELP empty?").expect_err("Incompatible types in empty? reference").check();

        let mut t = tester();
        t.run("HELP undoc").expect_err("Cannot describe unknown command or function UNDOC").check();
        t.run("undoc = 3: HELP undoc")
            .expect_err("No help available for UNDOC")
            .expect_var("undoc", 3)
            .check();

        let mut t = tester();
        t.run("HELP undoc").expect_err("Cannot describe unknown command or function UNDOC").check();
        t.run("DIM undoc(3): HELP undoc")
            .expect_err("No help available for UNDOC")
            .expect_array("undoc", VarType::Integer, &[3])
            .check();
    }
}
