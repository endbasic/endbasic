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

use crate::ast::{ArgSep, Expr, VarType};
use crate::console::Console;
use crate::eval::{BuiltinFunction, CallableMetadata, CallableMetadataBuilder};
use crate::exec::{self, BuiltinCommand, Machine};
use async_trait::async_trait;
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::rc::Rc;
use std::str::Lines;

/// Cheat-sheet for the language syntax.
const LANG_REFERENCE: &str = r"
    Symbols (variable and function references):
        name?    Boolean (TRUE and FALSE).
        name%    Integer (32 bits).
        name$    String.
        name     Type determined by value or definition.

    Assignments:
        varref = expr

    Expressions:
        a + b      a - b       a * b     a / b      a MOD b    -a
        a AND b    NOT a       a OR b    a XOR b
        a = b      a <> b      a < b     a <= b     a > b      a >= b
        (a)        varref      funcref(a1[, ..., aN])

    Flow control:
        IF expr THEN: ...: ELSE IF expr THEN: ...: ELSE: ...: END IF
        FOR varref = expr TO expr [STEP int]: ...: NEXT
        WHILE expr: ...: END WHILE

    Misc:
        st1: st2    Separates statements (same as a newline).
        REM text    Comment until end of line.
        ' text      Comment until end of line.
        ,           Long separator for arguments to builtin call.
        ;           Short separator for arguments to builtin call.
";

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
    fn summary(&self) -> exec::Result<()> {
        let mut console = self.console.borrow_mut();
        console.print("")?;
        console.print(&format!("    EndBASIC {}", env!("CARGO_PKG_VERSION")))?;
        console.print("    Copyright 2020 Julio Merino")?;
        console.print("")?;
        console.print(&format!("    Project page at <{}>", env!("CARGO_PKG_HOMEPAGE")))?;
        console
            .print("    License Apache Version 2.0 <http://www.apache.org/licenses/LICENSE-2.0>")?;
        console.print("")?;
        console.print("    >> Help topics <<")?;
        console.print("    COMMANDS     Summary of all builtin commands.")?;
        console.print("    FUNCTIONS    Summary of all builtin functions.")?;
        console.print("    LANG         Language reference guide.")?;
        console.print("")?;
        console
            .print("    Type HELP followed by a topic, command, or function name for details.")?;
        console.print("")?;
        Ok(())
    }

    fn summarize_builtins(
        &self,
        by_category: BTreeMap<&'static str, BTreeMap<String, &'static str>>,
        what: &'static str,
    ) -> exec::Result<()> {
        let mut max_length = 0;
        for by_name in by_category.values() {
            for name in by_name.keys() {
                if name.len() > max_length {
                    max_length = name.len();
                }
            }
        }

        let mut console = self.console.borrow_mut();
        for (category, by_name) in by_category.iter() {
            console.print("")?;
            console.print(&format!("    >> {} <<", category))?;
            for (name, blurb) in by_name.iter() {
                let filler = " ".repeat(max_length - name.len());
                console.print(&format!("    {}{}    {}", name, filler, blurb))?;
            }
        }
        console.print("")?;
        console.print(&format!(
            "    Type HELP followed by a {} name for details on that {}.",
            what, what,
        ))?;
        console.print("")?;
        Ok(())
    }

    /// Prints a summary of all available commands.
    fn summarize_commands(
        &self,
        commands: &HashMap<&'static str, Rc<dyn BuiltinCommand>>,
    ) -> exec::Result<()> {
        let mut by_category: BTreeMap<&'static str, BTreeMap<String, &'static str>> =
            BTreeMap::new();
        for command in commands.values() {
            let metadata = command.metadata();
            let name = metadata.name().to_owned();
            let blurb = metadata.description().next().unwrap();
            by_category
                .entry(metadata.category())
                .or_insert_with(BTreeMap::new)
                .insert(name, blurb);
        }
        self.summarize_builtins(by_category, "command")
    }

    /// Prints a summary of all available functions.
    fn summarize_functions(
        &self,
        functions: &HashMap<&'static str, Rc<dyn BuiltinFunction>>,
    ) -> exec::Result<()> {
        let mut by_category: BTreeMap<&'static str, BTreeMap<String, &'static str>> =
            BTreeMap::new();
        for function in functions.values() {
            let metadata = function.metadata();
            let name = format!("{}{}", metadata.name(), metadata.return_type().annotation());
            let blurb = metadata.description().next().unwrap();
            by_category
                .entry(metadata.category())
                .or_insert_with(BTreeMap::new)
                .insert(name, blurb);
        }
        self.summarize_builtins(by_category, "function")
    }

    /// Describes one command or function.
    fn describe(&self, name: &str, syntax: &str, description: Lines) -> exec::Result<()> {
        let mut console = self.console.borrow_mut();
        console.print("")?;
        console.print(&format!("    {}{}", name, syntax))?;
        for line in description {
            console.print("")?;
            console.print(&format!("    {}", line))?;
        }
        console.print("")?;
        Ok(())
    }

    /// Prints details about a single command.
    fn describe_command(&self, command: &Rc<dyn BuiltinCommand>) -> exec::Result<()> {
        let metadata = command.metadata();
        let syntax = if metadata.syntax().is_empty() {
            "".to_owned()
        } else {
            format!(" {}", metadata.syntax())
        };
        self.describe(metadata.name(), &syntax, metadata.description())
    }

    /// Prints details about a single command.
    fn describe_function(&self, function: &Rc<dyn BuiltinFunction>) -> exec::Result<()> {
        let metadata = function.metadata();
        self.describe(
            &format!("{}{}", metadata.name(), metadata.return_type().annotation()),
            &format!("({})", metadata.syntax()),
            metadata.description(),
        )
    }

    /// Prints a quick reference of the language syntax.
    fn describe_lang(&self) -> exec::Result<()> {
        let mut console = self.console.borrow_mut();
        for line in LANG_REFERENCE.lines() {
            // Print line by line to honor any possible differences in line feeds.
            console.print(line)?;
        }
        console.print("")?;
        Ok(())
    }

    /// Checks if all command and function names are unique after discarding type annotations.
    // TODO(jmmv): This is a code smell from the lack of genericity between commands and functions.
    // If we can homogenize their representation, this should go away.
    fn all_names_unique(
        commands: &HashMap<&'static str, Rc<dyn BuiltinCommand>>,
        functions: &HashMap<&'static str, Rc<dyn BuiltinFunction>>,
    ) -> bool {
        let names: HashSet<&&'static str> = commands.keys().collect();
        for name in functions.keys() {
            if names.contains(&name) {
                return false;
            }
        }
        true
    }
}

#[async_trait(?Send)]
impl BuiltinCommand for HelpCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        machine: &mut Machine,
    ) -> exec::Result<()> {
        let commands = machine.get_commands();
        let functions = machine.get_functions();
        debug_assert!(HelpCommand::all_names_unique(commands, functions));
        match args {
            [] => {
                self.summary()?;
            }
            [(Some(Expr::Symbol(vref)), ArgSep::End)] => {
                let name = vref.name().to_ascii_uppercase();
                if name == "COMMANDS" {
                    if vref.ref_type() != VarType::Auto {
                        return exec::new_usage_error("Topic name cannot have a type annotation");
                    }
                    self.summarize_commands(commands)?;
                } else if name == "FUNCTIONS" {
                    if vref.ref_type() != VarType::Auto {
                        return exec::new_usage_error("Topic name cannot have a type annotation");
                    }
                    self.summarize_functions(functions)?;
                } else if name == "LANG" {
                    if vref.ref_type() != VarType::Auto {
                        return exec::new_usage_error("Topic name cannot have a type annotation");
                    }
                    self.describe_lang()?;
                } else {
                    let mut found = false;
                    if let Some(command) = &commands.get(name.as_str()) {
                        debug_assert!(!found);
                        if vref.ref_type() != VarType::Auto {
                            return exec::new_usage_error(
                                "Command name cannot have a type annotation",
                            );
                        }
                        self.describe_command(command)?;
                        found = true;
                    }
                    if let Some(function) = &functions.get(name.as_str()) {
                        debug_assert!(!found);
                        if vref.ref_type() != VarType::Auto
                            && vref.ref_type() != function.metadata().return_type()
                        {
                            return exec::new_usage_error(
                                "Incompatible type annotation for function",
                            );
                        }
                        self.describe_function(function)?;
                        found = true;
                    }
                    if !found {
                        return exec::new_usage_error(format!(
                            "Cannot describe unknown builtin or function {}",
                            name
                        ));
                    }
                }
            }
            _ => return exec::new_usage_error("HELP takes zero or only one argument"),
        }
        Ok(())
    }
}

#[cfg(test)]
pub(crate) mod testutils {
    use super::*;
    use crate::ast::Value;
    use crate::eval::{self, CallableMetadata, CallableMetadataBuilder};

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
    impl BuiltinCommand for DoNothingCommand {
        fn metadata(&self) -> &CallableMetadata {
            &self.metadata
        }

        async fn exec(
            &self,
            _args: &[(Option<Expr>, ArgSep)],
            _machine: &mut Machine,
        ) -> exec::Result<()> {
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

    impl BuiltinFunction for EmptyFunction {
        fn metadata(&self) -> &CallableMetadata {
            &self.metadata
        }

        fn exec(&self, _args: Vec<Value>) -> eval::Result<Value> {
            Ok(Value::Text("irrelevant".to_owned()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::testutils::*;
    use super::*;
    use crate::console::testutils::*;
    use crate::exec::MachineBuilder;
    use futures_lite::future::block_on;
    use std::cell::RefCell;

    /// Expects the output to the console to be just print calls and concatenates them all as they
    /// would have been printed on screen.
    fn flatten_captured_out(output: &[CapturedOut]) -> String {
        output.iter().fold(String::new(), |result, o| match o {
            CapturedOut::Print(text) => result + &text + "\n",
            _ => panic!("Unexpected element in output"),
        })
    }

    /// Runs the `input` code on a new machine and verifies that it fails with `expected_err`.
    fn do_error_test(input: &str, expected_err: &str) {
        let console = Rc::from(RefCell::from(MockConsoleBuilder::new().build()));
        let mut machine = MachineBuilder::default()
            .add_command(HelpCommand::new(console.clone()))
            .add_command(DoNothingCommand::new())
            .add_function(EmptyFunction::new())
            .build();
        assert_eq!(
            expected_err,
            format!(
                "{}",
                block_on(machine.exec(&mut input.as_bytes())).expect_err("Execution did not fail")
            )
        );
        assert!(console.borrow().captured_out().is_empty());
    }

    #[test]
    fn test_help_summarize_commands() {
        let console = Rc::from(RefCell::from(MockConsoleBuilder::new().build()));
        let mut machine = MachineBuilder::default()
            .add_command(HelpCommand::new(console.clone()))
            .add_command(DoNothingCommand::new())
            .build();
        block_on(machine.exec(&mut b"HELP COMMANDS".as_ref())).unwrap();

        let text = flatten_captured_out(console.borrow().captured_out());
        assert_eq!(
            "
    >> Interpreter manipulation <<
    HELP          Prints interactive help.

    >> Testing <<
    DO_NOTHING    This is the blurb.

    Type HELP followed by a command name for details on that command.

",
            text
        );
    }

    #[test]
    fn test_help_summarize_functions() {
        let console = Rc::from(RefCell::from(MockConsoleBuilder::new().build()));
        let mut machine = MachineBuilder::default()
            .add_command(HelpCommand::new(console.clone()))
            .add_function(EmptyFunction::new())
            .build();
        block_on(machine.exec(&mut b"HELP FUNCTIONS".as_ref())).unwrap();

        let text = flatten_captured_out(console.borrow().captured_out());
        assert_eq!(
            "
    >> Testing <<
    EMPTY$    This is the blurb.

    Type HELP followed by a function name for details on that function.

",
            text
        );
    }

    #[test]
    fn test_help_describe_command() {
        let console = Rc::from(RefCell::from(MockConsoleBuilder::new().build()));
        let mut machine = MachineBuilder::default()
            .add_command(HelpCommand::new(console.clone()))
            .add_command(DoNothingCommand::new())
            .build();
        block_on(machine.exec(&mut b"help Do_Nothing".as_ref())).unwrap();

        let text = flatten_captured_out(console.borrow().captured_out());
        assert_eq!(
            "
    DO_NOTHING this [would] <be|the> syntax \"specification\"

    This is the blurb.

    First paragraph of the extended description.

    Second paragraph of the extended description.

",
            &text
        );
    }

    fn do_help_describe_function_test(name: &str) {
        let console = Rc::from(RefCell::from(MockConsoleBuilder::new().build()));
        let mut machine = MachineBuilder::default()
            .add_command(HelpCommand::new(console.clone()))
            .add_function(EmptyFunction::new())
            .build();
        block_on(machine.exec(&mut format!("help {}", name).as_bytes())).unwrap();

        let text = flatten_captured_out(console.borrow().captured_out());
        assert_eq!(
            "
    EMPTY$(this [would] <be|the> syntax \"specification\")

    This is the blurb.

    First paragraph of the extended description.

    Second paragraph of the extended description.

",
            &text
        );
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
        let console = Rc::from(RefCell::from(MockConsoleBuilder::new().build()));
        let mut machine = MachineBuilder::default()
            .add_command(HelpCommand::new(console.clone()))
            .add_command(DoNothingCommand::new())
            .build();
        block_on(machine.exec(&mut b"help lang".as_ref())).unwrap();

        let text = flatten_captured_out(console.borrow().captured_out());
        assert_eq!(String::from(LANG_REFERENCE) + "\n", text);
    }

    #[test]
    fn test_help_errors() {
        do_error_test("HELP foo bar", "Unexpected value in expression");
        do_error_test("HELP foo, bar", "HELP takes zero or only one argument");

        do_error_test("HELP commands%", "Topic name cannot have a type annotation");
        do_error_test("HELP functions%", "Topic name cannot have a type annotation");
        do_error_test("HELP lang%", "Topic name cannot have a type annotation");

        do_error_test("HELP foo$", "Cannot describe unknown builtin or function FOO");
        do_error_test("HELP foo", "Cannot describe unknown builtin or function FOO");

        do_error_test("HELP do_nothing$", "Command name cannot have a type annotation");
        do_error_test("HELP empty?", "Incompatible type annotation for function");
    }
}
