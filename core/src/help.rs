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
use crate::exec::{self, BuiltinCommand, Machine};
use async_trait::async_trait;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

/// Cheat-sheet for the language syntax.
const LANG_REFERENCE: &str = r"
    Variable types and references:
        name?    Boolean variable (TRUE and FALSE).
        name%    Integer variable (32 bits).
        name$    String variable.
        name     Automatic variable (type determined by its value).

    Assignments:
        varref = expr

    Expressions:
        a + b      a - b       a * b     a / b      a MOD b    -a
        a AND b    NOT a       a OR b    a XOR b
        a = b      a <> b      a < b     a <= b     a > b      a >= b
        (a)        varref

    Flow control:
        IF expr THEN: ...: ELSE IF expr THEN: ...: ELSE: ...: END IF
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
    console: Rc<RefCell<dyn Console>>,
}

impl HelpCommand {
    /// Creates a new command that writes help messages to `output`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Self {
        Self { console }
    }

    /// Prints a summary of all available commands.
    fn summary(
        &self,
        builtins: &HashMap<&'static str, Rc<dyn BuiltinCommand>>,
    ) -> exec::Result<()> {
        let mut names = vec![];
        let mut max_length = 0;
        for name in builtins.keys() {
            names.push(name);
            if name.len() > max_length {
                max_length = name.len();
            }
        }
        names.sort();

        let mut console = self.console.borrow_mut();
        console.print("")?;
        for name in names {
            let filler = " ".repeat(max_length - name.len());
            let builtin = builtins.get(name).unwrap();
            let blurb = builtin.description().lines().next().unwrap();
            console.print(&format!("    {}{}    {}", builtin.name(), filler, blurb))?;
        }
        console.print("")?;
        console.print("    Type HELP followed by a command name for details on that command.")?;
        console.print("    Type HELP LANG for a quick reference guide about the language.")?;
        console.print("")?;
        Ok(())
    }

    /// Prints details about a single command.
    fn describe(&self, builtin: &Rc<dyn BuiltinCommand>) -> exec::Result<()> {
        let mut console = self.console.borrow_mut();
        console.print("")?;
        if builtin.syntax().is_empty() {
            console.print(&format!("    {}", builtin.name()))?;
        } else {
            console.print(&format!("    {} {}", builtin.name(), builtin.syntax()))?;
        }
        for line in builtin.description().lines() {
            console.print("")?;
            console.print(&format!("    {}", line))?;
        }
        console.print("")?;
        Ok(())
    }

    fn describe_lang(&self) -> exec::Result<()> {
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
impl BuiltinCommand for HelpCommand {
    fn name(&self) -> &'static str {
        "HELP"
    }

    fn syntax(&self) -> &'static str {
        "[commandname]"
    }

    fn description(&self) -> &'static str {
        "Prints interactive help.
Without arguments, shows a summary of all available commands.
With a single argument, shows detailed information about the given command."
    }

    async fn exec(
        &self,
        args: &[(Option<Expr>, ArgSep)],
        machine: &mut Machine,
    ) -> exec::Result<()> {
        let builtins = machine.get_builtins();
        match args {
            [] => {
                self.summary(builtins)?;
            }
            [(Some(Expr::Symbol(vref)), ArgSep::End)] => {
                if vref.ref_type() != VarType::Auto {
                    return exec::new_usage_error("Command name cannot have a type annotation");
                }
                let name = vref.name().to_ascii_uppercase();
                if name == "LANG" {
                    self.describe_lang()?;
                } else {
                    match &builtins.get(name.as_str()) {
                        Some(builtin) => self.describe(builtin)?,
                        None => {
                            return exec::new_usage_error(format!(
                                "Cannot describe unknown builtin {}",
                                name
                            ))
                        }
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

    /// A command that does nothing.
    pub(crate) struct DoNothingCommand {}

    #[async_trait(?Send)]
    impl BuiltinCommand for DoNothingCommand {
        fn name(&self) -> &'static str {
            "DO_NOTHING"
        }

        fn syntax(&self) -> &'static str {
            "this [would] <be|the> syntax \"specification\""
        }

        fn description(&self) -> &'static str {
            "This is the blurb.
First paragraph of the extended description.
Second paragraph of the extended description."
        }

        async fn exec(
            &self,
            _args: &[(Option<Expr>, ArgSep)],
            _machine: &mut Machine,
        ) -> exec::Result<()> {
            Ok(())
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
        let console = Rc::from(RefCell::from(MockConsole::new("")));
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(HelpCommand { console: console.clone() }))
            .add_builtin(Rc::from(DoNothingCommand {}))
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
    fn test_help_summary() {
        let console = Rc::from(RefCell::from(MockConsole::new("")));
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(HelpCommand { console: console.clone() }))
            .add_builtin(Rc::from(DoNothingCommand {}))
            .build();
        block_on(machine.exec(&mut b"HELP".as_ref())).unwrap();

        let text = flatten_captured_out(console.borrow().captured_out());
        assert_eq!(
            "
    DO_NOTHING    This is the blurb.
    HELP          Prints interactive help.

    Type HELP followed by a command name for details on that command.
    Type HELP LANG for a quick reference guide about the language.

",
            text
        );
    }

    #[test]
    fn test_help_describe() {
        let console = Rc::from(RefCell::from(MockConsole::new("")));
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(HelpCommand { console: console.clone() }))
            .add_builtin(Rc::from(DoNothingCommand {}))
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

    #[test]
    fn test_help_lang() {
        let console = Rc::from(RefCell::from(MockConsole::new("")));
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(HelpCommand { console: console.clone() }))
            .add_builtin(Rc::from(DoNothingCommand {}))
            .build();
        block_on(machine.exec(&mut b"help lang".as_ref())).unwrap();

        let text = flatten_captured_out(console.borrow().captured_out());
        assert_eq!(String::from(LANG_REFERENCE) + "\n", text);
    }

    #[test]
    fn test_help_errors() {
        do_error_test("HELP foo bar", "Unexpected value in expression");
        do_error_test("HELP foo, bar", "HELP takes zero or only one argument");

        do_error_test("HELP foo$", "Command name cannot have a type annotation");
        do_error_test("HELP lang%", "Command name cannot have a type annotation");
        do_error_test("HELP foo", "Cannot describe unknown builtin FOO");
    }
}
