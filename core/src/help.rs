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
use crate::exec::{BuiltinCommand, Machine};
use failure::Fallible;
use std::cell::RefCell;
use std::collections::HashMap;
use std::io::Write;
use std::rc::Rc;

/// The `HELP` command.
pub struct HelpCommand {
    output: Rc<RefCell<dyn Write>>,
}

impl HelpCommand {
    /// Creates a new command that writes help messages to `output`.
    pub fn new(output: Rc<RefCell<dyn Write>>) -> Self {
        Self { output }
    }

    /// Prints a summary of all available commands.
    fn summary(&self, builtins: &HashMap<&'static str, Rc<dyn BuiltinCommand>>) -> Fallible<()> {
        let mut names = vec![];
        let mut max_length = 0;
        for name in builtins.keys() {
            names.push(name);
            if name.len() > max_length {
                max_length = name.len();
            }
        }
        names.sort();

        let mut output = self.output.borrow_mut();
        output
            .write_fmt(format_args!("\n    This is EndBASIC {}.\n\n", env!("CARGO_PKG_VERSION")))?;
        for name in names {
            let filler = " ".repeat(max_length - name.len());
            let builtin = builtins.get(name).unwrap();
            let blurb = builtin.description().lines().next().unwrap();
            output.write_fmt(format_args!("    {}{}    {}\n", builtin.name(), filler, blurb))?;
        }
        output.write_all(
            b"\n    Type HELP followed by a command name for details on that command.",
        )?;
        // TODO(jmmv): Replace with an EXIT command.
        output.write_all(b"\n    Press CTRL+D to exit.\n\n")?;
        Ok(())
    }

    /// Prints details about a single command.
    fn describe(&self, builtin: &Rc<dyn BuiltinCommand>) -> Fallible<()> {
        let mut output = self.output.borrow_mut();
        output.write_all(b"\n")?;
        if builtin.syntax().is_empty() {
            output.write_fmt(format_args!("    {}\n", builtin.name()))?;
        } else {
            output.write_fmt(format_args!("    {} {}\n", builtin.name(), builtin.syntax()))?;
        }
        for line in builtin.description().lines() {
            output.write_all(b"\n")?;
            output.write_fmt(format_args!("    {}\n", line))?;
        }
        output.write_all(b"\n")?;
        Ok(())
    }
}

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

    fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
        let builtins = machine.get_builtins();
        match args {
            [] => {
                self.summary(builtins)?;
            }
            [(Some(Expr::Symbol(vref)), ArgSep::End)] => {
                ensure!(vref.ref_type() == VarType::Auto);
                let name = vref.name().to_ascii_uppercase();
                match &builtins.get(name.as_str()) {
                    Some(builtin) => self.describe(builtin)?,
                    None => bail!("Cannot describe unknown builtin {}", name),
                }
            }
            _ => bail!("HELP takes zero or only one argument"),
        }
        Ok(())
    }
}

#[cfg(test)]
pub(crate) mod testutils {
    use super::*;

    /// A command that does nothing.
    pub(crate) struct DoNothingCommand {}

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

        fn exec(&self, _args: &[(Option<Expr>, ArgSep)], _machine: &mut Machine) -> Fallible<()> {
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::testutils::*;
    use super::*;
    use crate::exec::MachineBuilder;
    use std::cell::RefCell;

    #[test]
    fn test_help_summary() {
        let output = Rc::from(RefCell::from(vec![]));
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(HelpCommand { output: output.clone() }))
            .add_builtin(Rc::from(DoNothingCommand {}))
            .build();
        machine.exec(&mut b"HELP".as_ref()).unwrap();

        let output = output.borrow();
        let text = std::str::from_utf8(&output).unwrap();
        let version_re = regex::Regex::new("[0-9]+\\.[0-9]+\\.[0-9]+").unwrap();
        let text = version_re.replace_all(&text, "X.Y.Z").to_owned();
        assert_eq!(
            "
    This is EndBASIC X.Y.Z.

    DO_NOTHING    This is the blurb.
    HELP          Prints interactive help.

    Type HELP followed by a command name for details on that command.
    Press CTRL+D to exit.

",
            text
        );
    }

    #[test]
    fn test_help_describe() {
        let output = Rc::from(RefCell::from(vec![]));
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(HelpCommand { output: output.clone() }))
            .add_builtin(Rc::from(DoNothingCommand {}))
            .build();
        machine.exec(&mut b"help Do_Nothing".as_ref()).unwrap();

        assert_eq!(
            "
    DO_NOTHING this [would] <be|the> syntax \"specification\"

    This is the blurb.

    First paragraph of the extended description.

    Second paragraph of the extended description.

",
            std::str::from_utf8(&output.borrow()).unwrap()
        );
    }
}
