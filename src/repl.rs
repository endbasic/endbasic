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

//! Interactive interpreter for the EndBASIC language.

use crate::ast::{ArgSep, Expr, VarType};
use crate::console;
use crate::exec::{BuiltinCommand, Machine, MachineBuilder};
use crate::program;
use crossterm::{cursor, execute, terminal, tty::IsTty};
use failure::Fallible;
use rustyline::error::ReadlineError;
use rustyline::Editor;
use std::cell::RefCell;
use std::collections::HashMap;
use std::io::{self, Write};
use std::path::Path;
use std::rc::Rc;

/// The `CLEAR` command.
struct ClearCommand {}

impl BuiltinCommand for ClearCommand {
    fn name(&self) -> &'static str {
        "CLEAR"
    }

    fn syntax(&self) -> &'static str {
        ""
    }

    fn description(&self) -> &'static str {
        "Clears all variables to restore initial state."
    }

    fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> Fallible<()> {
        ensure!(args.is_empty(), "CLEAR takes no arguments");
        machine.clear();
        Ok(())
    }
}

/// The `HELP` command.
struct HelpCommand {
    output: Rc<RefCell<dyn Write>>,
}

impl HelpCommand {
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
        output.write_fmt(format_args!(
            "\n    This is EndBASIC {}.\n\n",
            env!("CARGO_PKG_VERSION")
        ))?;
        for name in names {
            let filler = " ".repeat(max_length - name.len());
            let builtin = builtins.get(name).unwrap();
            let blurb = builtin.description().lines().next().unwrap();
            output.write_fmt(format_args!(
                "    {}{}    {}\n",
                builtin.name(),
                filler,
                blurb
            ))?;
        }
        output.write_all(
            b"\n    Type HELP followed by a command name for details on that command.",
        )?;
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
            output.write_fmt(format_args!(
                "    {} {}\n",
                builtin.name(),
                builtin.syntax()
            ))?;
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

//// Converts a `crossterm::ErrorKind` to an `io::Error`.
fn crossterm_error_to_io_error(e: crossterm::ErrorKind) -> io::Error {
    match e {
        crossterm::ErrorKind::IoError(e) => e,
        crossterm::ErrorKind::Utf8Error(e) => {
            io::Error::new(io::ErrorKind::InvalidData, format!("{}", e))
        }
        _ => io::Error::new(io::ErrorKind::Other, format!("{}", e)),
    }
}

/// Converts a `ReadLine` error into an `io::Error`.
pub(crate) fn readline_error_to_io_error(e: ReadlineError) -> io::Error {
    let kind = match e {
        ReadlineError::Eof => io::ErrorKind::UnexpectedEof,
        ReadlineError::Interrupted => io::ErrorKind::Interrupted,
        #[cfg(unix)]
        ReadlineError::Utf8Error => io::ErrorKind::InvalidData,
        #[cfg(windows)]
        ReadlineError::Decode(_) => io::ErrorKind::InvalidData,
        _ => io::ErrorKind::Other,
    };
    io::Error::new(kind, format!("{}", e))
}

/// Implementation of the EndBASIC console to interact with stdin and stdout.
pub struct TextConsole {
    is_tty: bool,
}

impl TextConsole {
    /// Creates a new console based on the properties of stdin/stdout.
    pub fn from_stdio() -> Self {
        Self {
            is_tty: io::stdout().is_tty(),
        }
    }
}

impl console::Console for TextConsole {
    fn clear(&mut self) -> io::Result<()> {
        execute!(
            io::stdout(),
            terminal::Clear(terminal::ClearType::All),
            cursor::MoveTo(0, 0)
        )
        .map_err(crossterm_error_to_io_error)
    }

    fn input(&mut self, prompt: &str, previous: &str) -> io::Result<String> {
        let answer = if self.is_tty {
            let mut rl = Editor::<()>::new();
            match rl.readline_with_initial(prompt, (previous, "")) {
                Ok(line) => line,
                Err(e) => return Err(readline_error_to_io_error(e)),
            }
        } else {
            if !prompt.is_empty() {
                let mut stdout = io::stdout();
                stdout.write_all(prompt.as_bytes())?;
                stdout.flush()?;
            }

            let mut answer = String::new();
            io::stdin().read_line(&mut answer)?;
            answer
        };
        Ok(answer.trim_end().to_owned())
    }

    fn print(&mut self, text: &str) -> io::Result<()> {
        println!("{}", text);
        Ok(())
    }
}

/// Enters the interactive interpreter.
///
/// `dir` specifies the directory that the interpreter will use for any commands that manipulate
/// files.
pub fn run_repl_loop(dir: &Path) -> io::Result<()> {
    let console = Rc::from(RefCell::from(TextConsole::from_stdio()));
    let mut machine = MachineBuilder::default()
        .add_builtin(Rc::from(ClearCommand {}))
        .add_builtin(Rc::from(HelpCommand {
            output: Rc::from(RefCell::from(io::stdout())),
        }))
        .add_builtins(console::all_commands(console.clone()))
        .add_builtins(program::all_commands(console, dir))
        .build();

    println!();
    println!("    Welcome to EndBASIC {}.", env!("CARGO_PKG_VERSION"));
    println!("    Type HELP for interactive usage information.");
    println!();

    let mut rl = Editor::<()>::new();
    loop {
        match rl.readline("Ready\n") {
            Ok(line) => {
                rl.add_history_entry(line.as_str());
                match machine.exec(&mut line.as_bytes()) {
                    Ok(()) => (),
                    Err(e) => {
                        println!("ERROR: {}", e);
                    }
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("Interrupted by CTRL-C");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("End of input by CTRL-D");
                break;
            }
            Err(e) => return Err(readline_error_to_io_error(e)),
        }
    }
    Ok(())
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

    #[test]
    fn test_clear_ok() {
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(ClearCommand {}))
            .build();
        machine.exec(&mut b"a = 1".as_ref()).unwrap();
        assert!(machine.get_var_as_int("a").is_ok());
        machine.exec(&mut b"CLEAR".as_ref()).unwrap();
        assert!(machine.get_var_as_int("a").is_err());
    }

    #[test]
    fn test_clear_errors() {
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(ClearCommand {}))
            .build();
        assert_eq!(
            "CLEAR takes no arguments",
            format!("{}", machine.exec(&mut b"CLEAR 123".as_ref()).unwrap_err())
        );
    }

    #[test]
    fn test_help_summary() {
        let output = Rc::from(RefCell::from(vec![]));
        let mut machine = MachineBuilder::default()
            .add_builtin(Rc::from(HelpCommand {
                output: output.clone(),
            }))
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
            .add_builtin(Rc::from(HelpCommand {
                output: output.clone(),
            }))
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
