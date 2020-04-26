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

use crate::console;
use crate::exec::MachineBuilder;
use rustyline::error::ReadlineError;
use rustyline::Editor;
use std::cell::RefCell;
use std::io::{self, Write};
use std::rc::Rc;

/// Converts a `ReadLine` error into an `io::Error`.
fn readline_error_to_io_error(e: ReadlineError) -> io::Error {
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
///
/// This is separate from `TtyConsole` to have full control on what gets written to stdout.  For
/// example: we do not use `rustyline` here because it wouldn't print a prompt when not attached
/// to the console---but we want to see it during `INPUT` calls.
#[derive(Default)]
struct RawConsole {}

impl console::Console for RawConsole {
    fn input(&mut self, prompt: &str, _previous: &str) -> io::Result<String> {
        if !prompt.is_empty() {
            let mut stdout = io::stdout();
            stdout.write_all(prompt.as_bytes())?;
            stdout.flush()?;
        }

        let mut answer = String::new();
        io::stdin().read_line(&mut answer)?;
        Ok(answer.trim_end().to_owned())
    }

    fn print(&mut self, text: &str) -> io::Result<()> {
        println!("{}", text);
        Ok(())
    }
}

/// Implementation of the EndBASIC console with fancier interactive support.
///
/// Uses `rustyline` to obtain input, which allows for better interactive editing when dealing with
/// a console but falls back to simpler reads when dealing with a file.
#[derive(Default)]
struct TtyConsole {}

impl console::Console for TtyConsole {
    fn input(&mut self, prompt: &str, previous: &str) -> io::Result<String> {
        let mut rl = rustyline::Editor::<()>::new();
        let answer = match rl.readline_with_initial(prompt, (previous, "")) {
            Ok(line) => line,
            Err(e) => return Err(readline_error_to_io_error(e)),
        };
        Ok(answer.trim_end().to_owned())
    }

    fn print(&mut self, text: &str) -> io::Result<()> {
        println!("{}", text);
        Ok(())
    }
}

/// Creates a new console for stdin/stdout depending on whether they are attached to a TTY or not.
pub fn new_console() -> Rc<RefCell<dyn console::Console>> {
    let mut rl = Editor::<()>::new();
    let is_tty = rl.dimensions().is_some();
    if is_tty {
        Rc::from(RefCell::from(TtyConsole::default()))
    } else {
        Rc::from(RefCell::from(RawConsole::default()))
    }
}

/// Enters the interactive interpreter.
pub fn run_repl_loop() -> io::Result<()> {
    let console = new_console();
    let mut machine = MachineBuilder::default()
        .add_builtins(console::all_commands(console))
        .build();

    println!();
    println!("    Welcome to EndBASIC {}", env!("CARGO_PKG_VERSION"));
    println!();

    let mut rl = Editor::<()>::new();
    loop {
        match rl.readline("Ready\n") {
            Ok(mut line) => {
                rl.add_history_entry(line.as_str());
                let mut input = io::Cursor::new(&mut line);
                match machine.exec(&mut input) {
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
