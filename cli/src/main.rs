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

//! Command-line interface for the EndBASIC language.

// Keep these in sync with other top-level files.
#![allow(clippy::await_holding_refcell_ref)]
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(unused, unused_extern_crates, unused_import_braces, unused_qualifications)]
#![warn(unsafe_code)]

use anyhow::{anyhow, Result};
use endbasic_std::store::{FileStore, Store};
use endbasic_std::terminal::TerminalConsole;
use futures_lite::future::block_on;
use getopts::Options;
use std::cell::RefCell;
use std::env;
use std::fs::File;
use std::io;
use std::path::{Path, PathBuf};
use std::process;
use std::rc::Rc;

/// Errors caused by the user when invoking this binary (invalid options or arguments).
#[derive(Debug, thiserror::Error)]
#[error("{message}")]
struct UsageError {
    message: String,
}

impl UsageError {
    /// Creates a new usage error with `message`.
    fn new<T: Into<String>>(message: T) -> Self {
        Self { message: message.into() }
    }
}

/// Consumes and returns the program name from `env::Args`.
///
/// If the program name cannot be obtained, return `default_name` instead.
fn program_name(mut args: env::Args, default_name: &'static str) -> (String, env::Args) {
    let name = match args.next() {
        Some(arg0) => match Path::new(&arg0).file_stem() {
            Some(basename) => match basename.to_str() {
                Some(s) => s.to_owned(),
                None => default_name.to_owned(),
            },
            None => default_name.to_owned(),
        },
        None => default_name.to_owned(),
    };
    (name, args)
}

/// Prints usage information for program `name` with `opts` following the GNU Standards format.
fn help(name: &str, opts: &Options) -> Result<i32> {
    let brief = format!("Usage: {} [options] [program-file]", name);
    println!("{}", opts.usage(&brief));
    println!("Report bugs to: https://github.com/jmmv/endbasic/issues");
    println!("EndBASIC home page: https://github.com/jmmv/endbasic");
    Ok(0)
}

/// Prints version information following the GNU Standards format.
fn version() -> Result<i32> {
    println!("EndBASIC {}", env!("CARGO_PKG_VERSION"));
    println!("Copyright 2020-2021 Julio Merino");
    println!("License Apache Version 2.0 <http://www.apache.org/licenses/LICENSE-2.0>");
    Ok(0)
}

/// Computes the path to the directory where user programs live if `flag` is none; otherwise
/// just returns `flag`.
fn get_programs_dir(flag: Option<String>) -> Result<PathBuf> {
    let dir = flag.map(PathBuf::from).or_else(|| {
        dirs::document_dir().map(|d| d.join("endbasic")).or_else(|| {
            // On Linux, dirs::document_dir() seems to return None whenever user-dirs.dirs is
            // not present... which is suboptimal.  Compute a reasonable default based on the
            // home directory.
            dirs::home_dir().map(|h| h.join("Documents/endbasic"))
        })
    });

    // Instead of aborting on a missing programs directory, we could disable the LOAD/SAVE commands
    // when we cannot compute this folder, but that seems like hiding a corner case that is unlikely
    // to surface.  A good reason to do this, however, would be to allow the user to explicitly
    // disable this functionality to keep the interpreter from touching the disk.
    if dir.is_none() {
        return Err(anyhow!("Cannot compute default path to the Documents folder"));
    }
    Ok(dir.unwrap())
}

/// Creates a new store backed by `dir` and overlays the built-in demos.
fn new_store_with_demos(dir: &Path) -> Rc<RefCell<dyn Store>> {
    if dir == Path::new(":memory:") {
        Rc::from(RefCell::from(endbasic::demos::DemoStoreOverlay::new(
            endbasic_std::store::InMemoryStore::default(),
        )))
    } else {
        Rc::from(RefCell::from(endbasic::demos::DemoStoreOverlay::new(FileStore::new(dir))))
    }
}

/// Enters the interactive interpreter.
///
/// `dir` specifies the directory that the interpreter will use for any commands that manipulate
/// files.  The special name `:memory:` makes the interpreter use an in-memory only store.
fn run_repl_loop(dir: &Path) -> io::Result<i32> {
    let console = Rc::from(RefCell::from(TerminalConsole::from_stdio()?));
    let store = new_store_with_demos(dir);
    let mut machine = endbasic_std::interactive_machine(console.clone(), store.clone());
    endbasic::print_welcome(console.clone())?;
    endbasic::try_load_autoexec(&mut machine, console.clone(), store)?;
    block_on(endbasic::run_repl_loop(&mut machine, console))
}

/// Executes the `path` program in a fresh machine.
fn run_script<P: AsRef<Path>>(path: P) -> endbasic_core::exec::Result<i32> {
    let console = Rc::from(RefCell::from(TerminalConsole::from_stdio()?));
    let mut machine = endbasic_std::scripting_machine(console);
    let mut input = File::open(path)?;
    Ok(block_on(machine.exec(&mut input))?.as_exit_code())
}

/// Executes the `path` program in a fresh machine allowing any interactive-only calls.
///
/// `dir` has the same meaning as the parameter passed to `run_repl_loop`.
fn run_interactive<P: AsRef<Path>>(path: P, dir: &Path) -> endbasic_core::exec::Result<i32> {
    let console = Rc::from(RefCell::from(TerminalConsole::from_stdio()?));
    let mut machine = endbasic_std::interactive_machine(console, new_store_with_demos(dir));
    let mut input = File::open(path)?;
    Ok(block_on(machine.exec(&mut input))?.as_exit_code())
}

/// Version of `main` that returns errors to the caller for reporting.
fn safe_main(name: &str, args: env::Args) -> Result<i32> {
    let args: Vec<String> = args.collect();

    let mut opts = Options::new();
    opts.optflag("h", "help", "show command-line usage information and exit");
    opts.optflag("i", "interactive", "force interactive mode when running a script");
    opts.optopt("", "programs-dir", "directory where user programs are stored", "PATH");
    opts.optflag("", "version", "show version information and exit");
    let matches = opts.parse(args)?;

    if matches.opt_present("help") {
        return help(name, &opts);
    }

    if matches.opt_present("version") {
        return version();
    }

    match matches.free.as_slice() {
        [] => {
            let programs_dir = get_programs_dir(matches.opt_str("programs-dir"))?;
            Ok(run_repl_loop(&programs_dir)?)
        }
        [file] => {
            if matches.opt_present("interactive") {
                let programs_dir = get_programs_dir(matches.opt_str("programs-dir"))?;
                Ok(run_interactive(file, &programs_dir)?)
            } else {
                Ok(run_script(file)?)
            }
        }
        [_, ..] => Err(UsageError::new("Too many arguments").into()),
    }
}

fn main() {
    let (name, args) = program_name(env::args(), "endbasic");
    match safe_main(&name, args) {
        Ok(code) => process::exit(code),
        Err(e) => {
            if let Some(e) = e.downcast_ref::<UsageError>() {
                eprintln!("Usage error: {}", e);
                eprintln!("Type {} --help for more information", name);
                process::exit(2);
            } else if let Some(e) = e.downcast_ref::<getopts::Fail>() {
                eprintln!("Usage error: {}", e);
                eprintln!("Type {} --help for more information", name);
                process::exit(2);
            } else {
                eprintln!("{}: {}", name, e);
                process::exit(1);
            }
        }
    }
}
