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
use endbasic_std::storage::Storage;
use endbasic_std::terminal::TerminalConsole;
use futures_lite::future::block_on;
use getopts::Options;
use std::cell::RefCell;
use std::env;
use std::fs::File;
use std::io;
use std::path::Path;
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
fn help(name: &str, opts: &Options) {
    let brief = format!("Usage: {} [options] [program-file]", name);
    println!("{}", opts.usage(&brief));
    println!("Report bugs to: https://github.com/jmmv/endbasic/issues");
    println!("EndBASIC home page: https://github.com/jmmv/endbasic");
}

/// Prints version information following the GNU Standards format.
fn version() {
    println!("EndBASIC {}", env!("CARGO_PKG_VERSION"));
    println!("Copyright 2020-2021 Julio Merino");
    println!("License Apache Version 2.0 <http://www.apache.org/licenses/LICENSE-2.0>");
}

/// Returns `flag` if present, or else returns the URI of the default `LOCAL` drive.
fn get_local_drive_spec(flag: Option<String>) -> Result<String> {
    let dir = flag.or_else(|| {
        dirs::document_dir().map(|d| format!("file://{}", d.join("endbasic").display())).or_else(
            || {
                // On Linux, dirs::document_dir() seems to return None whenever user-dirs.dirs is
                // not present... which is suboptimal.  Compute a reasonable default based on the
                // home directory.
                dirs::home_dir()
                    .map(|h| format!("file://{}", h.join("Documents/endbasic").display()))
            },
        )
    });

    // Instead of aborting on a missing programs directory, we could disable the LOAD/SAVE commands
    // when we cannot compute this folder, but that seems like hiding a corner case that is unlikely
    // to surface.  A good reason to do this, however, would be to allow the user to explicitly
    // disable this functionality to keep the interpreter from touching the disk.
    match dir {
        Some(dir) => Ok(dir),
        None => Err(anyhow!("Cannot compute default path to the Documents folder")),
    }
}

/// Sets up the common storage drives.
///
/// This instantiates non-optional drives, such as `MEMORY:` and `DEMOS:`, maps `LOCAL` the
/// location given in `local_drive_spec`.
pub fn setup_storage(storage: &mut Storage, local_drive_spec: &str) -> io::Result<()> {
    storage.register_scheme("demos", endbasic::demos::demos_drive_factory);
    storage.mount("demos", "demos://").expect("Demos drive shouldn't fail to mount");
    storage.register_scheme("file", endbasic_std::storage::directory_drive_factory);
    storage.mount("local", local_drive_spec)?;
    storage.cd("local:").expect("Local drive was just registered");
    Ok(())
}

/// Enters the interactive interpreter.
///
/// `local_drive` is the optional local drive to mount and use as the default location.
fn run_repl_loop(local_drive_spec: &str) -> endbasic_core::exec::Result<i32> {
    let console = Rc::from(RefCell::from(TerminalConsole::from_stdio()?));
    let mut builder =
        endbasic_std::MachineBuilder::default().with_console(console.clone()).make_interactive();

    let storage = builder.get_storage();
    setup_storage(&mut storage.borrow_mut(), local_drive_spec)?;

    let mut machine = builder.build()?;
    endbasic::print_welcome(console.clone())?;
    block_on(endbasic::try_load_autoexec(&mut machine, console.clone(), storage))?;
    Ok(block_on(endbasic::run_repl_loop(&mut machine, console))?)
}

/// Executes the `path` program in a fresh machine.
fn run_script<P: AsRef<Path>>(path: P) -> endbasic_core::exec::Result<i32> {
    let mut machine = endbasic_std::MachineBuilder::default().build()?;
    let mut input = File::open(path)?;
    Ok(block_on(machine.exec(&mut input))?.as_exit_code())
}

/// Executes the `path` program in a fresh machine allowing any interactive-only calls.
///
/// `local_drive` is the optional local drive to mount and use as the default location.
fn run_interactive<P: AsRef<Path>>(
    path: P,
    local_drive_spec: &str,
) -> endbasic_core::exec::Result<i32> {
    let mut builder = endbasic_std::MachineBuilder::default().make_interactive();

    let storage = builder.get_storage();
    setup_storage(&mut storage.borrow_mut(), local_drive_spec)?;

    let mut machine = builder.build()?;
    let mut input = File::open(path)?;
    Ok(block_on(machine.exec(&mut input))?.as_exit_code())
}

/// Version of `main` that returns errors to the caller for reporting.
fn safe_main(name: &str, args: env::Args) -> Result<i32> {
    let args: Vec<String> = args.collect();

    let mut opts = Options::new();
    opts.optflag("h", "help", "show command-line usage information and exit");
    opts.optflag("i", "interactive", "force interactive mode when running a script");
    opts.optopt("", "local-drive", "location of the drive to mount as LOCAL", "URI");
    opts.optflag("", "version", "show version information and exit");
    let matches = opts.parse(args)?;

    if matches.opt_present("help") {
        help(name, &opts);
        return Ok(0);
    }

    if matches.opt_present("version") {
        version();
        return Ok(0);
    }

    match matches.free.as_slice() {
        [] => {
            let local_drive = get_local_drive_spec(matches.opt_str("local-drive"))?;
            Ok(run_repl_loop(&local_drive)?)
        }
        [file] => {
            if matches.opt_present("interactive") {
                let local_drive = get_local_drive_spec(matches.opt_str("local-drive"))?;
                Ok(run_interactive(file, &local_drive)?)
            } else {
                Ok(run_script(file)?)
            }
        }
        [_, ..] => Err(UsageError::new("Too many arguments").into()),
    }
}

fn main() {
    let (name, args) = program_name(env::args(), "endbasic");
    let exit_code = match safe_main(&name, args) {
        Ok(code) => code,
        Err(e) => {
            if let Some(e) = e.downcast_ref::<UsageError>() {
                eprintln!("Usage error: {}", e);
                eprintln!("Type {} --help for more information", name);
                2
            } else if let Some(e) = e.downcast_ref::<getopts::Fail>() {
                eprintln!("Usage error: {}", e);
                eprintln!("Type {} --help for more information", name);
                2
            } else {
                eprintln!("{}: {}", name, e);
                1
            }
        }
    };
    // There should not be any interesting destructors left behind when calling this, or else they
    // will not run.
    process::exit(exit_code);
}
