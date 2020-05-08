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
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(
    unused,
    unused_extern_crates,
    unused_import_braces,
    unused_qualifications
)]
#![warn(unsafe_code)]

#[macro_use]
extern crate failure;

use failure::{Error, Fail, Fallible};
use getopts::Options;
use std::cell::RefCell;
use std::env;
use std::fs::File;
use std::path::{Path, PathBuf};
use std::process;
use std::rc::Rc;

/// Errors caused by the user when invoking this binary (invalid options or arguments).
#[derive(Debug, Fail)]
#[fail(display = "{}", message)]
struct UsageError {
    message: String,
}

impl UsageError {
    /// Creates a new usage error with `message`.
    fn new<T: Into<String>>(message: T) -> Self {
        Self {
            message: message.into(),
        }
    }
}

/// Flattens all causes of an error into a single string.
fn flatten_causes(err: &Error) -> String {
    err.iter_chain().fold(String::new(), |flattened, cause| {
        let flattened = if flattened.is_empty() {
            flattened
        } else {
            flattened + ": "
        };
        flattened + &format!("{}", cause)
    })
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
fn help(name: &str, opts: &Options) -> Fallible<()> {
    let brief = format!("Usage: {} [options] [program-file]", name);
    println!("{}", opts.usage(&brief));
    println!("Report bugs to: https://github.com/jmmv/endbasic/issues");
    println!("EndBASIC home page: https://github.com/jmmv/endbasic");
    Ok(())
}

/// Prints version information following the GNU Standards format.
fn version() -> Fallible<()> {
    println!("EndBASIC {}", env!("CARGO_PKG_VERSION"));
    println!("Copyright 2020 Julio Merino");
    println!("License Apache Version 2.0 <http://www.apache.org/licenses/LICENSE-2.0>");
    Ok(())
}

/// Computes the path to the directory where user programs live if `flag` is none; otherwise
/// just returns `flag`.
fn get_programs_dir(flag: Option<String>) -> Fallible<PathBuf> {
    let dir = flag.map(PathBuf::from).or_else(|| {
        dirs::document_dir()
            .map(|d| d.join("endbasic"))
            .or_else(|| {
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
    ensure!(
        dir.is_some(),
        "Cannot compute default path to the Documents folder"
    );
    Ok(dir.unwrap())
}

/// Executes the `path` program in a fresh machine.
fn run<P: AsRef<Path>>(path: P) -> Fallible<()> {
    let console = Rc::from(RefCell::from(endbasic::repl::TextConsole::from_stdio()));
    let mut machine = endbasic::exec::MachineBuilder::default()
        .add_builtins(endbasic::console::all_commands(console))
        .build();

    let mut input = File::open(path)?;
    machine.exec(&mut input)
}

/// Version of `main` that returns errors to the caller for reporting.
fn safe_main(name: &str, args: env::Args) -> Fallible<()> {
    let args: Vec<String> = args.collect();

    let mut opts = Options::new();
    opts.optflag("h", "help", "show command-line usage information and exit");
    opts.optopt(
        "",
        "programs-dir",
        "directory where user programs are stored",
        "PATH",
    );
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
            Ok(endbasic::repl::run_repl_loop(&programs_dir)?)
        }
        [file] => run(file),
        [_, ..] => Err(UsageError::new("Too many arguments").into()),
    }
}

fn main() {
    let (name, args) = program_name(env::args(), "endbasic");
    if let Err(e) = safe_main(&name, args) {
        if let Some(e) = e.downcast_ref::<UsageError>() {
            eprintln!("Usage error: {}", e);
            eprintln!("Type {} --help for more information", name);
            process::exit(2);
        } else if let Some(e) = e.downcast_ref::<getopts::Fail>() {
            eprintln!("Usage error: {}", e);
            eprintln!("Type {} --help for more information", name);
            process::exit(2);
        } else {
            eprintln!("{}: {}", name, flatten_causes(&e));
            process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flatten_causes_one() {
        assert_eq!("the error", flatten_causes(&format_err!("the error")));
    }

    #[test]
    fn flatten_causes_several() {
        let err = Error::from(format_err!("first").context("second").context("and last"));
        assert_eq!("and last: second: first", flatten_causes(&err));
    }
}
