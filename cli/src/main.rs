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
#![allow(clippy::collapsible_else_if)]
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(unused, unused_extern_crates, unused_import_braces, unused_qualifications)]
#![warn(unsafe_code)]

use anyhow::{anyhow, Result};
use async_channel::Sender;
use endbasic_core::exec::Signal;
use endbasic_std::console::Console;
use endbasic_std::storage::Storage;
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
    println!("CONSOLE-SPEC can be one of the following:");
    if cfg!(feature = "sdl") {
        println!("    graphics[:SPEC]     enables the graphical console and configures it");
        println!("                        with the settings in SPEC, which is of the form:");
        println!("                        RESOLUTION,TTF_FONT_PATH,FONT_SIZE");
        println!("                        individual components of the SPEC can be omitted");
        println!("                        RESOLUTION can be one of 'fs' (for full screen),");
        println!("                        'WIDTHxHEIGHT' or 'WIDTHxHEIGHTfs'");
    }
    println!("    text                enables the text-based console");
    println!();
    println!("Report bugs to: https://github.com/endbasic/endbasic/issues");
    println!("EndBASIC home page: https://www.endbasic.dev/");
}

/// Prints version information following the GNU Standards format.
fn version() {
    println!("EndBASIC {}", env!("CARGO_PKG_VERSION"));
    println!("Copyright 2020-2022 Julio Merino");
    println!("License Apache Version 2.0 <http://www.apache.org/licenses/LICENSE-2.0>");
}

/// Creates a new EndBASIC machine builder based on the features enabled in this crate.
fn new_machine_builder(console_spec: Option<&str>) -> io::Result<endbasic_std::MachineBuilder> {
    /// Obtains the default set of pins for a Raspberry Pi.
    #[cfg(feature = "rpi")]
    fn add_gpio_pins(builder: endbasic_std::MachineBuilder) -> endbasic_std::MachineBuilder {
        builder.with_gpio_pins(Rc::from(RefCell::from(endbasic_rpi::RppalPins::default())))
    }

    /// Obtains the default set of pins for a platform without GPIO support.
    #[cfg(not(feature = "rpi"))]
    fn add_gpio_pins(builder: endbasic_std::MachineBuilder) -> endbasic_std::MachineBuilder {
        builder
    }

    let signals_chan = async_channel::unbounded();
    let mut builder = endbasic_std::MachineBuilder::default();
    builder = builder.with_console(setup_console(console_spec, signals_chan.0.clone())?);
    builder = builder.with_signals_chan(signals_chan);
    builder = add_gpio_pins(builder);
    Ok(builder)
}

/// Turns a regular machine builder into an interactive builder ensuring common features for all
/// callers.
fn make_interactive(
    builder: endbasic_std::MachineBuilder,
) -> endbasic_std::InteractiveMachineBuilder {
    builder
        .make_interactive()
        .with_program(Rc::from(RefCell::from(endbasic_repl::editor::Editor::default())))
}

/// Completes the build of an interactive machine by taking a partial builder and running post-build
/// steps on it.
///
/// `service_url` is the base URL of the cloud service.
fn finish_interactive_build(
    mut builder: endbasic_std::InteractiveMachineBuilder,
    service_url: &str,
) -> endbasic_core::exec::Result<endbasic_core::exec::Machine> {
    let console = builder.get_console();
    let storage = builder.get_storage();

    let mut machine = builder.build()?;

    let service = Rc::from(RefCell::from(endbasic_client::CloudService::new(service_url)?));
    endbasic_client::add_all(&mut machine, service, console, storage, "https://repl.endbasic.dev/");

    Ok(machine)
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

/// Sets up the console.
fn setup_console(
    console_spec: Option<&str>,
    signals_tx: Sender<Signal>,
) -> io::Result<Rc<RefCell<dyn Console>>> {
    /// Creates the textual console when crossterm support is built in.
    #[cfg(feature = "crossterm")]
    fn setup_text_console(signals_tx: Sender<Signal>) -> io::Result<Rc<RefCell<dyn Console>>> {
        Ok(Rc::from(RefCell::from(endbasic_terminal::TerminalConsole::from_stdio(signals_tx)?)))
    }

    /// Creates the textual console with very basic features when crossterm support is not built in.
    #[cfg(not(feature = "crossterm"))]
    fn setup_text_console(_signals_tx: Sender<Signal>) -> io::Result<Rc<RefCell<dyn Console>>> {
        Ok(Rc::from(RefCell::from(endbasic_std::console::TrivialConsole::default())))
    }

    /// Creates the graphical console when SDL support is built in.
    #[cfg(feature = "sdl")]
    pub fn setup_graphics_console(
        signals_tx: Sender<Signal>,
        spec: &str,
    ) -> io::Result<Rc<RefCell<dyn Console>>> {
        endbasic_sdl::setup(spec, signals_tx)
    }

    /// Errors out during the creation of the graphical console when SDL support is not compiled in.
    #[cfg(not(feature = "sdl"))]
    pub fn setup_graphics_console(
        _signals_tx: Sender<Signal>,
        _spec: &str,
    ) -> io::Result<Rc<RefCell<dyn Console>>> {
        // TODO(jmmv): Make this io::ErrorKind::Unsupported when our MSRV allows it.
        Err(io::Error::new(io::ErrorKind::InvalidInput, "SDL support not compiled in"))
    }

    let console: Rc<RefCell<dyn Console>> = match console_spec {
        None | Some("text") => setup_text_console(signals_tx)?,

        Some("graphics") => setup_graphics_console(signals_tx, "")?,
        Some(text) if text.starts_with("graphics:") => {
            setup_graphics_console(signals_tx, &text["graphics:".len()..])?
        }

        Some(text) => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("Invalid console spec {}", text),
            ))
        }
    };
    Ok(console)
}

/// Sets up the common storage drives.
///
/// This instantiates non-optional drives, such as `MEMORY:` and `DEMOS:`, maps `LOCAL` the
/// location given in `local_drive_spec`.
pub fn setup_storage(storage: &mut Storage, local_drive_spec: &str) -> io::Result<()> {
    storage.register_scheme("demos", Box::from(endbasic_repl::demos::DemoDriveFactory::default()));
    storage.mount("demos", "demos://").expect("Demos drive shouldn't fail to mount");
    storage.register_scheme(
        "file",
        Box::from(endbasic_std::storage::DirectoryDriveFactory::default()),
    );
    storage.mount("local", local_drive_spec)?;
    storage.cd("local:").expect("Local drive was just registered");
    Ok(())
}

/// Enters the interactive interpreter.
///
/// `local_drive` is the optional local drive to mount and use as the default location.
/// `service_url` is the base URL of the cloud service.
async fn run_repl_loop(
    console_spec: Option<&str>,
    local_drive_spec: &str,
    service_url: &str,
) -> endbasic_core::exec::Result<i32> {
    let mut builder = make_interactive(new_machine_builder(console_spec)?);

    let console = builder.get_console();
    let program = builder.get_program();

    let storage = builder.get_storage();
    setup_storage(&mut storage.borrow_mut(), local_drive_spec)?;

    let mut machine = finish_interactive_build(builder, service_url)?;
    endbasic_repl::print_welcome(console.clone())?;
    endbasic_repl::try_load_autoexec(&mut machine, console.clone(), storage).await?;
    Ok(endbasic_repl::run_repl_loop(&mut machine, console, program).await?)
}

/// Executes the `path` program in a fresh machine.
async fn run_script<P: AsRef<Path>>(
    path: P,
    console_spec: Option<&str>,
) -> endbasic_core::exec::Result<i32> {
    let mut machine = new_machine_builder(console_spec)?.build()?;
    let mut input = File::open(path)?;
    Ok(machine.exec(&mut input).await?.as_exit_code())
}

/// Executes the `path` program in a fresh machine allowing any interactive-only calls.
///
/// `local_drive` is the optional local drive to mount and use as the default location.
/// `service_url` is the base URL of the cloud service.
///
/// If `path` starts with `cloud://`, this uses the same auto-run features that the web UI
/// exposes.  The presence of this here is kind of a hack but avoids having too much logic
/// just in the web and helps test this feature.
async fn run_interactive(
    path: &str,
    console_spec: Option<&str>,
    local_drive_spec: &str,
    service_url: &str,
) -> endbasic_core::exec::Result<i32> {
    let mut builder = make_interactive(new_machine_builder(console_spec)?);

    let console = builder.get_console();
    let program = builder.get_program();

    let storage = builder.get_storage();
    setup_storage(&mut storage.borrow_mut(), local_drive_spec)?;

    let mut machine = finish_interactive_build(builder, service_url)?;

    match path.strip_prefix("cloud://") {
        Some(username_path) => {
            endbasic_repl::run_from_cloud(
                &mut machine,
                console.clone(),
                storage.clone(),
                program.clone(),
                username_path,
                false,
            )
            .await
        }
        None => {
            let mut input = File::open(path)?;
            Ok(machine.exec(&mut input).await?.as_exit_code())
        }
    }
}

/// Version of `main` that returns errors to the caller for reporting.
async fn safe_main(name: &str, args: env::Args) -> Result<i32> {
    let args: Vec<String> = args.collect();

    let mut opts = Options::new();
    opts.optopt("", "console", "type and properties of the console to use", "CONSOLE-SPEC");
    opts.optflag("h", "help", "show command-line usage information and exit");
    opts.optflag("i", "interactive", "force interactive mode when running a script");
    opts.optopt("", "local-drive", "location of the drive to mount as LOCAL", "URI");
    opts.optopt("", "service-url", "base URL of the cloud service", "URL");
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

    let console_spec = matches.opt_str("console");

    let service_url = matches
        .opt_str("service-url")
        .unwrap_or_else(|| endbasic_client::PROD_API_ADDRESS.to_owned());

    match matches.free.as_slice() {
        [] => {
            let local_drive = get_local_drive_spec(matches.opt_str("local-drive"))?;
            Ok(run_repl_loop(console_spec.as_deref(), &local_drive, &service_url).await?)
        }
        [file] => {
            if matches.opt_present("interactive") {
                let local_drive = get_local_drive_spec(matches.opt_str("local-drive"))?;
                Ok(run_interactive(file, console_spec.as_deref(), &local_drive, &service_url)
                    .await?)
            } else {
                Ok(run_script(file, console_spec.as_deref()).await?)
            }
        }
        [_, ..] => Err(UsageError::new("Too many arguments").into()),
    }
}

#[tokio::main]
async fn main() {
    let (name, args) = program_name(env::args(), "endbasic");
    let exit_code = match safe_main(&name, args).await {
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
