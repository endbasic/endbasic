// EndBASIC
// Copyright 2026 Julio Merino
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

//! Supporting code for EndBASIC's CLI.

use anyhow::Result;
use endbasic_client::CloudService;
use endbasic_std::console::ConsoleFactory;
use endbasic_std::storage::Storage;
use endbasic_std::{Error as StdError, MachineBuilder};
use getoptsargs::prelude::*;
use std::cell::RefCell;
use std::fs::File;
use std::path::Path;
use std::rc::Rc;

mod console;
pub use console::setup_console;

mod gpio;
use gpio::setup_gpio_pins;

mod storage;
use storage::{get_local_drive_spec, setup_storage};

/// Exit code representing `SIGINT` following shell semantics.
const INTERRUPTED_EXIT_CODE: i32 = 128 + 2;

/// Creates a new EndBASIC machine builder based on the features enabled in this crate.
fn new_machine_builder(
    console_factory: Box<dyn ConsoleFactory>,
    gpio_pins_spec: Option<&str>,
) -> Result<MachineBuilder> {
    let signals_chan = async_channel::unbounded();
    let console = console_factory.build(signals_chan.0.clone())?;
    let mut builder = MachineBuilder::default();
    builder = builder.with_console(console);
    builder = builder.with_signals_chan(signals_chan);
    builder = builder.with_gpio_pins(setup_gpio_pins(gpio_pins_spec)?);
    Ok(builder)
}

/// Enters the interactive interpreter.
///
/// `local_drive` is the optional local drive to mount and use as the default location.
/// `service_url` is the base URL of the cloud service.
pub async fn run_repl_loop(
    console_factory: Box<dyn ConsoleFactory>,
    gpio_pins_spec: Option<&str>,
    local_drive_spec: &str,
    service_url: &str,
) -> Result<i32> {
    let mut builder = new_machine_builder(console_factory, gpio_pins_spec)?;
    let console = builder.get_console();
    let program = Rc::from(RefCell::from(endbasic_repl::editor::Editor::default()));
    let storage = Rc::from(RefCell::from(Storage::default()));
    setup_storage(&mut storage.borrow_mut(), local_drive_spec)?;

    let service = Rc::from(RefCell::from(CloudService::new(service_url)?));
    endbasic_client::add_all(
        &mut builder,
        service,
        console.clone(),
        storage.clone(),
        "https://repl.endbasic.dev/",
    );

    let mut machine = builder
        .make_interactive()
        .with_program(program.clone())
        .with_storage(storage.clone())
        .build();
    endbasic_repl::print_welcome(console.clone())?;
    endbasic_repl::try_load_autoexec(&mut machine, console.clone(), storage).await?;
    Ok(endbasic_repl::run_repl_loop(&mut machine, console, program).await?)
}

/// Executes the `path` program in a fresh machine.
pub async fn run_script<P: AsRef<Path>>(
    path: P,
    console_factory: Box<dyn ConsoleFactory>,
    gpio_pins_spec: Option<&str>,
) -> Result<i32> {
    let builder = new_machine_builder(console_factory, gpio_pins_spec)?;
    let mut machine = builder.build();
    let mut input = File::open(path)?;

    machine.compile(&mut input)?;
    match machine.exec().await {
        Ok(Some(code)) => Ok(code),
        Ok(None) => Ok(0),
        Err(StdError::Break) => Ok(INTERRUPTED_EXIT_CODE),
        Err(e) => Err(e.into()),
    }
}

/// Executes the `path` program in a fresh machine allowing any interactive-only calls.
///
/// `local_drive` is the optional local drive to mount and use as the default location.
/// `service_url` is the base URL of the cloud service.
///
/// If `path` starts with `cloud://`, this uses the same auto-run features that the web UI
/// exposes.  The presence of this here is kind of a hack but avoids having too much logic
/// just in the web and helps test this feature.
pub async fn run_interactive(
    path: &str,
    console_factory: Box<dyn ConsoleFactory>,
    gpio_pins_spec: Option<&str>,
    local_drive_spec: &str,
    service_url: &str,
) -> Result<i32> {
    let mut builder = new_machine_builder(console_factory, gpio_pins_spec)?;
    let console = builder.get_console();
    let program = Rc::from(RefCell::from(endbasic_repl::editor::Editor::default()));
    let storage = Rc::from(RefCell::from(Storage::default()));
    setup_storage(&mut storage.borrow_mut(), local_drive_spec)?;

    let service = Rc::from(RefCell::from(CloudService::new(service_url)?));
    endbasic_client::add_all(
        &mut builder,
        service,
        console.clone(),
        storage.clone(),
        "https://repl.endbasic.dev/",
    );

    let mut machine = builder
        .make_interactive()
        .with_program(program.clone())
        .with_storage(storage.clone())
        .build();

    match path.strip_prefix("cloud://") {
        Some(username_path) => {
            let code = endbasic_repl::run_from_cloud(
                &mut machine,
                console.clone(),
                storage.clone(),
                program.clone(),
                username_path,
                false,
            )
            .await?;
            Ok(code)
        }
        None => {
            let mut input = File::open(path)?;
            machine.compile(&mut input)?;
            match machine.exec().await {
                Ok(Some(code)) => Ok(code),
                Ok(None) => Ok(0),
                Err(StdError::Break) => Ok(INTERRUPTED_EXIT_CODE),
                Err(e) => Err(e.into()),
            }
        }
    }
}

/// Representation of the CLI execution mode and the arguments required for each.
pub enum AppMode {
    /// Enter the REPL.
    ///
    /// The first argument contains the local drive spec.
    Repl(String),

    /// Run a file as if it had invoked in a REPL context.
    ///
    /// The first argument contains the file to run and the second argument contains the local
    /// drive spec.
    RunInteractive(String, String),

    /// Run a file in scripting mode.
    ///
    /// The first argument contains the file to run.
    RunScript(String),
}

impl AppMode {
    /// Determines the app mode by parsing the remainder of `matches`.
    pub fn from_matches(matches: Matches) -> Result<AppMode> {
        match matches.arg_trail() {
            [] => {
                let local_drive = get_local_drive_spec(matches.opt_str("local-drive"))?;
                Ok(AppMode::Repl(local_drive))
            }
            [file] => {
                if matches.opt_present("interactive") {
                    let local_drive = get_local_drive_spec(matches.opt_str("local-drive"))?;
                    Ok(AppMode::RunInteractive((*file).to_owned(), local_drive))
                } else {
                    Ok(AppMode::RunScript((*file).to_owned()))
                }
            }
            [_, ..] => Err(bad_usage!("Too many arguments").into()),
        }
    }
}

/// Runs the EndBASIC CLI depending on the provided `app_mode`.
pub async fn async_app_main(
    app_mode: AppMode,
    console_factory: Box<dyn ConsoleFactory>,
    gpio_pins_spec: Option<String>,
    service_url: String,
) -> Result<i32> {
    match app_mode {
        AppMode::Repl(local_drive) => Ok(run_repl_loop(
            console_factory,
            gpio_pins_spec.as_deref(),
            &local_drive,
            &service_url,
        )
        .await?),
        AppMode::RunInteractive(file, local_drive) => Ok(run_interactive(
            &file,
            console_factory,
            gpio_pins_spec.as_deref(),
            &local_drive,
            &service_url,
        )
        .await?),
        AppMode::RunScript(file) => {
            Ok(run_script(file, console_factory, gpio_pins_spec.as_deref()).await?)
        }
    }
}
