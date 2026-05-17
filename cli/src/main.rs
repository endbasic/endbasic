// EndBASIC
// Copyright 2020 Julio Merino
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

//! Command-line interface for the EndBASIC language.

use anyhow::{Result, anyhow};
use async_channel::Sender;
use endbasic_client::CloudService;
use endbasic_repl::demos::DemoDriveFactory;
use endbasic_std::console::{Console, ConsoleSpec};
use endbasic_std::storage::{DirectoryDriveFactory, Storage};
use endbasic_std::{Error as StdError, MachineBuilder, Signal, gpio};
use getoptsargs::prelude::*;
use std::cell::RefCell;
use std::fs::File;
use std::io;
use std::path::Path;
use std::rc::Rc;

/// Prints extra usage information into `o`.
fn app_extra_help(o: &mut dyn io::Write) -> io::Result<()> {
    writeln!(o, "CONSOLE-SPEC can be one of the following:")?;
    if cfg!(feature = "sdl") {
        writeln!(o, "    sdl[:SPEC]          enables the graphical console and configures it")?;
        writeln!(o, "                        with the settings in SPEC, which is of the form:")?;
        writeln!(
            o,
            "                        resolution=RESOLUTION,fg_color=COLOR,bg_color=COLOR,"
        )?;
        writeln!(o, "                        font_path=TTF,font_size=SIZE")?;
        writeln!(o, "                        individual components of the SPEC can be omitted")?;
        writeln!(o, "                        RESOLUTION can be one of 'fs' (for full screen),")?;
        writeln!(o, "                        'WIDTHxHEIGHT' or 'WIDTHxHEIGHTfs'")?;
    }
    if cfg!(feature = "rpi") {
        writeln!(o, "    st7735s[:SPEC]      enables the ST7735S LCD console and configures it")?;
        writeln!(o, "                        with the settings in SPEC, which is of the form:")?;
        writeln!(o, "                        fg_color=COLOR,bg_color=COLOR,font=NAME")?;
    }
    writeln!(o, "    text                enables the text-based console")?;
    writeln!(o)?;
    writeln!(o, "GPIO-PINS-SPEC can be one of the following:")?;
    writeln!(o, "    mock                mock backend for testing")?;
    writeln!(o, "    noop                dummy backend that always returns errors")?;
    if cfg!(feature = "rpi") {
        writeln!(o, "    rppal               uses the Raspberry Pi GPIO hardware")?;
    }
    Ok(())
}

/// Creates the rppal GPIO backend when the rpi feature is compiled in.
#[cfg(feature = "rpi")]
fn setup_gpio_pins_rppal() -> Result<Rc<RefCell<dyn gpio::Pins>>> {
    Ok(Rc::new(RefCell::new(endbasic_rpi::RppalPins::default())))
}

/// Errors out for rppal when the rpi feature is not compiled in.
#[cfg(not(feature = "rpi"))]
fn setup_gpio_pins_rppal() -> Result<Rc<RefCell<dyn gpio::Pins>>> {
    Err(bad_usage!("--gpio-pins=rppal requires the rpi feature to be compiled in").into())
}

/// Parses the `--gpio-pins` flag value and constructs the pins backend.
fn setup_gpio_pins(spec: Option<&str>) -> Result<Rc<RefCell<dyn gpio::Pins>>> {
    let spec = if cfg!(feature = "rpi") { spec.unwrap_or("rppal") } else { spec.unwrap_or("noop") };
    match spec {
        "mock" => Ok(Rc::new(RefCell::new(gpio::MockPins::default()))),
        "noop" => Ok(Rc::new(RefCell::new(gpio::NoopPins::default()))),
        "rppal" => setup_gpio_pins_rppal(),
        other => Err(bad_usage!(format!("Unknown --gpio-pins backend: {}", other)).into()),
    }
}

/// Creates a new EndBASIC machine builder based on the features enabled in this crate.
fn new_machine_builder(
    console_spec: Option<&str>,
    gpio_pins_spec: Option<&str>,
) -> Result<MachineBuilder> {
    let signals_chan = async_channel::unbounded();
    let mut builder = MachineBuilder::default();
    builder = builder.with_console(setup_console(console_spec, signals_chan.0.clone())?);
    builder = builder.with_signals_chan(signals_chan);
    builder = builder.with_gpio_pins(setup_gpio_pins(gpio_pins_spec)?);
    Ok(builder)
}

const INTERRUPTED_EXIT_CODE: i32 = 130;

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
    pub fn setup_sdl_console(
        signals_tx: Sender<Signal>,
        spec: &mut ConsoleSpec,
    ) -> io::Result<Rc<RefCell<dyn Console>>> {
        endbasic_sdl::setup(spec, &endbasic_std::gfx::lcd::fonts::Fonts::all(), signals_tx)
    }

    /// Errors out during the creation of the graphical console when SDL support is not compiled in.
    #[cfg(not(feature = "sdl"))]
    pub fn setup_sdl_console(
        _signals_tx: Sender<Signal>,
        _spec: &mut ConsoleSpec,
    ) -> io::Result<Rc<RefCell<dyn Console>>> {
        // TODO(jmmv): Make this io::ErrorKind::Unsupported when our MSRV allows it.
        Err(io::Error::new(io::ErrorKind::InvalidInput, "SDL support not compiled in"))
    }

    #[cfg(feature = "rpi")]
    fn setup_st7735s_console(
        signals_tx: Sender<Signal>,
        spec: &mut ConsoleSpec,
    ) -> io::Result<Rc<RefCell<dyn Console>>> {
        let console = endbasic_st7735s::new_console(
            endbasic_rpi::RppalPins::default(),
            endbasic_rpi::spi_bus_open,
            endbasic_terminal::TerminalConsole::from_stdio(signals_tx)?,
            spec,
            &endbasic_std::gfx::lcd::fonts::Fonts::all(),
        )?;
        Ok(Rc::from(RefCell::from(console)))
    }

    #[cfg(not(feature = "rpi"))]
    pub fn setup_st7735s_console(
        _signals_tx: Sender<Signal>,
        _spec: &mut ConsoleSpec,
    ) -> io::Result<Rc<RefCell<dyn Console>>> {
        Err(io::Error::new(io::ErrorKind::InvalidInput, "ST7735S support not compiled in"))
    }

    let mut console_spec = ConsoleSpec::init(console_spec.unwrap_or("text"));
    let console: Rc<RefCell<dyn Console>> = match console_spec.driver {
        "sdl" => setup_sdl_console(signals_tx, &mut console_spec)?,
        "st7735s" => setup_st7735s_console(signals_tx, &mut console_spec)?,
        "text" => setup_text_console(signals_tx)?,
        driver => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("Unknown console driver {}", driver),
            ));
        }
    };
    console_spec.finish().map_err(|e| {
        io::Error::new(io::ErrorKind::InvalidInput, format!("Invalid --console flag: {}", e))
    })?;
    Ok(console)
}

/// Sets up the common storage drives.
///
/// This instantiates non-optional drives, such as `MEMORY:` and `DEMOS:`, maps `LOCAL` the
/// location given in `local_drive_spec`.
pub fn setup_storage(storage: &mut Storage, local_drive_spec: &str) -> io::Result<()> {
    storage.register_scheme("demos", Box::from(DemoDriveFactory::default()));
    storage.mount("demos", "demos://").expect("Demos drive shouldn't fail to mount");
    storage.register_scheme("file", Box::from(DirectoryDriveFactory::default()));
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
    gpio_pins_spec: Option<&str>,
    local_drive_spec: &str,
    service_url: &str,
) -> Result<i32> {
    let mut builder = new_machine_builder(console_spec, gpio_pins_spec)?;
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
async fn run_script<P: AsRef<Path>>(
    path: P,
    console_spec: Option<&str>,
    gpio_pins_spec: Option<&str>,
) -> Result<i32> {
    let builder = new_machine_builder(console_spec, gpio_pins_spec)?;
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
async fn run_interactive(
    path: &str,
    console_spec: Option<&str>,
    gpio_pins_spec: Option<&str>,
    local_drive_spec: &str,
    service_url: &str,
) -> Result<i32> {
    let mut builder = new_machine_builder(console_spec, gpio_pins_spec)?;
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

fn app_build(builder: Builder) -> Builder {
    builder
        .copyright("Copyright 2020-2026 Julio Merino")
        .license(License::AGPL3OrLater)
        .homepage("https://www.endbasic.dev/")
        .bugs("https://github.com/endbasic/endbasic/issues")
        .optopt("", "console", "type and properties of the console to use", "CONSOLE-SPEC")
        .optopt("", "gpio-pins", "GPIO pins backend to use", "GPIO-PINS-SPEC")
        .optflag("i", "interactive", "force interactive mode when running a script")
        .optopt("", "local-drive", "location of the drive to mount as LOCAL", "URI")
        .optopt("", "service-url", "base URL of the cloud service", "URL")
        .trailarg("program-file", 0, 1, "script to execute without entering interactive mode")
        .extra_help(app_extra_help)
}

async fn app_main(matches: Matches) -> Result<i32> {
    let console_spec = matches.opt_str("console");

    let gpio_pins_spec = matches.opt_str("gpio-pins");

    let service_url = matches
        .opt_str("service-url")
        .unwrap_or_else(|| endbasic_client::PROD_API_ADDRESS.to_owned());

    match matches.arg_trail() {
        [] => {
            let local_drive = get_local_drive_spec(matches.opt_str("local-drive"))?;
            Ok(run_repl_loop(
                console_spec.as_deref(),
                gpio_pins_spec.as_deref(),
                &local_drive,
                &service_url,
            )
            .await?)
        }
        [file] => {
            if matches.opt_present("interactive") {
                let local_drive = get_local_drive_spec(matches.opt_str("local-drive"))?;
                Ok(run_interactive(
                    file,
                    console_spec.as_deref(),
                    gpio_pins_spec.as_deref(),
                    &local_drive,
                    &service_url,
                )
                .await?)
            } else {
                Ok(run_script(file, console_spec.as_deref(), gpio_pins_spec.as_deref()).await?)
            }
        }
        [_, ..] => Err(bad_usage!("Too many arguments").into()),
    }
}

tokio_app!("EndBASIC", app_build, app_main);
