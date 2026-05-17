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

use endbasic::*;
use getoptsargs::prelude::*;
use std::io;
use std::thread;

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

fn app_main(matches: Matches) -> Result<i32> {
    let console_spec = matches.opt_str("console");

    let gpio_pins_spec = matches.opt_str("gpio-pins");

    let service_url = matches
        .opt_str("service-url")
        .unwrap_or_else(|| endbasic_client::PROD_API_ADDRESS.to_owned());

    let console_factory = setup_console(console_spec.as_deref())?;

    let app_mode = AppMode::from_matches(matches)?;

    let interpreter = thread::spawn(move || -> Result<i32> {
        let runtime = tokio::runtime::Runtime::new()?;
        runtime.block_on(async move {
            async_app_main(app_mode, console_factory, gpio_pins_spec, service_url).await
        })
    });

    interpreter.join().expect("Interpreter thread shoult not have panicked")
}

app!("EndBASIC", app_build, app_main);
