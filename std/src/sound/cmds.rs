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

//! Commands for sound playback.

use crate::MachineBuilder;
use crate::console::Console;
use crate::sound::Tone;
use async_trait::async_trait;
use endbasic_core::{
    ArgSep, ArgSepSyntax, CallError, CallResult, Callable, CallableMetadata,
    CallableMetadataBuilder, ExprType, RequiredValueSyntax, Scope, SingularArgSyntax,
};
use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;
use std::time::Duration;

/// Category description for all symbols provided by this module.
const CATEGORY: &str = "Sound

The EndBASIC console supports sound playback.";

/// The `BEEP` command.
pub struct BeepCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
}

impl BeepCommand {
    /// Creates a new `BEEP` command that reproduces a canned tone on the `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("BEEP")
                .with_async(true)
                .with_syntax(&[(&[], None)])
                .with_category(CATEGORY)
                .with_description(
                    "Reproduces a short audible tone.
This command plays a square-wave tone at 800 hertz for 0.25 seconds in consoles that \
support sound.  Otherwise, this falls back to a BEL control code that should match this \
pitch and duration, but it may not.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Callable for BeepCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn async_exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(0, scope.nargs());
        self.console.borrow_mut().beep().await?;
        Ok(())
    }
}

/// The `SOUND` command.
pub struct SoundCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
}

impl SoundCommand {
    /// Creates a new `SOUND` command that reproduces arbitrary tones on the `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("SOUND")
                .with_async(true)
                .with_syntax(&[(
                    &[
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("pitch"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("duration"),
                                vtype: ExprType::Double,
                            },
                            ArgSepSyntax::End,
                        ),
                    ],
                    None,
                )])
                .with_category(CATEGORY)
                .with_description(
                    "Reproduces a tone with the given pitch and duration.
The pitch is specified in hertz and must be positive.  The duration is specified in seconds and \
must be zero or positive.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Callable for SoundCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn async_exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(2, scope.nargs());

        let pitch = scope.get_integer(0);
        if pitch <= 0 {
            return Err(CallError::Syntax(scope.get_pos(0), "Pitch must be positive".to_owned()));
        }
        let pitch = pitch as u32;

        let duration = scope.get_double(1);
        if duration < 0.0 {
            return Err(CallError::Syntax(
                scope.get_pos(1),
                "Duration must be positive".to_owned(),
            ));
        }

        self.console
            .borrow_mut()
            .play_tone(Tone::square(pitch, Duration::from_secs_f64(duration)))
            .await?;
        Ok(())
    }
}

/// Adds all console-related commands for the given `console` to the `machine`.
pub fn add_all(machine: &mut MachineBuilder, console: Rc<RefCell<dyn Console>>) {
    machine.add_callable(BeepCommand::new(console.clone()));
    machine.add_callable(SoundCommand::new(console));
}

#[cfg(test)]
mod tests {
    use crate::sound::{BEEP_TONE, Tone};
    use crate::testutils::*;
    use std::time::Duration;

    #[test]
    fn test_beep_ok() {
        Tester::default().run("BEEP").expect_output([CapturedOut::PlayTone(BEEP_TONE)]).check();
    }

    #[test]
    fn test_beep_errors() {
        check_stmt_compilation_err("1:1: BEEP expected no arguments", "BEEP 1");
    }

    #[test]
    fn test_sound_ok() {
        Tester::default()
            .run("SOUND 440, 1.5")
            .expect_output([CapturedOut::PlayTone(Tone::square(440, Duration::from_millis(1500)))])
            .check();

        Tester::default()
            .run("SOUND 440, 0")
            .expect_output([CapturedOut::PlayTone(Tone::square(440, Duration::from_secs(0)))])
            .check();
    }

    #[test]
    fn test_sound_errors() {
        check_stmt_compilation_err("1:1: SOUND expected pitch%, duration#", "SOUND");
        check_stmt_compilation_err("1:1: SOUND expected pitch%, duration#", "SOUND 1");
        check_stmt_compilation_err("1:1: SOUND expected pitch%, duration#", "SOUND 1, 2, 3");
        check_stmt_compilation_err("1:8: SOUND expected pitch%, duration#", "SOUND 1; 2");

        check_stmt_compilation_err("1:7: BOOLEAN is not a number", "SOUND TRUE, 1");
        check_stmt_compilation_err("1:10: BOOLEAN is not a number", "SOUND 1, TRUE");

        check_stmt_err("1:7: Pitch must be positive", "SOUND 0, 1");
        check_stmt_err("1:7: Pitch must be positive", "SOUND -1, 1");
        check_stmt_err("1:10: Duration must be positive", "SOUND 1, -1");
    }
}
