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

//! Sound manipulation for the EndBASIC console.

use async_trait::async_trait;
use std::io;
use std::time::Duration;

pub(super) mod cmds;

/// Default tone for the `beep` primitive.
// If modifying this, don't forget to update the `BeepCommand` docstring.
pub const BEEP_TONE: Tone = Tone::square(800, Duration::from_millis(250));

/// Waveform to use when reproducing a tone.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Waveform {
    /// Square wave.
    Square,
}

/// Description of a tone to reproduce.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Tone {
    /// Frequency of the tone in hertz.
    pub frequency_hz: u32,

    /// Duration of the tone.
    pub duration: Duration,

    /// Waveform of the tone.
    pub waveform: Waveform,
}

impl Tone {
    /// Constructs a square-wave tone.
    pub const fn square(frequency_hz: u32, duration: Duration) -> Self {
        Self { frequency_hz, duration, waveform: Waveform::Square }
    }
}

/// Primitive audio operations.
#[async_trait(?Send)]
pub trait AudioOps {
    /// Reproduces `tone` and returns once playback completes.
    async fn play_tone(&mut self, tone: Tone) -> io::Result<()>;
}

/// Audio backend that always reports the feature as unsupported.
pub struct NoopAudioOps;

#[async_trait(?Send)]
impl AudioOps for NoopAudioOps {
    async fn play_tone(&mut self, _tone: Tone) -> io::Result<()> {
        Err(io::Error::other("No audio support in this console"))
    }
}
