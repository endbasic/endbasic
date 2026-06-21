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

//! Web Audio-backed tone playback.

use crate::canvas::js_value_to_io_error;
use crate::datetime::do_sleep;
use async_trait::async_trait;
use endbasic_std::sound::{AudioOps, Tone, Waveform};
use std::convert::TryFrom;
use std::io;
use web_sys::{AudioContext, OscillatorType};

/// Implementation of `AudioOps` via the Web Audio API.
pub(crate) struct WebAudioOps {
    context: AudioContext,
}

impl WebAudioOps {
    /// Creates a new reusable Web Audio backend.
    pub(crate) fn new() -> io::Result<Self> {
        let context = AudioContext::new().map_err(js_value_to_io_error)?;
        Ok(Self { context })
    }
}

#[async_trait(?Send)]
impl AudioOps for WebAudioOps {
    async fn play_tone(&mut self, tone: Tone) -> io::Result<()> {
        if tone.frequency_hz == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Tone frequency must be positive",
            ));
        }

        // Oscillators are one-shot nodes in the Web Audio API, so we must create one per tone.
        let oscillator = self.context.create_oscillator().map_err(js_value_to_io_error)?;
        oscillator.frequency().set_value(tone.frequency_hz as f32);
        oscillator.set_type(match tone.waveform {
            Waveform::Square => OscillatorType::Square,
        });
        oscillator
            .connect_with_audio_node(&self.context.destination())
            .map_err(js_value_to_io_error)?;
        oscillator.start().map_err(js_value_to_io_error)?;

        let ms = i32::try_from(tone.duration.as_millis())
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "Tone duration too long"))?;
        do_sleep(ms, ()).await;

        oscillator.stop().map_err(js_value_to_io_error)?;
        Ok(())
    }
}
