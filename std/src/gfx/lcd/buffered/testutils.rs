// EndBASIC
// Copyright 2024 Julio Merino
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

//! Utilities to implement tests for the `BufferedLcd`.

use crate::console::RGB;
use crate::gfx::lcd::fonts::FONT_5X8;
use crate::gfx::lcd::{AsByteSlice, BufferedLcd, Lcd, LcdSize, LcdXY};
use std::io;

/// Data for one pixel encoded as RGB888.
#[cfg(test)]
#[derive(Clone, Copy)]
pub(super) struct RGB888Pixel(pub(super) [u8; 3]);

#[cfg(test)]
impl AsByteSlice for RGB888Pixel {
    fn as_slice(&self) -> &[u8] {
        &self.0
    }
}

/// Syntactic sugar to instantiate a coordinate in the LCD space.
pub(super) fn xy(x: usize, y: usize) -> LcdXY {
    LcdXY { x, y }
}

/// Syntactic sugar to instantiate a size in the LCD space.
pub(super) fn size(width: usize, height: usize) -> LcdSize {
    LcdSize { width, height }
}

/// Mock LCD that captures rendering operations.
///
/// Fo simplicity, the pixel data is encoded as three separate RGB `u8` values.
pub(super) struct LcdRecorder {
    size: LcdSize,
    ops: Vec<String>,
}

impl LcdRecorder {
    /// Creates a mock LCD of the given `size`.
    pub(crate) fn new(size: LcdSize) -> Self {
        Self { size, ops: vec![] }
    }
}

impl Lcd for LcdRecorder {
    type Pixel = RGB888Pixel;

    fn info(&self) -> (LcdSize, usize) {
        (self.size, 3)
    }

    fn encode(&self, rgb: RGB) -> Self::Pixel {
        RGB888Pixel([rgb.0, rgb.1, rgb.2])
    }

    fn set_data(&mut self, x1y1: LcdXY, x2y2: LcdXY, data: &[u8]) -> io::Result<()> {
        self.ops.push(format!(
            "set_data: from=({}, {}), to=({}, {}), data={:?}",
            x1y1.x, x1y1.y, x2y2.x, x2y2.y, data
        ));
        Ok(())
    }
}

/// Builder pattern to define and execute `BufferedLcd` tests.
#[must_use]
pub(super) struct Tester {
    size: LcdSize,
    buffered: BufferedLcd<LcdRecorder>,
    exp_fb: Vec<u8>,
    exp_damage: Option<(LcdXY, LcdXY)>,
    exp_ops: Vec<String>,
}

impl Tester {
    /// Creates a new tester backed by a mock `LcdRecorder` of the given `size`.
    pub(super) fn new(size: LcdSize) -> Self {
        let fb_size = size.width * size.height * 3;
        Self {
            size,
            buffered: BufferedLcd::new(LcdRecorder::new(size), &FONT_5X8),
            exp_fb: vec![0; fb_size],
            exp_damage: None,
            exp_ops: vec![],
        }
    }

    /// Executes an operation on the backing `LcdRecorder`.
    pub(super) fn op<F>(mut self, op: F) -> Self
    where
        F: Fn(&mut BufferedLcd<LcdRecorder>),
    {
        op(&mut self.buffered);
        self
    }

    /// Records that the pixel `xy` should be `rgb` after all `op`s have been executed.
    pub(super) fn expect_pixel(mut self, xy: LcdXY, rgb: RGB) -> Self {
        let offset = ((xy.y * self.size.width) + xy.x) * 3;
        self.exp_fb[offset] = rgb.0;
        self.exp_fb[offset + 1] = rgb.1;
        self.exp_fb[offset + 2] = rgb.2;
        self
    }

    /// Records that the area between `x1y1` and `x2y2` is damaged after all `op`s have been
    /// executed.
    pub(super) fn expect_damage(mut self, x1y1: LcdXY, x2y2: LcdXY) -> Self {
        assert!(self.exp_damage.is_none());
        self.exp_damage = Some((x1y1, x2y2));
        self
    }

    /// Records that the given `op` should have been received by the mock `LcdRecorder` after
    /// all `op`s have been executed.
    pub(super) fn expect_op(mut self, op: &str) -> Self {
        self.exp_ops.push(op.into());
        self
    }

    /// Configures the test to ignore the content of all pixels.  This is for simplicity of
    /// tests that only one to validate other aspects of the LCD handling.
    pub(super) fn ignore_pixels(mut self) -> Self {
        self.exp_fb = self.buffered.fb.clone();
        self
    }

    /// Validates recorded expectations about the changes made by all executed `op`s.
    pub(super) fn check(self) {
        if self.exp_fb != self.buffered.fb {
            for y in 0..self.size.height {
                for x in 0..self.size.width {
                    let offset = (y * self.size.width + x) * 3;
                    let exp_pixel = &self.exp_fb[offset..offset + 3];
                    let pixel = &self.buffered.fb[offset..offset + 3];
                    if exp_pixel != pixel {
                        // Print the difference as a bunch of expect_pixel lines that can be
                        // copy-pasted into the code to re-define golden data.
                        eprintln!(
                                ".expect_pixel(xy({:3}, {:3}), ({:3}, {:3}, {:3}))  // got ({:3}, {:3}, {:3})",
                                x, y,
                                pixel[0], pixel[1], pixel[2],
                                exp_pixel[0], exp_pixel[1], exp_pixel[2],
                            );
                    }
                }
            }
            panic!("Pixel contents differ; see output above");
        }
        assert_eq!(self.exp_damage, self.buffered.damage);
        assert_eq!(self.exp_ops, self.buffered.lcd.ops);
    }
}
