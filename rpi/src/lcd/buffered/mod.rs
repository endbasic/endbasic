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

//! Buffered implementation of the `RasterOps` for a hardware LCD.

use crate::lcd::font8;
use crate::lcd::{to_xy_size, Lcd, LcdSize, LcdXY};
use endbasic_std::console::graphics::{RasterInfo, RasterOps};
use endbasic_std::console::{CharsXY, PixelsXY, SizeInPixels, RGB};
use std::convert::TryFrom;
use std::io;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod testutils;

/// Implements buffering for a backing slow LCD `L`.
///
/// All drawing operations are saved to a memory-backed framebuffer.  If syncing is enabled, drawing
/// primitives are flushed right away to the device; otherwise, they are applied to memory only
/// until an explicit sync is requested.  The framebuffer is also used to implement all pixel data
/// reading.
pub(crate) struct BufferedLcd<L: Lcd> {
    lcd: L,

    fb: Vec<u8>,
    stride: usize,
    sync: bool,
    damage: Option<(LcdXY, LcdXY)>,

    size_pixels: LcdSize,
    glyph_size: LcdSize,
    size_chars: CharsXY,
}

impl<L> BufferedLcd<L>
where
    L: Lcd,
{
    /// Creates a new buffered LCD backed by `lcd`.
    pub(crate) fn new(lcd: L) -> Self {
        let (size, stride) = lcd.info();

        let fb = {
            let pixels = size.width * size.height;
            vec![0; pixels * stride]
        };

        let glyph_size = LcdSize { width: font8::WIDTH, height: font8::HEIGHT };
        let size_chars = CharsXY::new(
            u16::try_from(size.width / glyph_size.width).expect("Must fit"),
            u16::try_from(size.height / glyph_size.height).expect("Must fit"),
        );

        Self {
            lcd,
            fb,
            stride,
            sync: true,
            damage: None,
            size_pixels: size,
            glyph_size,
            size_chars,
        }
    }

    /// Executes mutations on the buffered LCD via `ops` while ensuring that syncing is disabled.
    fn without_sync<F>(&mut self, ops: F) -> io::Result<()>
    where
        F: Fn(&mut BufferedLcd<L>) -> io::Result<()>,
    {
        if self.sync {
            let old_sync = self.sync;
            self.sync = false;

            let result = ops(self);

            self.sync = old_sync;
            if self.sync {
                self.force_present_canvas()?;
            }

            result
        } else {
            ops(self)
        }
    }

    /// Clips the user-supplied `xy` coordinates to the LCD space.  Returns `None` if they are out
    /// of range and the converted value otherwise.
    fn clip_xy(&self, xy: PixelsXY) -> Option<LcdXY> {
        fn clamp(value: i16, max: usize) -> Option<usize> {
            if value < 0 {
                None
            } else {
                let value = usize::try_from(value).expect("Positive value must fit");
                if value > max {
                    None
                } else {
                    Some(value)
                }
            }
        }

        let x = clamp(xy.x, self.size_pixels.width - 1);
        let y = clamp(xy.y, self.size_pixels.height - 1);
        match (x, y) {
            (Some(x), Some(y)) => Some(LcdXY { x, y }),
            _ => None,
        }
    }

    /// Clamps the user-supplied `xy` coordinates to the LCD space.
    fn clamp_xy(&self, xy: PixelsXY) -> LcdXY {
        fn clamp(value: i16, max: usize) -> usize {
            if value < 0 {
                0
            } else {
                let value = usize::try_from(value).expect("Positive value must fit");
                if value > max {
                    max
                } else {
                    value
                }
            }
        }

        LcdXY {
            x: clamp(xy.x, self.size_pixels.width - 1),
            y: clamp(xy.y, self.size_pixels.height - 1),
        }
    }

    /// Given a top-left `xy` coordinate, adds the user-supplied `size` to it and clamps the result
    /// to the LCD space.
    fn clip_x2y2(&self, xy: PixelsXY, size: SizeInPixels) -> Option<LcdXY> {
        fn clamp(value: i16, delta: u16, max: usize) -> Option<usize> {
            let value = i32::from(value);
            let delta = i32::from(delta);

            let value = value + delta;
            if value < 0 {
                None
            } else {
                let value = usize::try_from(value).expect("Positive value must fit");
                if value > max {
                    Some(max)
                } else {
                    Some(value)
                }
            }
        }

        let x = clamp(xy.x, size.width - 1, self.size_pixels.width - 1);
        let y = clamp(xy.y, size.height - 1, self.size_pixels.height - 1);
        match (x, y) {
            (Some(x), Some(y)) => Some(LcdXY { x, y }),
            _ => None,
        }
    }

    /// Make sure that the coordinates are within the LCD space.
    ///
    /// This is only used to validate input parameters for those functions that are internal to the
    /// console (such as `move_pixels`).  Functions subject to user input (such as `draw_rect`) must
    /// not use this.
    fn assert_xy_in_range(&mut self, xy: PixelsXY) {
        if cfg!(test) {
            let x = usize::try_from(xy.x).expect("x must be positive and must fit");
            let y = usize::try_from(xy.y).expect("y must be positive and must fit");
            debug_assert!(x < self.size_pixels.width, "x must be within the LCD width");
            debug_assert!(y < self.size_pixels.height, "y must be within the LCD height");
        }
    }

    /// Make sure that the coordinates and size are within the LCD space.
    ///
    /// This is only used to validate input parameters for those functions that are internal to the
    /// console (such as `move_pixels`).  Functions subject to user input (such as `draw_rect`) must
    /// not use this.
    fn assert_xy_size_in_range(&mut self, xy: PixelsXY, size: SizeInPixels) {
        if cfg!(test) {
            self.assert_xy_in_range(xy);
            let x = xy.x as usize;
            let y = xy.y as usize;

            let width = usize::from(size.width);
            let height = usize::from(size.height);

            debug_assert!(
                x + width - 1 < self.size_pixels.width,
                "x + width must be within the LCD width"
            );
            debug_assert!(
                y + height - 1 < self.size_pixels.height,
                "y + height must be within the LCD height"
            );
        }
    }

    /// Gets the start address of the pixel `x`/`y` in the framebuffer.
    fn fb_addr(&self, x: usize, y: usize) -> usize {
        debug_assert!(x < self.size_pixels.width);
        debug_assert!(y < self.size_pixels.height);
        ((y * self.size_pixels.width) + x) * self.stride
    }

    /// Extends the current damage area to include the area between between `x1y1` and `x2y2`
    /// (inclusive) as damaged.
    ///
    /// This only makes sense when syncing is disabled, as the damage area represents the contents
    /// that need to be flushed to the LCD once syncing is enabled again.
    fn damage(&mut self, x1y1: LcdXY, x2y2: LcdXY) {
        debug_assert!(!self.sync);
        debug_assert!(x2y2.x >= x1y1.x);
        debug_assert!(x2y2.y >= x1y1.y);

        if self.damage.is_none() {
            self.damage = Some((x1y1, x2y2));
            return;
        }
        let mut damage = self.damage.unwrap();

        if damage.0.x > x1y1.x {
            damage.0.x = x1y1.x;
        }
        if damage.0.y > x1y1.y {
            damage.0.y = x1y1.y;
        }

        if damage.1.x < x2y2.x {
            damage.1.x = x2y2.x;
        }
        if damage.1.y < x2y2.y {
            damage.1.y = x2y2.y;
        }

        self.damage = Some(damage);
    }

    /// Fills the area contained between `x1y1` and `x2y2` (inclusive) with the `rgb` color.
    ///
    /// If syncing is enabled, this writes directly to the LCD.  Otherwise, this writes to the
    /// framebuffer and records the area as damaged.
    fn fill(&mut self, x1y1: LcdXY, x2y2: LcdXY, rgb: RGB) -> io::Result<()> {
        let pixel = self.lcd.encode(rgb);

        if self.sync {
            let mut data = LcdSize::between(x1y1, x2y2).new_buffer(self.stride);
            for y in x1y1.y..(x2y2.y + 1) {
                for x in x1y1.x..(x2y2.x + 1) {
                    let offset = self.fb_addr(x, y);
                    for (i, byte) in pixel.into_iter().enumerate() {
                        self.fb[offset + i] = byte;
                        data.push(byte);
                    }
                }
            }
            self.lcd.set_data(x1y1, x2y2, &data)?;
        } else {
            for y in x1y1.y..(x2y2.y + 1) {
                for x in x1y1.x..(x2y2.x + 1) {
                    let offset = self.fb_addr(x, y);
                    for (i, byte) in pixel.into_iter().enumerate() {
                        self.fb[offset + i] = byte;
                    }
                }
            }
            self.damage(x1y1, x2y2);
        }

        Ok(())
    }

    /// Flushes any pending damaged area to the LCD.
    fn force_present_canvas(&mut self) -> io::Result<()> {
        let (x1y1, x2y2) = match self.damage {
            None => return Ok(()),
            Some(damage) => damage,
        };

        let mut data = LcdSize::between(x1y1, x2y2).new_buffer(self.stride);
        for y in x1y1.y..(x2y2.y + 1) {
            for x in x1y1.x..(x2y2.x + 1) {
                let offset = self.fb_addr(x, y);
                data.extend_from_slice(&self.fb[offset..offset + self.stride]);
            }
        }
        debug_assert_eq!(
            {
                let (_xy, size) = to_xy_size(x1y1, x2y2);
                size.width * size.height * self.stride
            },
            data.len()
        );

        self.lcd.set_data(x1y1, x2y2, &data)?;

        self.damage = None;

        Ok(())
    }
}

impl<L> Drop for BufferedLcd<L>
where
    L: Lcd,
{
    fn drop(&mut self) {
        self.clear((0, 0, 0)).unwrap();
    }
}

impl<L> RasterOps for BufferedLcd<L>
where
    L: Lcd,
{
    type ID = (Vec<u8>, SizeInPixels);

    fn get_info(&self) -> RasterInfo {
        RasterInfo {
            size_pixels: self.size_pixels.into(),
            glyph_size: self.glyph_size.into(),
            size_chars: self.size_chars,
        }
    }

    fn clear(&mut self, color: RGB) -> io::Result<()> {
        self.fill(
            LcdXY { x: 0, y: 0 },
            LcdXY { x: self.size_pixels.width - 1, y: self.size_pixels.height - 1 },
            color,
        )
    }

    fn set_sync(&mut self, enabled: bool) {
        self.sync = enabled;
    }

    fn present_canvas(&mut self) -> io::Result<()> {
        if self.sync {
            Ok(())
        } else {
            self.force_present_canvas()
        }
    }

    fn read_pixels(&mut self, xy: PixelsXY, size: SizeInPixels) -> io::Result<Self::ID> {
        self.assert_xy_size_in_range(xy, size);
        let x1y1 = self.clip_xy(xy).expect("Internal ops must receive valid coordinates");
        let x2y2 = self.clip_x2y2(xy, size).expect("Internal ops must receive valid coordinates");

        let mut pixels = LcdSize::between(x1y1, x2y2).new_buffer(self.stride);

        for y in x1y1.y..(x2y2.y + 1) {
            for x in x1y1.x..(x2y2.x + 1) {
                let offset = self.fb_addr(x, y);
                pixels.extend_from_slice(&self.fb[offset..offset + self.stride]);
            }
        }

        debug_assert_eq!(
            usize::from(size.width) * usize::from(size.height) * self.stride,
            pixels.len()
        );
        Ok((pixels, size))
    }

    fn put_pixels(&mut self, xy: PixelsXY, (pixels, size): &Self::ID) -> io::Result<()> {
        debug_assert_eq!(
            usize::from(size.width) * usize::from(size.height) * self.stride,
            pixels.len()
        );

        self.assert_xy_in_range(xy);
        let x1y1 = self.clip_xy(xy).expect("Internal ops must receive valid coordinates");
        let x2y2 = self.clip_x2y2(xy, *size).expect("Internal ops must receive valid coordinates");

        let mut p = 0;
        for y in x1y1.y..(x2y2.y + 1) {
            for x in x1y1.x..(x2y2.x + 1) {
                let offset = self.fb_addr(x, y);
                self.fb[offset..(offset + self.stride)]
                    .copy_from_slice(&pixels[p..(p + self.stride)]);
                p += self.stride;
            }
        }

        if self.sync {
            self.lcd.set_data(x1y1, x2y2, pixels)?;
        } else {
            self.damage(x1y1, x2y2);
        }

        Ok(())
    }

    fn move_pixels(
        &mut self,
        x1y1: PixelsXY,
        x2y2: PixelsXY,
        size: SizeInPixels,
        color: RGB,
    ) -> io::Result<()> {
        self.assert_xy_size_in_range(x1y1, size);
        self.assert_xy_size_in_range(x2y2, size);

        let data = self.read_pixels(x1y1, size)?;

        self.without_sync(|self2| {
            self2.draw_rect_filled(x1y1, size, color)?;
            self2.put_pixels(x2y2, &data)
        })?;

        Ok(())
    }

    fn write_text(
        &mut self,
        xy: PixelsXY,
        text: &str,
        fg_color: RGB,
        bg_color: RGB,
    ) -> io::Result<()> {
        self.assert_xy_in_range(xy);

        let x1y1 = self.clip_xy(xy).expect("Internal ops must receive valid coordinates");
        let size =
            LcdSize { width: text.len() * self.glyph_size.width, height: self.glyph_size.height };
        let x2y2 = LcdXY {
            x: (x1y1.x + size.width - 1).clamp(0, self.size_pixels.width - 1),
            y: (x1y1.y + size.height - 1).clamp(0, self.size_pixels.height - 1),
        };

        self.without_sync(|self2| {
            self2.fill(x1y1, x2y2, bg_color)?;

            let mut pos = x1y1;
            for ch in text.chars() {
                let glyph = font8::glyph(ch);
                debug_assert_eq!(self2.glyph_size.height, glyph.len());
                for (j, row) in glyph.iter().enumerate() {
                    let mut mask = 0x80;
                    for i in 0..self2.glyph_size.width {
                        let bit = row & mask;
                        if bit != 0 {
                            let x = pos.x + i;
                            if x >= self2.size_pixels.width {
                                continue;
                            }

                            let y = pos.y + j;
                            if y >= self2.size_pixels.height {
                                continue;
                            }

                            let xy = LcdXY { x, y };
                            self2.fill(xy, xy, fg_color)?;
                        }
                        mask >>= 1;
                    }
                }

                pos.x += self2.glyph_size.width;
            }
            Ok(())
        })
    }

    fn draw_circle(&mut self, _center: PixelsXY, _radius: u16, _color: RGB) -> io::Result<()> {
        todo!()
    }

    fn draw_circle_filled(
        &mut self,
        _center: PixelsXY,
        _radius: u16,
        _color: RGB,
    ) -> io::Result<()> {
        todo!()
    }

    fn draw_line(&mut self, _x1y1: PixelsXY, _x2y2: PixelsXY, _color: RGB) -> io::Result<()> {
        todo!()
    }

    fn draw_pixel(&mut self, xy: PixelsXY, color: RGB) -> io::Result<()> {
        let xy = self.clip_xy(xy);
        match xy {
            Some(xy) => self.fill(xy, xy, color),
            None => Ok(()),
        }
    }

    fn draw_rect(&mut self, _xy: PixelsXY, _size: SizeInPixels, _color: RGB) -> io::Result<()> {
        todo!()
    }

    fn draw_rect_filled(&mut self, xy: PixelsXY, size: SizeInPixels, color: RGB) -> io::Result<()> {
        let x1y1 = self.clamp_xy(xy);
        let x2y2 = self.clip_x2y2(xy, size);
        match x2y2 {
            Some(x2y2) => self.fill(x1y1, x2y2, color),
            _ => Ok(()),
        }
    }
}
