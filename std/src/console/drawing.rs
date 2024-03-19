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

//! Drawing algorithms for consoles that don't provide native rendering primitives.

use crate::console::graphics::RasterOps;
use crate::console::PixelsXY;
use std::convert::TryFrom;
use std::io;

/// Auxiliary function for the `draw_line` algorithm to handle slopes between 0 and -1.
fn draw_line_low<R>(rasops: &mut R, x1: i32, y1: i32, x2: i32, y2: i32) -> io::Result<()>
where
    R: RasterOps,
{
    let dx = x2 - x1;
    let mut dy = y2 - y1;

    let mut yi = 1;
    if dy < 0 {
        yi = -1;
        dy = -dy;
    }
    let mut d = (2 * dy) - dx;
    let mut y = y1;

    for x in x1..(x2 + 1) {
        if cfg!(debug_assertions) {
            rasops.draw_pixel(PixelsXY {
                x: i16::try_from(x).expect("Coordinate must fit after computations"),
                y: i16::try_from(y).expect("Coordinate must fit after computations"),
            })?;
        } else {
            rasops.draw_pixel(PixelsXY { x: x as i16, y: y as i16 })?;
        }
        if d > 0 {
            y += yi;
            d += 2 * (dy - dx);
        } else {
            d += 2 * dy;
        }
    }

    Ok(())
}

/// Auxiliary function for the `draw_line` algorithm to handle positive or negative slopes.
fn draw_line_high<R>(rasops: &mut R, x1: i32, y1: i32, x2: i32, y2: i32) -> io::Result<()>
where
    R: RasterOps,
{
    let mut dx = x2 - x1;
    let dy = y2 - y1;

    let mut xi = 1;
    if dx < 0 {
        xi = -1;
        dx = -dx;
    }
    let mut d = (2 * dx) - dy;
    let mut x = x1;

    for y in y1..(y2 + 1) {
        if cfg!(debug_assertions) {
            rasops.draw_pixel(PixelsXY {
                x: i16::try_from(x).expect("Coordinate must fit after computations"),
                y: i16::try_from(y).expect("Coordinate must fit after computations"),
            })?;
        } else {
            rasops.draw_pixel(PixelsXY { x: x as i16, y: y as i16 })?;
        }
        if d > 0 {
            x += xi;
            d += 2 * (dx - dy);
        } else {
            d += 2 * dx;
        }
    }

    Ok(())
}

/// Draws a line from `x1y1` to `x2y2` via `rasops`.
///
/// This implements the [Bresenham's line
/// algorithm](https://en.wikipedia.org/wiki/Bresenham%27s_line_algorithm).
pub fn draw_line<R>(rasops: &mut R, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()>
where
    R: RasterOps,
{
    // Widen coordinates so we don't have to worry about overflows anywhere.
    let x1 = i32::from(x1y1.x);
    let y1 = i32::from(x1y1.y);
    let x2 = i32::from(x2y2.x);
    let y2 = i32::from(x2y2.y);

    if (y2 - y1).abs() < (x2 - x1).abs() {
        if x1y1.x > x2y2.x {
            draw_line_low(rasops, x2, y2, x1, y1)
        } else {
            draw_line_low(rasops, x1, y1, x2, y2)
        }
    } else {
        if x1y1.y > x2y2.y {
            draw_line_high(rasops, x2, y2, x1, y1)
        } else {
            draw_line_high(rasops, x1, y1, x2, y2)
        }
    }
}

#[cfg(test)]
mod testutils {
    use super::*;
    use crate::console::graphics::RasterInfo;
    use crate::console::{SizeInPixels, RGB};

    /// Representation of captured raster operations.
    #[derive(Debug, PartialEq)]
    pub(crate) enum CapturedRasop {
        DrawPixel(i16, i16),
    }

    /// An implementation of `RasterOps` that captures calls for later validation.
    #[derive(Default)]
    pub(crate) struct RecordingRasops {
        pub(crate) ops: Vec<CapturedRasop>,
    }

    impl RasterOps for RecordingRasops {
        type ID = u8;

        fn get_info(&self) -> RasterInfo {
            unimplemented!();
        }

        fn set_draw_color(&mut self, _color: RGB) {
            unimplemented!();
        }

        fn clear(&mut self) -> io::Result<()> {
            unimplemented!();
        }

        fn set_sync(&mut self, _enabled: bool) {
            unimplemented!();
        }

        fn present_canvas(&mut self) -> io::Result<()> {
            unimplemented!();
        }

        fn read_pixels(&mut self, _xy: PixelsXY, _size: SizeInPixels) -> io::Result<Self::ID> {
            unimplemented!();
        }

        fn put_pixels(&mut self, _xy: PixelsXY, _data: &Self::ID) -> io::Result<()> {
            unimplemented!();
        }

        fn move_pixels(
            &mut self,
            _x1y1: PixelsXY,
            _x2y2: PixelsXY,
            _size: SizeInPixels,
        ) -> io::Result<()> {
            unimplemented!();
        }

        fn write_text(&mut self, _xy: PixelsXY, _text: &str) -> io::Result<()> {
            unimplemented!();
        }

        fn draw_circle(&mut self, _center: PixelsXY, _radius: u16) -> io::Result<()> {
            unimplemented!();
        }

        fn draw_circle_filled(&mut self, _center: PixelsXY, _radius: u16) -> io::Result<()> {
            unimplemented!();
        }

        fn draw_line(&mut self, _x1y1: PixelsXY, _x2y2: PixelsXY) -> io::Result<()> {
            unimplemented!();
        }

        fn draw_pixel(&mut self, xy: PixelsXY) -> io::Result<()> {
            self.ops.push(CapturedRasop::DrawPixel(xy.x, xy.y));
            Ok(())
        }

        fn draw_rect(&mut self, _xy: PixelsXY, _size: SizeInPixels) -> io::Result<()> {
            unimplemented!();
        }

        fn draw_rect_filled(&mut self, _xy: PixelsXY, _size: SizeInPixels) -> io::Result<()> {
            unimplemented!();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::testutils::*;
    use super::*;

    #[test]
    fn test_draw_line_dot() {
        let mut rasops = RecordingRasops::default();
        draw_line(&mut rasops, PixelsXY::new(10, 20), PixelsXY::new(10, 20)).unwrap();
        assert_eq!([CapturedRasop::DrawPixel(10, 20)], rasops.ops.as_slice());
    }

    #[test]
    fn test_draw_line_horizontal_right() {
        let mut rasops = RecordingRasops::default();
        draw_line(&mut rasops, PixelsXY::new(100, 0), PixelsXY::new(105, 0)).unwrap();
        assert_eq!(
            [
                CapturedRasop::DrawPixel(100, 0),
                CapturedRasop::DrawPixel(101, 0),
                CapturedRasop::DrawPixel(102, 0),
                CapturedRasop::DrawPixel(103, 0),
                CapturedRasop::DrawPixel(104, 0),
                CapturedRasop::DrawPixel(105, 0),
            ],
            rasops.ops.as_slice()
        );
    }

    #[test]
    fn test_draw_line_horizontal_left() {
        let mut rasops = RecordingRasops::default();
        draw_line(&mut rasops, PixelsXY::new(105, 0), PixelsXY::new(100, 0)).unwrap();
        assert_eq!(
            [
                CapturedRasop::DrawPixel(100, 0),
                CapturedRasop::DrawPixel(101, 0),
                CapturedRasop::DrawPixel(102, 0),
                CapturedRasop::DrawPixel(103, 0),
                CapturedRasop::DrawPixel(104, 0),
                CapturedRasop::DrawPixel(105, 0),
            ],
            rasops.ops.as_slice()
        );
    }

    #[test]
    fn test_draw_line_vertical_down() {
        let mut rasops = RecordingRasops::default();
        draw_line(&mut rasops, PixelsXY::new(0, 100), PixelsXY::new(0, 105)).unwrap();
        assert_eq!(
            [
                CapturedRasop::DrawPixel(0, 100),
                CapturedRasop::DrawPixel(0, 101),
                CapturedRasop::DrawPixel(0, 102),
                CapturedRasop::DrawPixel(0, 103),
                CapturedRasop::DrawPixel(0, 104),
                CapturedRasop::DrawPixel(0, 105),
            ],
            rasops.ops.as_slice()
        );
    }

    #[test]
    fn test_draw_line_vertical_up() {
        let mut rasops = RecordingRasops::default();
        draw_line(&mut rasops, PixelsXY::new(0, 105), PixelsXY::new(0, 100)).unwrap();
        assert_eq!(
            [
                CapturedRasop::DrawPixel(0, 100),
                CapturedRasop::DrawPixel(0, 101),
                CapturedRasop::DrawPixel(0, 102),
                CapturedRasop::DrawPixel(0, 103),
                CapturedRasop::DrawPixel(0, 104),
                CapturedRasop::DrawPixel(0, 105),
            ],
            rasops.ops.as_slice()
        );
    }

    #[test]
    fn test_draw_line_horizontal_slope_right() {
        let mut rasops = RecordingRasops::default();
        draw_line(&mut rasops, PixelsXY::new(100, 0), PixelsXY::new(105, 3)).unwrap();
        assert_eq!(
            [
                CapturedRasop::DrawPixel(100, 0),
                CapturedRasop::DrawPixel(101, 1),
                CapturedRasop::DrawPixel(102, 1),
                CapturedRasop::DrawPixel(103, 2),
                CapturedRasop::DrawPixel(104, 2),
                CapturedRasop::DrawPixel(105, 3),
            ],
            rasops.ops.as_slice()
        );
    }

    #[test]
    fn test_draw_line_horizontal_slope_left() {
        let mut rasops = RecordingRasops::default();
        draw_line(&mut rasops, PixelsXY::new(105, 0), PixelsXY::new(100, 3)).unwrap();
        assert_eq!(
            [
                CapturedRasop::DrawPixel(100, 3),
                CapturedRasop::DrawPixel(101, 2),
                CapturedRasop::DrawPixel(102, 2),
                CapturedRasop::DrawPixel(103, 1),
                CapturedRasop::DrawPixel(104, 1),
                CapturedRasop::DrawPixel(105, 0),
            ],
            rasops.ops.as_slice()
        );
    }

    #[test]
    fn test_draw_line_vertical_slope_up() {
        let mut rasops = RecordingRasops::default();
        draw_line(&mut rasops, PixelsXY::new(0, 100), PixelsXY::new(3, 105)).unwrap();
        assert_eq!(
            [
                CapturedRasop::DrawPixel(0, 100),
                CapturedRasop::DrawPixel(1, 101),
                CapturedRasop::DrawPixel(1, 102),
                CapturedRasop::DrawPixel(2, 103),
                CapturedRasop::DrawPixel(2, 104),
                CapturedRasop::DrawPixel(3, 105),
            ],
            rasops.ops.as_slice()
        );
    }

    #[test]
    fn test_draw_line_vertical_slope_down() {
        let mut rasops = RecordingRasops::default();
        draw_line(&mut rasops, PixelsXY::new(0, 105), PixelsXY::new(3, 100)).unwrap();
        assert_eq!(
            [
                CapturedRasop::DrawPixel(3, 100),
                CapturedRasop::DrawPixel(2, 101),
                CapturedRasop::DrawPixel(2, 102),
                CapturedRasop::DrawPixel(1, 103),
                CapturedRasop::DrawPixel(1, 104),
                CapturedRasop::DrawPixel(0, 105),
            ],
            rasops.ops.as_slice()
        );
    }

    #[test]
    fn test_draw_line_corners() {
        for corner in
            [PixelsXY::TOP_LEFT, PixelsXY::TOP_RIGHT, PixelsXY::BOTTOM_LEFT, PixelsXY::BOTTOM_RIGHT]
        {
            let mut rasops = RecordingRasops::default();
            draw_line(&mut rasops, corner, corner).unwrap();
            assert_eq!([CapturedRasop::DrawPixel(corner.x, corner.y)], rasops.ops.as_slice());
        }
    }

    #[test]
    fn test_draw_line_perimeter() {
        for corners in [
            (PixelsXY::TOP_LEFT, PixelsXY::TOP_RIGHT),
            (PixelsXY::TOP_RIGHT, PixelsXY::BOTTOM_RIGHT),
            (PixelsXY::BOTTOM_RIGHT, PixelsXY::BOTTOM_LEFT),
            (PixelsXY::BOTTOM_LEFT, PixelsXY::TOP_LEFT),
        ] {
            let mut rasops = RecordingRasops::default();
            draw_line(&mut rasops, corners.0, corners.1).unwrap();
            assert_eq!(usize::from(u16::MAX) + 1, rasops.ops.len());
        }
    }

    #[test]
    fn test_draw_line_diagonals() {
        for corners in [
            (PixelsXY::TOP_LEFT, PixelsXY::BOTTOM_RIGHT),
            (PixelsXY::BOTTOM_RIGHT, PixelsXY::TOP_LEFT),
            (PixelsXY::TOP_RIGHT, PixelsXY::BOTTOM_LEFT),
            (PixelsXY::BOTTOM_LEFT, PixelsXY::TOP_RIGHT),
        ] {
            let mut rasops = RecordingRasops::default();
            draw_line(&mut rasops, corners.0, corners.1).unwrap();
            assert_eq!(usize::from(u16::MAX) + 1, rasops.ops.len());
        }
    }
}
