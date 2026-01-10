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

use crate::console::graphics::{ClampedInto, RasterOps};
use crate::console::{PixelsXY, SizeInPixels};
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

/// Draws a circle via `rasops` with `center` and `radius`.
///
/// This implements the [Midpoint circle
/// algorithm](https://en.wikipedia.org/wiki/Midpoint_circle_algorithm).
pub fn draw_circle<R>(rasops: &mut R, center: PixelsXY, radius: u16) -> io::Result<()>
where
    R: RasterOps,
{
    fn point<R: RasterOps>(rasops: &mut R, x: i16, y: i16) -> io::Result<()> {
        rasops.draw_pixel(PixelsXY { x, y })
    }

    if radius == 0 {
        return Ok(());
    } else if radius == 1 {
        return rasops.draw_pixel(center);
    }

    let (diameter, radius): (i16, i16) = match radius.checked_mul(2) {
        Some(d) => match i16::try_from(d) {
            Ok(d) => (d, radius as i16),
            Err(_) => return Err(io::Error::new(io::ErrorKind::InvalidInput, "Radius is too big")),
        },
        None => return Err(io::Error::new(io::ErrorKind::InvalidInput, "Radius is too big")),
    };

    let mut x: i16 = radius - 1;
    let mut y: i16 = 0;
    let mut tx: i16 = 1;
    let mut ty: i16 = 1;
    let mut e: i16 = tx - diameter;

    while x >= y {
        point(rasops, center.x + x, center.y - y)?;
        point(rasops, center.x + x, center.y + y)?;
        point(rasops, center.x - x, center.y - y)?;
        point(rasops, center.x - x, center.y + y)?;
        point(rasops, center.x + y, center.y - x)?;
        point(rasops, center.x + y, center.y + x)?;
        point(rasops, center.x - y, center.y - x)?;
        point(rasops, center.x - y, center.y + x)?;

        if e <= 0 {
            y += 1;
            e += ty;
            ty += 2;
        }

        if e > 0 {
            x -= 1;
            tx += 2;
            e += tx - diameter;
        }
    }

    Ok(())
}

/// Draws a circle via `rasops` with `center` and `radius`.
///
/// This implements the [Midpoint circle
/// algorithm](https://en.wikipedia.org/wiki/Midpoint_circle_algorithm).
pub fn draw_circle_filled<R>(rasops: &mut R, center: PixelsXY, radius: u16) -> io::Result<()>
where
    R: RasterOps,
{
    fn line<R: RasterOps>(rasops: &mut R, x1: i16, y1: i16, x2: i16, y2: i16) -> io::Result<()> {
        rasops.draw_line(PixelsXY { x: x1, y: y1 }, PixelsXY { x: x2, y: y2 })
    }

    if radius == 0 {
        return Ok(());
    } else if radius == 1 {
        return rasops.draw_pixel(center);
    }

    let (diameter, radius): (i16, i16) = match radius.checked_mul(2) {
        Some(d) => match i16::try_from(d) {
            Ok(d) => (d, radius as i16),

            Err(_) => return Err(io::Error::new(io::ErrorKind::InvalidInput, "Radius is too big")),
        },
        None => return Err(io::Error::new(io::ErrorKind::InvalidInput, "Radius is too big")),
    };

    let mut x: i16 = radius - 1;
    let mut y: i16 = 0;
    let mut tx: i16 = 1;
    let mut ty: i16 = 1;
    let mut e: i16 = tx - diameter;

    while x >= y {
        line(rasops, center.x + x, center.y - y, center.x + x, center.y + y)?;
        line(rasops, center.x - x, center.y - y, center.x - x, center.y + y)?;
        line(rasops, center.x + y, center.y - x, center.x + y, center.y + x)?;
        line(rasops, center.x - y, center.y - x, center.x - y, center.y + x)?;

        if e <= 0 {
            y += 1;
            e += ty;
            ty += 2;
        }

        if e > 0 {
            x -= 1;
            tx += 2;
            e += tx - diameter;
        }
    }

    Ok(())
}

/// Draws a rectangle via `rasops` starting at `x1y1` with `size`.
pub fn draw_rect<R>(rasops: &mut R, x1y1: PixelsXY, size: SizeInPixels) -> io::Result<()>
where
    R: RasterOps,
{
    let x2y2 = PixelsXY {
        x: (i32::from(x1y1.x) + i32::from(size.width - 1)).clamped_into(),
        y: (i32::from(x1y1.y) + i32::from(size.height - 1)).clamped_into(),
    };
    rasops.draw_line(PixelsXY { x: x1y1.x, y: x1y1.y }, PixelsXY { x: x2y2.x, y: x1y1.y })?;
    rasops.draw_line(PixelsXY { x: x2y2.x, y: x1y1.y }, PixelsXY { x: x2y2.x, y: x2y2.y })?;
    rasops.draw_line(PixelsXY { x: x2y2.x, y: x2y2.y }, PixelsXY { x: x1y1.x, y: x2y2.y })?;
    rasops.draw_line(PixelsXY { x: x1y1.x, y: x2y2.y }, PixelsXY { x: x1y1.x, y: x1y1.y })?;
    Ok(())
}

#[cfg(test)]
mod testutils {
    use super::*;
    use crate::console::graphics::RasterInfo;
    use crate::console::{RGB, SizeInPixels};

    /// Representation of captured raster operations.
    #[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
    pub(crate) enum CapturedRasop {
        DrawLine(i16, i16, i16, i16),
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

        fn draw_line(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
            self.ops.push(CapturedRasop::DrawLine(x1y1.x, x1y1.y, x2y2.x, x2y2.y));
            Ok(())
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
    fn test_draw_circle_zero() {
        let mut rasops = RecordingRasops::default();
        draw_circle(&mut rasops, PixelsXY::new(10, 20), 0).unwrap();
        assert!(rasops.ops.is_empty());
    }

    #[test]
    fn test_draw_circle_dot() {
        let mut rasops = RecordingRasops::default();
        draw_circle(&mut rasops, PixelsXY::new(10, 20), 1).unwrap();
        assert_eq!([CapturedRasop::DrawPixel(10, 20)], rasops.ops.as_slice());
    }

    #[test]
    fn test_draw_circle_larger() {
        let mut rasops = RecordingRasops::default();
        draw_circle(&mut rasops, PixelsXY::new(10, 20), 4).unwrap();
        rasops.ops.sort();
        assert_eq!(
            [
                CapturedRasop::DrawPixel(7, 18),
                CapturedRasop::DrawPixel(7, 19),
                CapturedRasop::DrawPixel(7, 20),
                CapturedRasop::DrawPixel(7, 20),
                CapturedRasop::DrawPixel(7, 21),
                CapturedRasop::DrawPixel(7, 22),
                CapturedRasop::DrawPixel(8, 17),
                CapturedRasop::DrawPixel(8, 23),
                CapturedRasop::DrawPixel(9, 17),
                CapturedRasop::DrawPixel(9, 23),
                CapturedRasop::DrawPixel(10, 17),
                CapturedRasop::DrawPixel(10, 17),
                CapturedRasop::DrawPixel(10, 23),
                CapturedRasop::DrawPixel(10, 23),
                CapturedRasop::DrawPixel(11, 17),
                CapturedRasop::DrawPixel(11, 23),
                CapturedRasop::DrawPixel(12, 17),
                CapturedRasop::DrawPixel(12, 23),
                CapturedRasop::DrawPixel(13, 18),
                CapturedRasop::DrawPixel(13, 19),
                CapturedRasop::DrawPixel(13, 20),
                CapturedRasop::DrawPixel(13, 20),
                CapturedRasop::DrawPixel(13, 21),
                CapturedRasop::DrawPixel(13, 22),
            ],
            rasops.ops.as_slice()
        );
    }

    #[test]
    fn test_draw_circle_corners() {
        for corner in
            [PixelsXY::TOP_LEFT, PixelsXY::TOP_RIGHT, PixelsXY::BOTTOM_LEFT, PixelsXY::BOTTOM_RIGHT]
        {
            let mut rasops = RecordingRasops::default();
            draw_circle(&mut rasops, corner, 1).unwrap();
            assert_eq!([CapturedRasop::DrawPixel(corner.x, corner.y)], rasops.ops.as_slice());
        }
    }

    #[test]
    fn test_draw_circle_filled_zero() {
        let mut rasops = RecordingRasops::default();
        draw_circle_filled(&mut rasops, PixelsXY::new(10, 20), 0).unwrap();
        assert!(rasops.ops.is_empty());
    }

    #[test]
    fn test_draw_circle_filled_dot() {
        let mut rasops = RecordingRasops::default();
        draw_circle_filled(&mut rasops, PixelsXY::new(10, 20), 1).unwrap();
        assert_eq!([CapturedRasop::DrawPixel(10, 20)], rasops.ops.as_slice());
    }

    #[test]
    fn test_draw_circle_filled_larger() {
        let mut rasops = RecordingRasops::default();
        draw_circle_filled(&mut rasops, PixelsXY::new(10, 20), 4).unwrap();
        rasops.ops.sort();
        assert_eq!(
            [
                CapturedRasop::DrawLine(7, 18, 7, 22),
                CapturedRasop::DrawLine(7, 19, 7, 21),
                CapturedRasop::DrawLine(7, 20, 7, 20),
                CapturedRasop::DrawLine(8, 17, 8, 23),
                CapturedRasop::DrawLine(9, 17, 9, 23),
                CapturedRasop::DrawLine(10, 17, 10, 23),
                CapturedRasop::DrawLine(10, 17, 10, 23),
                CapturedRasop::DrawLine(11, 17, 11, 23),
                CapturedRasop::DrawLine(12, 17, 12, 23),
                CapturedRasop::DrawLine(13, 18, 13, 22),
                CapturedRasop::DrawLine(13, 19, 13, 21),
                CapturedRasop::DrawLine(13, 20, 13, 20),
            ],
            rasops.ops.as_slice()
        );
    }

    #[test]
    fn test_draw_circle_filled_corners() {
        for corner in
            [PixelsXY::TOP_LEFT, PixelsXY::TOP_RIGHT, PixelsXY::BOTTOM_LEFT, PixelsXY::BOTTOM_RIGHT]
        {
            let mut rasops = RecordingRasops::default();
            draw_circle_filled(&mut rasops, corner, 1).unwrap();
            assert_eq!([CapturedRasop::DrawPixel(corner.x, corner.y)], rasops.ops.as_slice());
        }
    }

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

    #[test]
    fn test_draw_rect_dot() {
        let mut rasops = RecordingRasops::default();
        draw_rect(&mut rasops, PixelsXY::new(10, 20), SizeInPixels::new(1, 1)).unwrap();
        assert_eq!(
            [
                CapturedRasop::DrawLine(10, 20, 10, 20),
                CapturedRasop::DrawLine(10, 20, 10, 20),
                CapturedRasop::DrawLine(10, 20, 10, 20),
                CapturedRasop::DrawLine(10, 20, 10, 20),
            ],
            rasops.ops.as_slice()
        );
    }

    #[test]
    fn test_draw_rect_horizontal_line() {
        let mut rasops = RecordingRasops::default();
        draw_rect(&mut rasops, PixelsXY::new(10, 20), SizeInPixels::new(6, 1)).unwrap();
        assert_eq!(
            [
                CapturedRasop::DrawLine(10, 20, 15, 20),
                CapturedRasop::DrawLine(15, 20, 15, 20),
                CapturedRasop::DrawLine(15, 20, 10, 20),
                CapturedRasop::DrawLine(10, 20, 10, 20),
            ],
            rasops.ops.as_slice()
        );
    }

    #[test]
    fn test_draw_rect_vertical_line() {
        let mut rasops = RecordingRasops::default();
        draw_rect(&mut rasops, PixelsXY::new(10, 20), SizeInPixels::new(1, 6)).unwrap();
        assert_eq!(
            [
                CapturedRasop::DrawLine(10, 20, 10, 20),
                CapturedRasop::DrawLine(10, 20, 10, 25),
                CapturedRasop::DrawLine(10, 25, 10, 25),
                CapturedRasop::DrawLine(10, 25, 10, 20),
            ],
            rasops.ops.as_slice()
        );
    }

    #[test]
    fn test_draw_rect_2d() {
        let mut rasops = RecordingRasops::default();
        draw_rect(&mut rasops, PixelsXY::new(10, 20), SizeInPixels::new(6, 7)).unwrap();
        assert_eq!(
            [
                CapturedRasop::DrawLine(10, 20, 15, 20),
                CapturedRasop::DrawLine(15, 20, 15, 26),
                CapturedRasop::DrawLine(15, 26, 10, 26),
                CapturedRasop::DrawLine(10, 26, 10, 20),
            ],
            rasops.ops.as_slice()
        );
    }

    #[test]
    fn test_draw_rect_corners() {
        let mut rasops = RecordingRasops::default();
        draw_rect(&mut rasops, PixelsXY::TOP_LEFT, SizeInPixels::MAX).unwrap();
        assert_eq!(
            [
                CapturedRasop::DrawLine(i16::MIN, i16::MIN, i16::MAX - 1, i16::MIN),
                CapturedRasop::DrawLine(i16::MAX - 1, i16::MIN, i16::MAX - 1, i16::MAX - 1),
                CapturedRasop::DrawLine(i16::MAX - 1, i16::MAX - 1, i16::MIN, i16::MAX - 1),
                CapturedRasop::DrawLine(i16::MIN, i16::MAX - 1, i16::MIN, i16::MIN),
            ],
            rasops.ops.as_slice()
        );
    }
}
