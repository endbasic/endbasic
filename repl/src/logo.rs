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

//! EndBASIC logo rendering.

use endbasic_std::console::{Console, PixelsXY};
use std::io;

/// Support logic for `draw_logo` that doesn't handle color save/restore.
fn draw_logo_internal(
    console: &mut dyn Console,
    x1y1: PixelsXY,
    x2y2: Option<PixelsXY>,
) -> io::Result<()> {
    const SOURCE_W: i32 = 90;
    const SOURCE_H: i32 = 93;
    const SOURCE_WF: f32 = SOURCE_W as f32;
    const SOURCE_HF: f32 = SOURCE_H as f32;

    let x2y2 = x2y2.unwrap_or(PixelsXY::new(
        x1y1.x.saturating_add(i16::try_from(SOURCE_W).unwrap()),
        x1y1.y.saturating_add(i16::try_from(SOURCE_H).unwrap()),
    ));
    let x1 = i32::from(x1y1.x);
    let y1 = i32::from(x1y1.y);
    let x2 = i32::from(x2y2.x);
    let y2 = i32::from(x2y2.y);
    let (x1, x2) = if x1 <= x2 { (x1, x2) } else { (x2, x1) };
    let (y1, y2) = if y1 <= y2 { (y1, y2) } else { (y2, y1) };
    let target_w = x2 - x1;
    let target_h = y2 - y1;
    let scale = (target_w as f32 / SOURCE_WF).min(target_h as f32 / SOURCE_HF);
    let offset_x = x1 as f32 + (target_w as f32 - SOURCE_WF * scale) / 2.0;
    let offset_y = y1 as f32 + (target_h as f32 - SOURCE_HF * scale) / 2.0;

    let tx = |x: i32| -> i16 { (offset_x + x as f32 * scale).round() as i16 };
    let ty = |y: i32| -> i16 { (offset_y + y as f32 * scale).round() as i16 };
    let xy = |x: i32, y: i32| PixelsXY::new(tx(x), ty(y));

    // Outline.
    console.set_color(Some(202), None)?;
    console.draw_poly_filled(&[
        xy(0, 0),
        xy(9, 0),
        xy(9, 1),
        xy(22, 1),
        xy(22, 0),
        xy(69, 0),
        xy(69, 1),
        xy(81, 1),
        xy(81, 0),
        xy(85, 0),
        xy(90, 5),
        xy(90, 93),
        xy(0, 93),
    ])?;

    // Bottom holes.
    console.set_color(Some(0), None)?;
    console.draw_rect_filled(xy(3, 83), xy(7, 86))?;
    console.draw_rect_filled(xy(83, 83), xy(87, 86))?;

    // Top indent.
    console.set_color(Some(208), None)?;
    console.draw_rect_filled(xy(9, 1), xy(81, 32))?;
    console.draw_rect_filled(xy(9, 40), xy(81, 93))?;

    // Label.
    console.set_color(Some(7), None)?;
    console.draw_rect_filled(xy(11, 42), xy(79, 91))?;

    // Top Cover.
    console.set_color(Some(243), None)?;
    console.draw_rect_filled(xy(22, 0), xy(69, 31))?;
    console.set_color(Some(208), None)?;
    console.draw_rect_filled(xy(50, 4), xy(62, 28))?;

    // Letters.
    console.set_color(Some(0), None)?;
    // E.
    console.draw_line(xy(25, 55), xy(25, 75))?;
    console.draw_line(xy(25, 55), xy(35, 55))?;
    console.draw_line(xy(25, 75), xy(35, 75))?;
    console.draw_line(xy(25, 65), xy(30, 65))?;
    // N.
    console.draw_line(xy(40, 55), xy(40, 75))?;
    console.draw_line(xy(40, 55), xy(50, 75))?;
    console.draw_line(xy(50, 55), xy(50, 75))?;
    // D.
    console.draw_line(xy(55, 55), xy(55, 75))?;
    console.draw_line(xy(55, 55), xy(60, 55))?;
    console.draw_line(xy(55, 75), xy(60, 75))?;
    console.draw_line(xy(65, 60), xy(65, 70))?;
    console.draw_line(xy(60, 55), xy(65, 60))?;
    console.draw_line(xy(60, 75), xy(65, 70))?;

    Ok(())
}

/// Draws the EndBASIC logo fitted within the rectangle bounded by `x1y1` and `x2y2`.
///
/// When `x2y2` is not specified, the logo is drawn at its intrinsic size.
pub(crate) fn draw_logo(
    console: &mut dyn Console,
    x1y1: PixelsXY,
    x2y2: Option<PixelsXY>,
) -> io::Result<()> {
    let (old_fg, old_bg) = console.color();
    let result = draw_logo_internal(console, x1y1, x2y2);
    console.set_color(old_fg, old_bg)?;
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use endbasic_sdl::testutils::SdlTest;

    #[test]
    fn test_draw_logo_origin_and_unscaled() {
        let mut test = SdlTest::default();
        test.console().hide_cursor().unwrap();
        draw_logo(test.console(), PixelsXY::new(0, 0), None).unwrap();
        test.verify("repl/src", "logo-unscaled");
    }

    #[test]
    fn test_draw_logo_transported_and_scaled() {
        let mut test = SdlTest::default();
        test.console().hide_cursor().unwrap();
        let x1y1 = PixelsXY { x: 100, y: 100 };
        let x2y2 = PixelsXY { x: 300, y: 300 };
        test.console().draw_rect(x1y1, x2y2).unwrap();
        draw_logo(test.console(), x1y1, Some(x2y2)).unwrap();
        test.verify("repl/src", "logo-scaled");
    }
}
