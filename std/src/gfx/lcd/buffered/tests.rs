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

//! Generic operations for LCD displays.

use super::testutils::*;
use super::*;
use crate::console::graphics::RasterOps;
use crate::console::{CharsXY, PixelsXY, SizeInPixels};
use crate::gfx::lcd::fonts::FONT_5X8;

#[test]
fn test_new_does_nothing() {
    Tester::new(size(8, 4)).check()
}

#[test]
fn test_clip_xy() {
    let lcd = BufferedLcd::new(LcdRecorder::new(size(100, 200)), &FONT_5X8);

    assert_eq!(Some(xy(0, 0)), lcd.clip_xy(PixelsXY::new(0, 0)));
    assert_eq!(Some(xy(10, 20)), lcd.clip_xy(PixelsXY::new(10, 20)));
    assert_eq!(Some(xy(99, 199)), lcd.clip_xy(PixelsXY::new(99, 199)));

    assert_eq!(None, lcd.clip_xy(PixelsXY::new(-1, 0)));
    assert_eq!(None, lcd.clip_xy(PixelsXY::new(0, -1)));
    assert_eq!(None, lcd.clip_xy(PixelsXY::new(100, 0)));
    assert_eq!(None, lcd.clip_xy(PixelsXY::new(0, 200)));
}

#[test]
fn test_clamp_xy() {
    let lcd = BufferedLcd::new(LcdRecorder::new(size(100, 200)), &FONT_5X8);

    assert_eq!(xy(0, 0), lcd.clamp_xy(PixelsXY::new(0, 0)));
    assert_eq!(xy(10, 20), lcd.clamp_xy(PixelsXY::new(10, 20)));
    assert_eq!(xy(99, 199), lcd.clamp_xy(PixelsXY::new(99, 199)));

    assert_eq!(xy(0, 0), lcd.clamp_xy(PixelsXY::new(-1, 0)));
    assert_eq!(xy(0, 0), lcd.clamp_xy(PixelsXY::new(0, -1)));
    assert_eq!(xy(99, 0), lcd.clamp_xy(PixelsXY::new(100, 0)));
    assert_eq!(xy(0, 199), lcd.clamp_xy(PixelsXY::new(0, 200)));
}

#[test]
fn test_clip_x2y2() {
    let lcd = BufferedLcd::new(LcdRecorder::new(size(100, 200)), &FONT_5X8);

    assert_eq!(Some(xy(9, 19)), lcd.clip_x2y2(PixelsXY::new(0, 0), SizeInPixels::new(10, 20)));
    assert_eq!(Some(xy(19, 39)), lcd.clip_x2y2(PixelsXY::new(10, 20), SizeInPixels::new(10, 20)));
    assert_eq!(Some(xy(98, 198)), lcd.clip_x2y2(PixelsXY::new(98, 198), SizeInPixels::new(1, 1)));

    assert_eq!(Some(xy(99, 199)), lcd.clip_x2y2(PixelsXY::new(99, 199), SizeInPixels::new(1, 1)));
    assert_eq!(Some(xy(99, 199)), lcd.clip_x2y2(PixelsXY::new(100, 200), SizeInPixels::new(1, 1)));
    assert_eq!(
        Some(xy(99, 199)),
        lcd.clip_x2y2(PixelsXY::new(0, 0), SizeInPixels::new(1000, 2000))
    );

    assert_eq!(Some(xy(0, 0)), lcd.clip_x2y2(PixelsXY::new(-10, -20), SizeInPixels::new(11, 21)));
    assert_eq!(
        Some(xy(99, 199)),
        lcd.clip_x2y2(PixelsXY::new(-10, -20), SizeInPixels::new(150, 250))
    );

    assert_eq!(None, lcd.clip_x2y2(PixelsXY::new(-10, -20), SizeInPixels::new(10, 20)));
}

#[test]
fn test_fb_addr() {
    let lcd = BufferedLcd::new(LcdRecorder::new(size(100, 200)), &FONT_5X8);

    assert_eq!(0, lcd.fb_addr(0, 0));
    assert_eq!(3, lcd.fb_addr(1, 0));
    assert_eq!(300, lcd.fb_addr(0, 1));
    assert_eq!(609, lcd.fb_addr(3, 2));
}

#[test]
fn test_damage_extend_right_down() {
    Tester::new(size(10, 12))
        .op(|l| l.set_sync(false))
        .op(|l| l.set_draw_color((255, 255, 255)))
        .op(|l| l.fill(xy(2, 1), xy(2, 1)).unwrap())
        .op(|l| l.fill(xy(4, 2), xy(6, 7)).unwrap())
        .expect_damage(xy(2, 1), xy(6, 7))
        .ignore_pixels()
        .check();
}

#[test]
fn test_damage_extend_up_left() {
    Tester::new(size(10, 12))
        .op(|l| l.set_sync(false))
        .op(|l| l.set_draw_color((255, 255, 255)))
        .op(|l| l.fill(xy(4, 2), xy(6, 7)).unwrap())
        .op(|l| l.fill(xy(2, 1), xy(2, 1)).unwrap())
        .expect_damage(xy(2, 1), xy(6, 7))
        .ignore_pixels()
        .check();
}

#[test]
fn test_fill_one_pixel_sync() {
    Tester::new(size(8, 4))
        .op(|l| l.set_draw_color((100, 200, 50)))
        .op(|l| l.fill(xy(3, 2), xy(3, 2)).unwrap())
        .expect_pixel(xy(3, 2), (100, 200, 50))
        .expect_op("set_data: from=(3, 2), to=(3, 2), data=[100, 200, 50]")
        .check();
}

#[test]
fn test_fill_one_pixel_no_sync() {
    Tester::new(size(8, 4))
        .op(|l| l.set_sync(false))
        .op(|l| l.set_draw_color((100, 200, 50)))
        .op(|l| l.fill(xy(3, 2), xy(3, 2)).unwrap())
        .expect_pixel(xy(3, 2), (100, 200, 50))
        .expect_damage(xy(3, 2), xy(3, 2))
        .check();
}

#[test]
fn test_fill_rect_sync() {
    Tester::new(size(8, 4))
        .op(|l| l.set_draw_color((210, 220, 230)))
        .op(|l| l.fill(xy(2, 1), xy(5, 3)).unwrap())
        .expect_pixel(xy(2, 1), (210, 220, 230))
        .expect_pixel(xy(3, 1), (210, 220, 230))
        .expect_pixel(xy(4, 1), (210, 220, 230))
        .expect_pixel(xy(5, 1), (210, 220, 230))
        .expect_pixel(xy(2, 2), (210, 220, 230))
        .expect_pixel(xy(3, 2), (210, 220, 230))
        .expect_pixel(xy(4, 2), (210, 220, 230))
        .expect_pixel(xy(5, 2), (210, 220, 230))
        .expect_pixel(xy(2, 3), (210, 220, 230))
        .expect_pixel(xy(3, 3), (210, 220, 230))
        .expect_pixel(xy(4, 3), (210, 220, 230))
        .expect_pixel(xy(5, 3), (210, 220, 230))
        .expect_op("set_data: from=(2, 1), to=(5, 3), data=[210, 220, 230, 210, 220, 230, 210, 220, 230, 210, 220, 230, 210, 220, 230, 210, 220, 230, 210, 220, 230, 210, 220, 230, 210, 220, 230, 210, 220, 230, 210, 220, 230, 210, 220, 230]")
        .check();
}

#[test]
fn test_fill_rect_no_sync() {
    Tester::new(size(8, 4))
        .op(|l| l.set_sync(false))
        .op(|l| l.set_draw_color((210, 220, 230)))
        .op(|l| l.fill(xy(2, 1), xy(5, 3)).unwrap())
        .expect_pixel(xy(2, 1), (210, 220, 230))
        .expect_pixel(xy(3, 1), (210, 220, 230))
        .expect_pixel(xy(4, 1), (210, 220, 230))
        .expect_pixel(xy(5, 1), (210, 220, 230))
        .expect_pixel(xy(2, 2), (210, 220, 230))
        .expect_pixel(xy(3, 2), (210, 220, 230))
        .expect_pixel(xy(4, 2), (210, 220, 230))
        .expect_pixel(xy(5, 2), (210, 220, 230))
        .expect_pixel(xy(2, 3), (210, 220, 230))
        .expect_pixel(xy(3, 3), (210, 220, 230))
        .expect_pixel(xy(4, 3), (210, 220, 230))
        .expect_pixel(xy(5, 3), (210, 220, 230))
        .expect_damage(xy(2, 1), xy(5, 3))
        .check();
}

#[test]
fn test_force_present_canvas_no_damage() {
    Tester::new(size(10, 12)).op(|l| l.force_present_canvas().unwrap()).check();
}

#[test]
fn test_force_present_canvas_damage() {
    Tester::new(size(10, 12))
        .op(|l| l.set_sync(false))
        .op(|l| l.set_draw_color((120, 40, 180)))
        .op(|l| l.fill(xy(2, 3), xy(2, 3)).unwrap())
        .op(|l| l.force_present_canvas().unwrap())
        .expect_pixel(xy(2, 3), (120, 40, 180))
        .expect_op("set_data: from=(2, 3), to=(2, 3), data=[120, 40, 180]")
        .check();
}

#[test]
fn test_get_info() {
    let lcd = BufferedLcd::new(LcdRecorder::new(size(100, 200)), &FONT_5X8);
    let info = lcd.get_info();
    assert_eq!(info.size_pixels, SizeInPixels::new(100, 200));
    assert_eq!(info.glyph_size, SizeInPixels::new(5, 8));
    assert_eq!(info.size_chars, CharsXY { x: 20, y: 25 });
}

#[test]
fn test_clear() {
    Tester::new(size(2, 3))
        .op(|l| l.set_draw_color((10, 20, 30)))
        .op(|l| l.clear().unwrap())
        .ignore_pixels()
        .expect_op("set_data: from=(0, 0), to=(1, 2), data=[10, 20, 30, 10, 20, 30, 10, 20, 30, 10, 20, 30, 10, 20, 30, 10, 20, 30]")
        .check();
}

#[test]
fn test_present_canvas() {
    Tester::new(size(10, 20))
        .op(|l| {
            l.set_sync(false);
            l.set_draw_color((1, 2, 3));
            l.draw_pixel(PixelsXY::new(5, 6)).unwrap();
            l.present_canvas().unwrap();
            l.set_draw_color((7, 8, 9));
            l.draw_pixel(PixelsXY::new(0, 0)).unwrap();
        })
        .expect_pixel(xy(5, 6), (1, 2, 3))
        .expect_pixel(xy(0, 0), (7, 8, 9))
        .expect_damage(xy(0, 0), xy(0, 0))
        .expect_op("set_data: from=(5, 6), to=(5, 6), data=[1, 2, 3]")
        .check();
}

#[test]
fn test_read_pixels_sync() {
    Tester::new(size(10, 12))
        .op(|l| l.set_draw_color((120, 40, 180)))
        .op(|l| l.fill(xy(4, 2), xy(5, 4)).unwrap())
        .op(|l| {
            let size = SizeInPixels::new(2, 3);
            let data = l.read_pixels(PixelsXY { x: 3, y: 1 }, size).unwrap();
            let exp_pixels = vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 120, 40, 180, 0, 0, 0, 120, 40, 180];
            assert_eq!((exp_pixels, size), data);
        })
        .expect_op("set_data: from=(4, 2), to=(5, 4), data=[120, 40, 180, 120, 40, 180, 120, 40, 180, 120, 40, 180, 120, 40, 180, 120, 40, 180]")
        .ignore_pixels()
        .check();
}

#[test]
fn test_read_pixels_no_sync() {
    Tester::new(size(10, 12))
        .op(|l| l.set_sync(false))
        .op(|l| l.set_draw_color((120, 40, 180)))
        .op(|l| l.fill(xy(4, 2), xy(5, 4)).unwrap())
        .op(|l| {
            let size = SizeInPixels::new(2, 3);
            let data = l.read_pixels(PixelsXY { x: 3, y: 1 }, size).unwrap();
            let exp_pixels = vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 120, 40, 180, 0, 0, 0, 120, 40, 180];
            assert_eq!((exp_pixels, size), data);
        })
        .expect_damage(xy(4, 2), xy(5, 4))
        .ignore_pixels()
        .check();
}

#[test]
fn test_put_pixels_sync() {
    Tester::new(size(10, 12))
        .op(|l| {
            let pixels = vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 90, 80, 70, 0, 0, 0, 90, 80, 70];
            let size = SizeInPixels::new(2, 3);
            l.put_pixels(PixelsXY { x: 3, y: 1 }, &(pixels, size)).unwrap();
        })
        .expect_pixel(xy(4, 2), (90, 80, 70))
        .expect_pixel(xy(4, 3), (90, 80, 70))
        .expect_op(
            "set_data: from=(3, 1), to=(4, 3), data=[0, 0, 0, 0, 0, 0, 0, 0, 0, 90, 80, 70, 0, 0, 0, 90, 80, 70]",
        )
        .check();
}

#[test]
fn test_put_pixels_no_sync() {
    Tester::new(size(10, 12))
        .op(|l| l.set_sync(false))
        .op(|l| {
            let pixels = vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 90, 80, 70, 0, 0, 0, 90, 80, 70];
            let size = SizeInPixels::new(2, 3);
            l.put_pixels(PixelsXY { x: 3, y: 1 }, &(pixels, size)).unwrap();
        })
        .expect_damage(xy(3, 1), xy(4, 3))
        .expect_pixel(xy(4, 2), (90, 80, 70))
        .expect_pixel(xy(4, 3), (90, 80, 70))
        .check();
}

#[test]
fn test_write_text_sync() {
    Tester::new(size(20, 30))
        .op(|l| l.set_draw_color((250, 251, 252)))
        .op(|l| l.write_text(PixelsXY::new(0, 0), "#").unwrap())
        .expect_pixel(xy(2, 0), (250, 251, 252))
        .expect_pixel(xy(4, 0), (250, 251, 252))
        .expect_pixel(xy(1, 1), (250, 251, 252))
        .expect_pixel(xy(3, 1), (250, 251, 252))
        .expect_pixel(xy(0, 2), (250, 251, 252))
        .expect_pixel(xy(1, 2), (250, 251, 252))
        .expect_pixel(xy(2, 2), (250, 251, 252))
        .expect_pixel(xy(3, 2), (250, 251, 252))
        .expect_pixel(xy(4, 2), (250, 251, 252))
        .expect_pixel(xy(1, 3), (250, 251, 252))
        .expect_pixel(xy(3, 3), (250, 251, 252))
        .expect_pixel(xy(0, 4), (250, 251, 252))
        .expect_pixel(xy(1, 4), (250, 251, 252))
        .expect_pixel(xy(2, 4), (250, 251, 252))
        .expect_pixel(xy(3, 4), (250, 251, 252))
        .expect_pixel(xy(4, 4), (250, 251, 252))
        .expect_pixel(xy(1, 5), (250, 251, 252))
        .expect_pixel(xy(3, 5), (250, 251, 252))
        .expect_pixel(xy(0, 6), (250, 251, 252))
        .expect_pixel(xy(2, 6), (250, 251, 252))
        .expect_op("set_data: from=(0, 0), to=(4, 6), data=[0, 0, 0, 0, 0, 0, 250, 251, 252, 0, 0, 0, 250, 251, 252, 0, 0, 0, 250, 251, 252, 0, 0, 0, 250, 251, 252, 0, 0, 0, 250, 251, 252, 250, 251, 252, 250, 251, 252, 250, 251, 252, 250, 251, 252, 0, 0, 0, 250, 251, 252, 0, 0, 0, 250, 251, 252, 0, 0, 0, 250, 251, 252, 250, 251, 252, 250, 251, 252, 250, 251, 252, 250, 251, 252, 0, 0, 0, 250, 251, 252, 0, 0, 0, 250, 251, 252, 0, 0, 0, 250, 251, 252, 0, 0, 0, 250, 251, 252, 0, 0, 0, 0, 0, 0]")
        .check();
}

#[test]
fn test_write_text_no_sync() {
    Tester::new(size(20, 30))
        .op(|l| {
            l.set_sync(false);
            l.set_draw_color((250, 251, 252));
            l.write_text(PixelsXY::new(2, 3), "Hi").unwrap()
        })
        .expect_damage(xy(2, 3), xy(10, 8))
        .expect_pixel(xy(2, 3), (250, 251, 252))
        .expect_pixel(xy(3, 3), (250, 251, 252))
        .expect_pixel(xy(4, 3), (250, 251, 252))
        .expect_pixel(xy(6, 3), (250, 251, 252))
        .expect_pixel(xy(9, 3), (250, 251, 252))
        .expect_pixel(xy(3, 4), (250, 251, 252))
        .expect_pixel(xy(6, 4), (250, 251, 252))
        .expect_pixel(xy(3, 5), (250, 251, 252))
        .expect_pixel(xy(4, 5), (250, 251, 252))
        .expect_pixel(xy(5, 5), (250, 251, 252))
        .expect_pixel(xy(6, 5), (250, 251, 252))
        .expect_pixel(xy(8, 5), (250, 251, 252))
        .expect_pixel(xy(9, 5), (250, 251, 252))
        .expect_pixel(xy(3, 6), (250, 251, 252))
        .expect_pixel(xy(6, 6), (250, 251, 252))
        .expect_pixel(xy(9, 6), (250, 251, 252))
        .expect_pixel(xy(3, 7), (250, 251, 252))
        .expect_pixel(xy(6, 7), (250, 251, 252))
        .expect_pixel(xy(9, 7), (250, 251, 252))
        .expect_pixel(xy(2, 8), (250, 251, 252))
        .expect_pixel(xy(3, 8), (250, 251, 252))
        .expect_pixel(xy(4, 8), (250, 251, 252))
        .expect_pixel(xy(6, 8), (250, 251, 252))
        .expect_pixel(xy(8, 8), (250, 251, 252))
        .expect_pixel(xy(9, 8), (250, 251, 252))
        .expect_pixel(xy(10, 8), (250, 251, 252))
        .check();
}

#[test]
fn test_write_text_clip() {
    Tester::new(size(20, 30))
        .op(|l| {
            l.set_sync(false);
            l.set_draw_color((250, 251, 252));
            l.write_text(PixelsXY::new(17, 27), "Hi").unwrap()
        })
        .expect_damage(xy(17, 27), xy(19, 29))
        .expect_pixel(xy(17, 27), (250, 251, 252))
        .expect_pixel(xy(18, 27), (250, 251, 252))
        .expect_pixel(xy(19, 27), (250, 251, 252))
        .expect_pixel(xy(18, 28), (250, 251, 252))
        .expect_pixel(xy(18, 29), (250, 251, 252))
        .expect_pixel(xy(19, 29), (250, 251, 252))
        .check();
}

#[test]
fn test_draw_circle_sync() {
    Tester::new(size(20, 30))
        .op(|l| l.set_draw_color((50, 51, 52)))
        .op(|l| l.draw_circle(PixelsXY::new(10, 15), 4).unwrap())
        .expect_pixel(xy(7, 13), (50, 51, 52))
        .expect_pixel(xy(7, 14), (50, 51, 52))
        .expect_pixel(xy(7, 15), (50, 51, 52))
        .expect_pixel(xy(7, 16), (50, 51, 52))
        .expect_pixel(xy(7, 17), (50, 51, 52))
        .expect_pixel(xy(8, 12), (50, 51, 52))
        .expect_pixel(xy(8, 18), (50, 51, 52))
        .expect_pixel(xy(9, 12), (50, 51, 52))
        .expect_pixel(xy(9, 18), (50, 51, 52))
        .expect_pixel(xy(10, 12), (50, 51, 52))
        .expect_pixel(xy(10, 18), (50, 51, 52))
        .expect_pixel(xy(11, 12), (50, 51, 52))
        .expect_pixel(xy(11, 18), (50, 51, 52))
        .expect_pixel(xy(12, 12), (50, 51, 52))
        .expect_pixel(xy(12, 18), (50, 51, 52))
        .expect_pixel(xy(13, 13), (50, 51, 52))
        .expect_pixel(xy(13, 14), (50, 51, 52))
        .expect_pixel(xy(13, 15), (50, 51, 52))
        .expect_pixel(xy(13, 16), (50, 51, 52))
        .expect_pixel(xy(13, 17), (50, 51, 52))
        .expect_op("set_data: from=(7, 12), to=(13, 18), data=[0, 0, 0, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 0, 0, 0, 50, 51, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 51, 52, 50, 51, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 51, 52, 50, 51, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 51, 52, 50, 51, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 51, 52, 50, 51, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 51, 52, 0, 0, 0, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 0, 0, 0]")
        .check();
}

#[test]
fn test_draw_circle_no_sync() {
    Tester::new(size(20, 30))
        .op(|l| l.set_draw_color((50, 51, 52)))
        .op(|l| {
            l.set_sync(false);
            l.draw_circle(PixelsXY::new(10, 15), 4).unwrap()
        })
        .expect_damage(xy(7, 12), xy(13, 18))
        .expect_pixel(xy(7, 13), (50, 51, 52))
        .expect_pixel(xy(7, 14), (50, 51, 52))
        .expect_pixel(xy(7, 15), (50, 51, 52))
        .expect_pixel(xy(7, 16), (50, 51, 52))
        .expect_pixel(xy(7, 17), (50, 51, 52))
        .expect_pixel(xy(8, 12), (50, 51, 52))
        .expect_pixel(xy(8, 18), (50, 51, 52))
        .expect_pixel(xy(9, 12), (50, 51, 52))
        .expect_pixel(xy(9, 18), (50, 51, 52))
        .expect_pixel(xy(10, 12), (50, 51, 52))
        .expect_pixel(xy(10, 18), (50, 51, 52))
        .expect_pixel(xy(11, 12), (50, 51, 52))
        .expect_pixel(xy(11, 18), (50, 51, 52))
        .expect_pixel(xy(12, 12), (50, 51, 52))
        .expect_pixel(xy(12, 18), (50, 51, 52))
        .expect_pixel(xy(13, 13), (50, 51, 52))
        .expect_pixel(xy(13, 14), (50, 51, 52))
        .expect_pixel(xy(13, 15), (50, 51, 52))
        .expect_pixel(xy(13, 16), (50, 51, 52))
        .expect_pixel(xy(13, 17), (50, 51, 52))
        .check();
}

#[test]
fn test_draw_circle_clip() {
    Tester::new(size(20, 30))
        .op(|l| l.set_draw_color((50, 51, 52)))
        .op(|l| l.draw_circle(PixelsXY::new(0, 0), 4).unwrap())
        .expect_pixel(xy(0, 3), (50, 51, 52))
        .expect_pixel(xy(1, 3), (50, 51, 52))
        .expect_pixel(xy(2, 3), (50, 51, 52))
        .expect_pixel(xy(3, 0), (50, 51, 52))
        .expect_pixel(xy(3, 1), (50, 51, 52))
        .expect_pixel(xy(3, 2), (50, 51, 52))
        .expect_op("set_data: from=(0, 0), to=(3, 3), data=[0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 51, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 51, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 0, 0, 0]")
        .check();
}

#[test]
fn test_draw_circle_filled_sync() {
    Tester::new(size(20, 30))
        .op(|l| l.set_draw_color((50, 51, 52)))
        .op(|l| l.draw_circle_filled(PixelsXY::new(10, 15), 4).unwrap())
        .expect_pixel(xy(7, 13), (50, 51, 52))
        .expect_pixel(xy(7, 14), (50, 51, 52))
        .expect_pixel(xy(7, 15), (50, 51, 52))
        .expect_pixel(xy(7, 16), (50, 51, 52))
        .expect_pixel(xy(7, 17), (50, 51, 52))
        .expect_pixel(xy(8, 12), (50, 51, 52))
        .expect_pixel(xy(8, 13), (50, 51, 52))
        .expect_pixel(xy(8, 14), (50, 51, 52))
        .expect_pixel(xy(8, 15), (50, 51, 52))
        .expect_pixel(xy(8, 16), (50, 51, 52))
        .expect_pixel(xy(8, 17), (50, 51, 52))
        .expect_pixel(xy(8, 18), (50, 51, 52))
        .expect_pixel(xy(9, 12), (50, 51, 52))
        .expect_pixel(xy(9, 13), (50, 51, 52))
        .expect_pixel(xy(9, 14), (50, 51, 52))
        .expect_pixel(xy(9, 15), (50, 51, 52))
        .expect_pixel(xy(9, 16), (50, 51, 52))
        .expect_pixel(xy(9, 17), (50, 51, 52))
        .expect_pixel(xy(9, 18), (50, 51, 52))
        .expect_pixel(xy(10, 12), (50, 51, 52))
        .expect_pixel(xy(10, 13), (50, 51, 52))
        .expect_pixel(xy(10, 14), (50, 51, 52))
        .expect_pixel(xy(10, 15), (50, 51, 52))
        .expect_pixel(xy(10, 16), (50, 51, 52))
        .expect_pixel(xy(10, 17), (50, 51, 52))
        .expect_pixel(xy(10, 18), (50, 51, 52))
        .expect_pixel(xy(11, 12), (50, 51, 52))
        .expect_pixel(xy(11, 13), (50, 51, 52))
        .expect_pixel(xy(11, 14), (50, 51, 52))
        .expect_pixel(xy(11, 15), (50, 51, 52))
        .expect_pixel(xy(11, 16), (50, 51, 52))
        .expect_pixel(xy(11, 17), (50, 51, 52))
        .expect_pixel(xy(11, 18), (50, 51, 52))
        .expect_pixel(xy(12, 12), (50, 51, 52))
        .expect_pixel(xy(12, 13), (50, 51, 52))
        .expect_pixel(xy(12, 14), (50, 51, 52))
        .expect_pixel(xy(12, 15), (50, 51, 52))
        .expect_pixel(xy(12, 16), (50, 51, 52))
        .expect_pixel(xy(12, 17), (50, 51, 52))
        .expect_pixel(xy(12, 18), (50, 51, 52))
        .expect_pixel(xy(13, 13), (50, 51, 52))
        .expect_pixel(xy(13, 14), (50, 51, 52))
        .expect_pixel(xy(13, 15), (50, 51, 52))
        .expect_pixel(xy(13, 16), (50, 51, 52))
        .expect_pixel(xy(13, 17), (50, 51, 52))
        .expect_op("set_data: from=(7, 12), to=(13, 18), data=[0, 0, 0, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 0, 0, 0, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 0, 0, 0, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 0, 0, 0]")
        .check();
}

#[test]
fn test_draw_circle_filled_no_sync() {
    Tester::new(size(20, 30))
        .op(|l| l.set_draw_color((50, 51, 52)))
        .op(|l| {
            l.set_sync(false);
            l.draw_circle_filled(PixelsXY::new(10, 15), 4).unwrap()
        })
        .expect_damage(xy(7, 12), xy(13, 18))
        .expect_pixel(xy(7, 13), (50, 51, 52))
        .expect_pixel(xy(7, 14), (50, 51, 52))
        .expect_pixel(xy(7, 15), (50, 51, 52))
        .expect_pixel(xy(7, 16), (50, 51, 52))
        .expect_pixel(xy(7, 17), (50, 51, 52))
        .expect_pixel(xy(8, 12), (50, 51, 52))
        .expect_pixel(xy(8, 13), (50, 51, 52))
        .expect_pixel(xy(8, 14), (50, 51, 52))
        .expect_pixel(xy(8, 15), (50, 51, 52))
        .expect_pixel(xy(8, 16), (50, 51, 52))
        .expect_pixel(xy(8, 17), (50, 51, 52))
        .expect_pixel(xy(8, 18), (50, 51, 52))
        .expect_pixel(xy(9, 12), (50, 51, 52))
        .expect_pixel(xy(9, 13), (50, 51, 52))
        .expect_pixel(xy(9, 14), (50, 51, 52))
        .expect_pixel(xy(9, 15), (50, 51, 52))
        .expect_pixel(xy(9, 16), (50, 51, 52))
        .expect_pixel(xy(9, 17), (50, 51, 52))
        .expect_pixel(xy(9, 18), (50, 51, 52))
        .expect_pixel(xy(10, 12), (50, 51, 52))
        .expect_pixel(xy(10, 13), (50, 51, 52))
        .expect_pixel(xy(10, 14), (50, 51, 52))
        .expect_pixel(xy(10, 15), (50, 51, 52))
        .expect_pixel(xy(10, 16), (50, 51, 52))
        .expect_pixel(xy(10, 17), (50, 51, 52))
        .expect_pixel(xy(10, 18), (50, 51, 52))
        .expect_pixel(xy(11, 12), (50, 51, 52))
        .expect_pixel(xy(11, 13), (50, 51, 52))
        .expect_pixel(xy(11, 14), (50, 51, 52))
        .expect_pixel(xy(11, 15), (50, 51, 52))
        .expect_pixel(xy(11, 16), (50, 51, 52))
        .expect_pixel(xy(11, 17), (50, 51, 52))
        .expect_pixel(xy(11, 18), (50, 51, 52))
        .expect_pixel(xy(12, 12), (50, 51, 52))
        .expect_pixel(xy(12, 13), (50, 51, 52))
        .expect_pixel(xy(12, 14), (50, 51, 52))
        .expect_pixel(xy(12, 15), (50, 51, 52))
        .expect_pixel(xy(12, 16), (50, 51, 52))
        .expect_pixel(xy(12, 17), (50, 51, 52))
        .expect_pixel(xy(12, 18), (50, 51, 52))
        .expect_pixel(xy(13, 13), (50, 51, 52))
        .expect_pixel(xy(13, 14), (50, 51, 52))
        .expect_pixel(xy(13, 15), (50, 51, 52))
        .expect_pixel(xy(13, 16), (50, 51, 52))
        .expect_pixel(xy(13, 17), (50, 51, 52))
        .check();
}

#[test]
fn test_draw_circle_filled_clip() {
    Tester::new(size(20, 30))
        .op(|l| l.set_draw_color((50, 51, 52)))
        .op(|l| l.draw_circle_filled(PixelsXY::new(0, 0), 4).unwrap())
        .expect_pixel(xy(0, 0), (50, 51, 52))
        .expect_pixel(xy(0, 1), (50, 51, 52))
        .expect_pixel(xy(0, 2), (50, 51, 52))
        .expect_pixel(xy(0, 3), (50, 51, 52))
        .expect_pixel(xy(1, 0), (50, 51, 52))
        .expect_pixel(xy(1, 1), (50, 51, 52))
        .expect_pixel(xy(1, 2), (50, 51, 52))
        .expect_pixel(xy(1, 3), (50, 51, 52))
        .expect_pixel(xy(2, 0), (50, 51, 52))
        .expect_pixel(xy(2, 1), (50, 51, 52))
        .expect_pixel(xy(2, 2), (50, 51, 52))
        .expect_pixel(xy(2, 3), (50, 51, 52))
        .expect_pixel(xy(3, 0), (50, 51, 52))
        .expect_pixel(xy(3, 1), (50, 51, 52))
        .expect_pixel(xy(3, 2), (50, 51, 52))
        .expect_op("set_data: from=(0, 0), to=(3, 3), data=[50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 0, 0, 0]")
        .check();
}

#[test]
fn test_draw_line_sync() {
    Tester::new(size(20, 30))
        .op(|l| l.set_draw_color((50, 51, 52)))
        .op(|l| l.draw_line(PixelsXY::new(4, 5), PixelsXY::new(8, 9)).unwrap())
        .expect_pixel(xy(4, 5), (50, 51, 52))
        .expect_pixel(xy(5, 6), (50, 51, 52))
        .expect_pixel(xy(6, 7), (50, 51, 52))
        .expect_pixel(xy(7, 8), (50, 51, 52))
        .expect_pixel(xy(8, 9), (50, 51, 52))
        .expect_op("set_data: from=(4, 5), to=(8, 9), data=[50, 51, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 51, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 51, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 51, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 51, 52]")
        .check();
}

#[test]
fn test_draw_line_no_sync() {
    Tester::new(size(20, 30))
        .op(|l| l.set_draw_color((50, 51, 52)))
        .op(|l| {
            l.set_sync(false);
            l.draw_line(PixelsXY::new(4, 5), PixelsXY::new(8, 9)).unwrap()
        })
        .expect_damage(xy(4, 5), xy(8, 9))
        .expect_pixel(xy(4, 5), (50, 51, 52))
        .expect_pixel(xy(5, 6), (50, 51, 52))
        .expect_pixel(xy(6, 7), (50, 51, 52))
        .expect_pixel(xy(7, 8), (50, 51, 52))
        .expect_pixel(xy(8, 9), (50, 51, 52))
        .check();
}

#[test]
fn test_draw_line_clip() {
    Tester::new(size(20, 30))
        .op(|l| l.set_draw_color((50, 51, 52)))
        .op(|l| {
            l.set_sync(false);
            l.draw_line(PixelsXY::new(-2, 10), PixelsXY::new(1, 10)).unwrap()
        })
        .expect_damage(xy(0, 10), xy(1, 10))
        .expect_pixel(xy(0, 10), (50, 51, 52))
        .expect_pixel(xy(1, 10), (50, 51, 52))
        .check();
}

#[test]
fn test_draw_pixel_sync() {
    Tester::new(size(20, 30))
        .op(|l| l.set_draw_color((50, 51, 52)))
        .op(|l| l.draw_pixel(PixelsXY::new(4, 5)).unwrap())
        .expect_pixel(xy(4, 5), (50, 51, 52))
        .expect_op("set_data: from=(4, 5), to=(4, 5), data=[50, 51, 52]")
        .check();
}

#[test]
fn test_draw_pixel_no_sync() {
    Tester::new(size(20, 30))
        .op(|l| l.set_draw_color((50, 51, 52)))
        .op(|l| {
            l.set_sync(false);
            l.draw_pixel(PixelsXY::new(4, 5)).unwrap();
        })
        .expect_damage(xy(4, 5), xy(4, 5))
        .expect_pixel(xy(4, 5), (50, 51, 52))
        .check();
}

#[test]
fn test_draw_pixel_limits() {
    Tester::new(size(20, 30))
        .op(|l| l.set_draw_color((50, 51, 52)))
        .op(|l| l.draw_pixel(PixelsXY::new(0, 0)).unwrap())
        .expect_pixel(xy(0, 0), (50, 51, 52))
        .expect_op("set_data: from=(0, 0), to=(0, 0), data=[50, 51, 52]")
        .check();

    Tester::new(size(20, 30))
        .op(|l| l.set_draw_color((50, 51, 52)))
        .op(|l| l.draw_pixel(PixelsXY::new(19, 29)).unwrap())
        .expect_pixel(xy(19, 29), (50, 51, 52))
        .expect_op("set_data: from=(19, 29), to=(19, 29), data=[50, 51, 52]")
        .check();
}

#[test]
fn test_draw_pixel_out_of_bounds() {
    Tester::new(size(20, 30))
        .op(|l| l.set_draw_color((50, 51, 52)))
        .op(|l| l.draw_pixel(PixelsXY::new(-5, 10)).unwrap())
        .check();

    Tester::new(size(20, 30))
        .op(|l| l.set_draw_color((50, 51, 52)))
        .op(|l| l.draw_pixel(PixelsXY::new(5, -10)).unwrap())
        .check();

    Tester::new(size(20, 30))
        .op(|l| l.set_draw_color((50, 51, 52)))
        .op(|l| l.draw_pixel(PixelsXY::new(20, 30)).unwrap())
        .check();
}

#[test]
fn test_draw_rect_sync() {
    Tester::new(size(20, 30))
        .op(|l| {
            l.set_draw_color((50, 51, 52));
            l.draw_rect(
                PixelsXY::new(4, 5),
                SizeInPixels::new(2, 3),
            )
            .unwrap()
        })
        .expect_pixel(xy(4, 5), (50, 51, 52))
        .expect_pixel(xy(4, 6), (50, 51, 52))
        .expect_pixel(xy(4, 7), (50, 51, 52))
        .expect_pixel(xy(5, 5), (50, 51, 52))
        .expect_pixel(xy(5, 6), (50, 51, 52))
        .expect_pixel(xy(5, 7), (50, 51, 52))
        .expect_op("set_data: from=(4, 5), to=(5, 7), data=[50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52]")
        .check();
}

#[test]
fn test_draw_rect_no_sync() {
    Tester::new(size(20, 30))
        .op(|l| {
            l.set_sync(false);
            l.set_draw_color((50, 51, 52));
            l.draw_rect(PixelsXY::new(4, 5), SizeInPixels::new(2, 3)).unwrap()
        })
        .expect_pixel(xy(4, 5), (50, 51, 52))
        .expect_pixel(xy(4, 6), (50, 51, 52))
        .expect_pixel(xy(4, 7), (50, 51, 52))
        .expect_pixel(xy(5, 5), (50, 51, 52))
        .expect_pixel(xy(5, 6), (50, 51, 52))
        .expect_pixel(xy(5, 7), (50, 51, 52))
        .expect_damage(xy(4, 5), xy(5, 7))
        .check();
}

#[test]
fn test_draw_rect_limits() {
    Tester::new(size(2, 3))
        .op(|l| {
            l.set_draw_color((50, 51, 52));
            l.draw_rect(
                PixelsXY::new(0, 0),
                SizeInPixels::new(2, 3),
            )
            .unwrap()
        })
        .expect_pixel(xy(0, 0), (50, 51, 52))
        .expect_pixel(xy(0, 1), (50, 51, 52))
        .expect_pixel(xy(0, 2), (50, 51, 52))
        .expect_pixel(xy(1, 0), (50, 51, 52))
        .expect_pixel(xy(1, 1), (50, 51, 52))
        .expect_pixel(xy(1, 2), (50, 51, 52))
        .expect_op("set_data: from=(0, 0), to=(1, 2), data=[50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52]")
        .check();
}

#[test]
fn test_draw_rect_clip() {
    Tester::new(size(20, 30))
        .op(|l| {
            l.set_draw_color((50, 51, 52));
            l.draw_rect(PixelsXY::new(-2, 28), SizeInPixels::new(3, 10)).unwrap()
        })
        .expect_pixel(xy(0, 28), (50, 51, 52))
        .expect_pixel(xy(0, 29), (50, 51, 52))
        .expect_op("set_data: from=(0, 28), to=(0, 29), data=[50, 51, 52, 50, 51, 52]")
        .check();
}

#[test]
fn test_draw_rect_filled_sync() {
    Tester::new(size(20, 30))
        .op(|l| {
            l.set_draw_color((50, 51, 52));
            l.draw_rect_filled(
                PixelsXY::new(4, 5),
                SizeInPixels::new(2, 3),
            )
            .unwrap()
        })
        .expect_pixel(xy(4, 5), (50, 51, 52))
        .expect_pixel(xy(4, 6), (50, 51, 52))
        .expect_pixel(xy(4, 7), (50, 51, 52))
        .expect_pixel(xy(5, 5), (50, 51, 52))
        .expect_pixel(xy(5, 6), (50, 51, 52))
        .expect_pixel(xy(5, 7), (50, 51, 52))
        .expect_op("set_data: from=(4, 5), to=(5, 7), data=[50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52]")
        .check();
}

#[test]
fn test_draw_rect_filled_no_sync() {
    Tester::new(size(20, 30))
        .op(|l| {
            l.set_draw_color((50, 51, 52));
            l.set_sync(false);
            l.draw_rect_filled(PixelsXY::new(4, 5), SizeInPixels::new(2, 3)).unwrap()
        })
        .expect_pixel(xy(4, 5), (50, 51, 52))
        .expect_pixel(xy(4, 6), (50, 51, 52))
        .expect_pixel(xy(4, 7), (50, 51, 52))
        .expect_pixel(xy(5, 5), (50, 51, 52))
        .expect_pixel(xy(5, 6), (50, 51, 52))
        .expect_pixel(xy(5, 7), (50, 51, 52))
        .expect_damage(xy(4, 5), xy(5, 7))
        .check();
}

#[test]
fn test_draw_rect_filled_limits() {
    Tester::new(size(2, 3))
        .op(|l| {
            l.set_draw_color((50, 51, 52));
            l.draw_rect_filled(
                PixelsXY::new(0, 0),
                SizeInPixels::new(2, 3),
            )
            .unwrap()
        })
        .expect_pixel(xy(0, 0), (50, 51, 52))
        .expect_pixel(xy(0, 1), (50, 51, 52))
        .expect_pixel(xy(0, 2), (50, 51, 52))
        .expect_pixel(xy(1, 0), (50, 51, 52))
        .expect_pixel(xy(1, 1), (50, 51, 52))
        .expect_pixel(xy(1, 2), (50, 51, 52))
        .expect_op("set_data: from=(0, 0), to=(1, 2), data=[50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52, 50, 51, 52]")
        .check();
}

#[test]
fn test_draw_rect_filled_clip() {
    Tester::new(size(20, 30))
        .op(|l| {
            l.set_draw_color((50, 51, 52));
            l.draw_rect_filled(PixelsXY::new(-2, 28), SizeInPixels::new(3, 10)).unwrap()
        })
        .expect_pixel(xy(0, 28), (50, 51, 52))
        .expect_pixel(xy(0, 29), (50, 51, 52))
        .expect_op("set_data: from=(0, 28), to=(0, 29), data=[50, 51, 52, 50, 51, 52]")
        .check();
}
