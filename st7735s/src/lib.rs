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

/***************************************************************************************************
* | file        :    LCD_Driver.c
* | version     :    V1.0
* | date        :    2017-10-16
* | function    :    On the ST7735S chip driver and clear screen, drawing lines, drawing, writing
                     and other functions to achieve
***************************************************************************************************/

//! Console driver for the ST7735S LCD.

use async_channel::{Receiver, TryRecvError};
use async_trait::async_trait;
use endbasic_std::console::graphics::InputOps;
use endbasic_std::console::{
    CharsXY, ClearType, Console, GraphicsConsole, Key, PixelsXY, SizeInPixels, RGB,
};
use endbasic_std::gfx::lcd::{to_xy_size, BufferedLcd, Font8, Lcd, LcdSize, LcdXY, RGB565Pixel};
use endbasic_std::gpio::{Pin, PinMode, Pins};
use endbasic_std::spi::{SpiBus, SpiFactory, SpiMode};
use std::io;
use std::sync::{Arc, Mutex};
use std::time::Duration;

const INPUT_PINS: &[(Pin, Key)] = &[
    (Pin(6), Key::ArrowUp),
    (Pin(19), Key::ArrowDown),
    (Pin(5), Key::ArrowLeft),
    (Pin(26), Key::ArrowRight),
    (Pin(13), Key::NewLine),
    (Pin(21), Key::Char('1')),
    (Pin(20), Key::Char('2')),
    (Pin(16), Key::Char('3')),
];

const OUTPUT_PIN_CS: Pin = Pin(8);
const OUTPUT_PIN_RST: Pin = Pin(27);
const OUTPUT_PIN_DC: Pin = Pin(25);
const OUTPUT_PIN_BL: Pin = Pin(24);

/// Input handler for the ST7735S console.
///
/// This driver reads the (limited) physical buttons of the ST7735S device and multiplexes them with
/// a real keyboard.
struct ST7735SInput<K> {
    on_button_rx: Receiver<Key>,
    keyboard: K,
}

impl<K> ST7735SInput<K> {
    /// Constructs a new input handler that reads button presses through `pins` and multiplexes them
    /// with `keyboard`.
    fn new<P: Pins + Send + 'static>(pins: Arc<Mutex<P>>, keyboard: K) -> io::Result<Self> {
        let (on_button_tx, on_button_rx) = async_channel::unbounded();

        {
            let mut pins = pins.lock().unwrap();
            for (pin, _key) in INPUT_PINS {
                pins.setup(*pin, PinMode::InPullUp)?;
            }
        }

        tokio::task::spawn(async move {
            loop {
                let mut keys = vec![];
                {
                    let mut pins = pins.lock().unwrap();
                    for (pin, key) in INPUT_PINS {
                        match pins.read(*pin) {
                            Ok(false) => keys.push(*key),
                            Ok(true) => (),
                            Err(e) => {
                                eprintln!("Ignoring button {:?} due to error: {}", key, e);
                                continue;
                            }
                        };
                    }
                }

                for key in keys {
                    if let Err(e) = on_button_tx.send(key).await {
                        eprintln!("Ignoring button {:?} due to error: {}", key, e);
                    }
                }

                tokio::time::sleep(Duration::from_millis(50)).await;
            }
        });

        Ok(Self { on_button_rx, keyboard })
    }
}

#[async_trait(?Send)]
impl<K: InputOps> InputOps for ST7735SInput<K> {
    async fn poll_key(&mut self) -> io::Result<Option<Key>> {
        match self.on_button_rx.try_recv() {
            Ok(k) => Ok(Some(k)),
            Err(TryRecvError::Empty) => self.keyboard.poll_key().await,
            Err(TryRecvError::Closed) => Ok(Some(Key::Eof)),
        }
    }

    async fn read_key(&mut self) -> io::Result<Key> {
        tokio::select! {
            result = self.on_button_rx.recv() => {
                match result {
                    Ok(k) => Ok(k),
                    Err(_) => Ok(Key::Eof),
                }
            }
            result = self.keyboard.read_key() => result,
        }
    }
}

/// Writes arbitrary data to the SPI bus.
///
/// The input data is chunked to respect the maximum write size accepted by the SPI bus.
fn lcd_write<B: SpiBus>(spi_bus: &mut B, data: &[u8]) -> io::Result<()> {
    // TODO(jmmv): Do we really need to chunk the data ourselves, or can we try to write it
    // all to the bus and then expect the write to return partial results?
    for chunk in data.chunks(spi_bus.max_size()) {
        let mut i = 0;
        loop {
            let n = spi_bus.write(&chunk[i..])?;
            if n == chunk.len() - i {
                break;
            }
            i += n;
        }
    }
    Ok(())
}

/// LCD handler for the ST7735S console.
struct ST7735SLcd<P: Pins, B> {
    pins: Arc<Mutex<P>>,
    spi_bus: B,
    size_pixels: LcdSize,
}

impl<P: Pins, B: SpiBus> ST7735SLcd<P, B> {
    /// Initializes the LCD.
    pub fn new(pins: Arc<Mutex<P>>, spi_factory: SpiFactory<B>) -> io::Result<Self> {
        {
            let mut pins = pins.lock().unwrap();
            for pin in [OUTPUT_PIN_CS, OUTPUT_PIN_RST, OUTPUT_PIN_DC, OUTPUT_PIN_BL] {
                pins.setup(pin, PinMode::Out)?;
            }
        }

        let spi_bus = spi_factory(0, 0, 9000000, SpiMode::Mode0)?;

        let size_pixels = LcdSize { width: 128, height: 128 };

        let mut device = Self { pins, spi_bus, size_pixels };

        device.lcd_init()?;

        Ok(device)
    }

    /// Selects the registers to affect by the next data write.
    fn lcd_write_reg(pins: &mut P, spi_bus: &mut B, regs: &[u8]) -> io::Result<()> {
        pins.write(OUTPUT_PIN_DC, false)?;
        lcd_write(spi_bus, regs)
    }

    /// Writes data to the device.  A register should have been selected before.
    fn lcd_write_data(pins: &mut P, spi_bus: &mut B, data: &[u8]) -> io::Result<()> {
        pins.write(OUTPUT_PIN_DC, true)?;
        lcd_write(spi_bus, data)
    }

    /// Resets the LCD.
    fn lcd_reset(pins: &mut P) -> io::Result<()> {
        pins.write(OUTPUT_PIN_RST, true)?;
        std::thread::sleep(Duration::from_millis(100));
        pins.write(OUTPUT_PIN_RST, false)?;
        std::thread::sleep(Duration::from_millis(100));
        pins.write(OUTPUT_PIN_RST, true)?;
        std::thread::sleep(Duration::from_millis(100));
        Ok(())
    }

    /// Sets up the LCD registers.
    fn lcd_init_reg(pins: &mut P, spi_bus: &mut B) -> io::Result<()> {
        // ST7735R Frame Rate.
        Self::lcd_write_reg(pins, spi_bus, &[0xb1])?;
        Self::lcd_write_data(pins, spi_bus, &[0x01, 0x2c, 0x2d])?;

        Self::lcd_write_reg(pins, spi_bus, &[0xb2])?;
        Self::lcd_write_data(pins, spi_bus, &[0x01, 0x2c, 0x2d])?;

        Self::lcd_write_reg(pins, spi_bus, &[0xb3])?;
        Self::lcd_write_data(pins, spi_bus, &[0x01, 0x2c, 0x2d, 0x01, 0x2c, 0x2d])?;

        // Column inversion.
        Self::lcd_write_reg(pins, spi_bus, &[0xb4])?;
        Self::lcd_write_data(pins, spi_bus, &[0x07])?;

        // ST7735R Power Sequence.
        Self::lcd_write_reg(pins, spi_bus, &[0xc0])?;
        Self::lcd_write_data(pins, spi_bus, &[0xa2, 0x02, 0x84])?;
        Self::lcd_write_reg(pins, spi_bus, &[0xc1])?;
        Self::lcd_write_data(pins, spi_bus, &[0xc5])?;

        Self::lcd_write_reg(pins, spi_bus, &[0xc2])?;
        Self::lcd_write_data(pins, spi_bus, &[0x0a, 0x00])?;

        Self::lcd_write_reg(pins, spi_bus, &[0xc3])?;
        Self::lcd_write_data(pins, spi_bus, &[0x8a, 0x2a])?;
        Self::lcd_write_reg(pins, spi_bus, &[0xc4])?;
        Self::lcd_write_data(pins, spi_bus, &[0x8a, 0xee])?;

        // VCOM.
        Self::lcd_write_reg(pins, spi_bus, &[0xc5])?;
        Self::lcd_write_data(pins, spi_bus, &[0x0e])?;

        // ST7735R Gamma Sequence.
        Self::lcd_write_reg(pins, spi_bus, &[0xe0])?;
        Self::lcd_write_data(
            pins,
            spi_bus,
            &[
                0x0f, 0x1a, 0x0f, 0x18, 0x2f, 0x28, 0x20, 0x22, 0x1f, 0x1b, 0x23, 0x37, 0x00, 0x07,
                0x02, 0x10,
            ],
        )?;

        Self::lcd_write_reg(pins, spi_bus, &[0xe1])?;
        Self::lcd_write_data(
            pins,
            spi_bus,
            &[
                0x0f, 0x1b, 0x0f, 0x17, 0x33, 0x2c, 0x29, 0x2e, 0x30, 0x30, 0x39, 0x3f, 0x00, 0x07,
                0x03, 0x10,
            ],
        )?;

        // Enable test command.
        Self::lcd_write_reg(pins, spi_bus, &[0xf0])?;
        Self::lcd_write_data(pins, spi_bus, &[0x01])?;

        // Disable ram power save mode.
        Self::lcd_write_reg(pins, spi_bus, &[0xf6])?;
        Self::lcd_write_data(pins, spi_bus, &[0x00])?;

        // 65k mode.
        Self::lcd_write_reg(pins, spi_bus, &[0x3a])?;
        Self::lcd_write_data(pins, spi_bus, &[0x05])?;

        Ok(())
    }

    /// Initializes the LCD scan direction and pixel color encoding.
    fn lcd_set_gram_scan_way(pins: &mut P, spi_bus: &mut B) -> io::Result<()> {
        Self::lcd_write_reg(pins, spi_bus, &[0x36])?; // MX, MY, RGB mode.
        let scan_dir = 0x40 | 0x20; // X, Y.
        let rgb_mode = 0x08; // RGB for 1.44in display.
        Self::lcd_write_data(pins, spi_bus, &[scan_dir | rgb_mode])?;
        Ok(())
    }

    /// Initializes the LCD.
    fn lcd_init(&mut self) -> io::Result<()> {
        let mut pins = self.pins.lock().unwrap();

        // I'm not sure what this does.  This does not have an effect on Linux but
        // setting this to high on NetBSD causes the LCD to remain lit up.
        pins.write(OUTPUT_PIN_CS, false)?;

        pins.write(OUTPUT_PIN_BL, true)?;

        Self::lcd_reset(&mut *pins)?;
        Self::lcd_init_reg(&mut *pins, &mut self.spi_bus)?;

        Self::lcd_set_gram_scan_way(&mut *pins, &mut self.spi_bus)?;
        std::thread::sleep(Duration::from_millis(200));

        Self::lcd_write_reg(&mut *pins, &mut self.spi_bus, &[0x11])?;
        std::thread::sleep(Duration::from_millis(200));

        // Turn display on.
        Self::lcd_write_reg(&mut *pins, &mut self.spi_bus, &[0x29])?;

        Ok(())
    }

    /// Configures the LCD so that the next write, which carries pixel data, affects the specified
    /// region.
    fn lcd_set_window(pins: &mut P, spi_bus: &mut B, xy: LcdXY, size: LcdSize) -> io::Result<()> {
        let adjust_x = 1;
        let adjust_y = 2;

        let x1 = ((xy.x & 0xff) + adjust_x) as u8;
        let x2 = (((xy.x + size.width) + adjust_x - 1) & 0xff) as u8;
        let y1 = ((xy.y & 0xff) + adjust_y) as u8;
        let y2 = (((xy.y + size.height) + adjust_y - 1) & 0xff) as u8;

        Self::lcd_write_reg(pins, spi_bus, &[0x2a])?;
        Self::lcd_write_data(pins, spi_bus, &[0x00, x1, 0x00, x2])?;

        Self::lcd_write_reg(pins, spi_bus, &[0x2b])?;
        Self::lcd_write_data(pins, spi_bus, &[0x00, y1, 0x00, y2])?;

        Self::lcd_write_reg(pins, spi_bus, &[0x2c])?;

        Ok(())
    }
}

impl<P: Pins, B> Drop for ST7735SLcd<P, B> {
    fn drop(&mut self) {
        let mut pins = self.pins.lock().unwrap();
        let _result = pins.write(OUTPUT_PIN_BL, false);
    }
}

impl<P: Pins, B: SpiBus> Lcd for ST7735SLcd<P, B> {
    type Pixel = RGB565Pixel;

    fn info(&self) -> (LcdSize, usize) {
        (self.size_pixels, 2)
    }

    fn encode(&self, rgb: RGB) -> Self::Pixel {
        let rgb = (u16::from(rgb.0), u16::from(rgb.1), u16::from(rgb.2));

        let pixel: u16 = ((rgb.0 >> 3) << 11) | ((rgb.1 >> 2) << 5) | (rgb.2 >> 3);

        let high = (pixel >> 8) as u8;
        let low = (pixel & 0xff) as u8;
        RGB565Pixel([high, low])
    }

    fn set_data(&mut self, x1y1: LcdXY, x2y2: LcdXY, data: &[u8]) -> io::Result<()> {
        let (xy, size) = to_xy_size(x1y1, x2y2);
        let mut pins = self.pins.lock().unwrap();
        Self::lcd_set_window(&mut *pins, &mut self.spi_bus, xy, size)?;
        Self::lcd_write_data(&mut *pins, &mut self.spi_bus, data)
    }
}

/// Console implementation using an ST7735S LCD.
pub struct ST7735SConsole<P: Pins + Send, B: SpiBus, K> {
    /// The graphical console itself.  We wrap it in a struct to prevent leaking all auxiliary types
    /// outside of this crate.
    inner: GraphicsConsole<ST7735SInput<K>, BufferedLcd<ST7735SLcd<P, B>, Font8>>,
}

#[async_trait(?Send)]
impl<P: Pins + Send, B: SpiBus, K: InputOps> Console for ST7735SConsole<P, B, K> {
    fn clear(&mut self, how: ClearType) -> io::Result<()> {
        self.inner.clear(how)
    }

    fn color(&self) -> (Option<u8>, Option<u8>) {
        self.inner.color()
    }

    fn set_color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()> {
        self.inner.set_color(fg, bg)
    }

    fn enter_alt(&mut self) -> io::Result<()> {
        self.inner.enter_alt()
    }

    fn hide_cursor(&mut self) -> io::Result<()> {
        self.inner.hide_cursor()
    }

    fn is_interactive(&self) -> bool {
        self.inner.is_interactive()
    }

    fn leave_alt(&mut self) -> io::Result<()> {
        self.inner.leave_alt()
    }

    fn locate(&mut self, pos: CharsXY) -> io::Result<()> {
        self.inner.locate(pos)
    }

    fn move_within_line(&mut self, off: i16) -> io::Result<()> {
        self.inner.move_within_line(off)
    }

    fn print(&mut self, text: &str) -> io::Result<()> {
        self.inner.print(text)
    }

    async fn poll_key(&mut self) -> io::Result<Option<Key>> {
        self.inner.poll_key().await
    }

    async fn read_key(&mut self) -> io::Result<Key> {
        self.inner.read_key().await
    }

    fn show_cursor(&mut self) -> io::Result<()> {
        self.inner.show_cursor()
    }

    fn size_chars(&self) -> io::Result<CharsXY> {
        self.inner.size_chars()
    }

    fn size_pixels(&self) -> io::Result<SizeInPixels> {
        self.inner.size_pixels()
    }

    fn write(&mut self, text: &str) -> io::Result<()> {
        self.inner.write(text)
    }

    fn draw_circle(&mut self, center: PixelsXY, radius: u16) -> io::Result<()> {
        self.inner.draw_circle(center, radius)
    }

    fn draw_circle_filled(&mut self, center: PixelsXY, radius: u16) -> io::Result<()> {
        self.inner.draw_circle_filled(center, radius)
    }

    fn draw_line(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        self.inner.draw_line(x1y1, x2y2)
    }

    fn draw_pixel(&mut self, xy: PixelsXY) -> io::Result<()> {
        self.inner.draw_pixel(xy)
    }

    fn draw_rect(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        self.inner.draw_rect(x1y1, x2y2)
    }

    fn draw_rect_filled(&mut self, x1y1: PixelsXY, x2y2: PixelsXY) -> io::Result<()> {
        self.inner.draw_rect_filled(x1y1, x2y2)
    }

    fn sync_now(&mut self) -> io::Result<()> {
        self.inner.sync_now()
    }

    fn set_sync(&mut self, enabled: bool) -> io::Result<bool> {
        self.inner.set_sync(enabled)
    }
}

/// Initializes a new console on a ST7735S LCD.
pub fn new_console<P: Pins + Send + 'static, B: SpiBus, K: InputOps>(
    pins: P,
    new_spi: SpiFactory<B>,
    keyboard: K,
) -> io::Result<ST7735SConsole<P, B, K>> {
    let pins = Arc::from(Mutex::from(pins));
    let lcd = ST7735SLcd::new(pins.clone(), new_spi)?;
    let input = ST7735SInput::new(pins, keyboard)?;
    let lcd = BufferedLcd::new(lcd, Font8::default());
    let inner = GraphicsConsole::new(input, lcd)?;
    Ok(ST7735SConsole { inner })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    #[derive(Default)]
    struct MockSpiBus {
        max_size: usize,

        writes: Vec<Vec<u8>>,
    }

    impl Write for MockSpiBus {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            let partial = if buf.len() < self.max_size { buf } else { &buf[0..self.max_size] };
            self.writes.push(partial.to_owned());
            Ok(partial.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    impl SpiBus for MockSpiBus {
        fn max_size(&self) -> usize {
            self.max_size
        }
    }

    #[test]
    fn test_lcd_write_shorter_than_max_size() {
        let mut bus = MockSpiBus { max_size: 100, ..Default::default() };
        lcd_write(&mut bus, &[0, 1, 2, 3, 4]).unwrap();
        assert_eq!(vec![vec![0, 1, 2, 3, 4]], bus.writes);
    }

    #[test]
    fn test_lcd_write_equal_to_max_size() {
        let mut bus = MockSpiBus { max_size: 3, ..Default::default() };
        lcd_write(&mut bus, &[0, 1, 2]).unwrap();
        assert_eq!(vec![vec![0, 1, 2]], bus.writes);
    }

    #[test]
    fn test_lcd_write_greater_than_max_size() {
        let mut bus = MockSpiBus { max_size: 6, ..Default::default() };
        lcd_write(&mut bus, &[0, 1, 2, 3, 4, 5, 6]).unwrap();
        assert_eq!(vec![vec![0, 1, 2, 3, 4, 5], vec![6]], bus.writes);
    }
}
