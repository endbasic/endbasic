// EndBASIC
// Copyright 2021 Julio Merino
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

//! Commands for graphical console interaction.

use crate::console::{Console, PixelsXY};
use async_trait::async_trait;
use endbasic_core::ast::{ArgSep, Expr, Value, VarType};
use endbasic_core::exec::Machine;
use endbasic_core::syms::{
    CallError, CallableMetadata, CallableMetadataBuilder, Command, CommandResult,
};
use std::cell::RefCell;
use std::rc::Rc;

/// Category description for all symbols provided by this module.
const CATEGORY: &str = "Graphics
The EndBASIC console overlays text and graphics in the same canvas.  The consequence of this \
design choice is that the console has two coordinate systems: the character-based system, used by
the commands described in HELP CONSOLE, and the pixel-based system, used by the commands described \
in this section.";

/// Parses an expression that represents a single coordinate.
async fn parse_coordinate(expr: &Expr, machine: &mut Machine) -> Result<usize, CallError> {
    match expr.eval(machine.get_mut_symbols()).await? {
        Value::Integer(i) if i >= 0 => Ok(i as usize),
        Value::Integer(i) => {
            Err(CallError::ArgumentError(format!("Coordinate {} out of range", i)))
        }
        _ => Err(CallError::ArgumentError(format!("Coordinate {:?} must be an integer", expr))),
    }
}

/// Parses a pair of expressions that represent an (x,y) coordinate pair.
async fn parse_coordinates(
    xexpr: &Expr,
    yexpr: &Expr,
    machine: &mut Machine,
) -> Result<PixelsXY, CallError> {
    Ok(PixelsXY {
        x: parse_coordinate(xexpr, machine).await?,
        y: parse_coordinate(yexpr, machine).await?,
    })
}

/// The `GFX_LINE` command.
pub struct GfxLineCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxLineCommand {
    /// Creates a new `GFX_LINE` command that draws a line on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_LINE", VarType::Void)
                .with_syntax("x1%, y1%, x2%, y2%")
                .with_category(CATEGORY)
                .with_description(
                    "Draws a line from (x1,y1) to (x2,y2).
The line is drawn using the foreground color as selected by COLOR.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Command for GfxLineCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        let (x1y1, x2y2) = match args {
            [(Some(x1), ArgSep::Long), (Some(y1), ArgSep::Long), (Some(x2), ArgSep::Long), (Some(y2), ArgSep::End)] => {
                (
                    parse_coordinates(x1, y1, machine).await?,
                    parse_coordinates(x2, y2, machine).await?,
                )
            }
            _ => {
                return Err(CallError::ArgumentError(
                    "GFX_LINE takes four integer arguments separated by commas".to_owned(),
                ))
            }
        };

        self.console.borrow_mut().draw_line(x1y1, x2y2)?;
        Ok(())
    }
}

/// The `GFX_PIXEL` command.
pub struct GfxPixelCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxPixelCommand {
    /// Creates a new `GFX_PIXEL` command that draws a single pixel on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_PIXEL", VarType::Void)
                .with_syntax("x%, y%")
                .with_category(CATEGORY)
                .with_description(
                    "Draws a pixel at (x,y).
The pixel is drawn using the foreground color as selected by COLOR.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Command for GfxPixelCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        let xy = match args {
            [(Some(x), ArgSep::Long), (Some(y), ArgSep::End)] => {
                parse_coordinates(x, y, machine).await?
            }
            _ => {
                return Err(CallError::ArgumentError(
                    "GFX_PIXEL takes two integer arguments separated by commas".to_owned(),
                ))
            }
        };

        self.console.borrow_mut().draw_pixel(xy)?;
        Ok(())
    }
}

/// The `GFX_RECT` command.
pub struct GfxRectCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxRectCommand {
    /// Creates a new `GFX_RECT` command that draws an empty rectangle on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_RECT", VarType::Void)
                .with_syntax("x1%, y1%, x2%, y2%")
                .with_category(CATEGORY)
                .with_description(
                    "Draws a rectangle from (x1,y1) to (x2,y2).
The outline of the rectangle is drawn using the foreground color as selected by COLOR and the \
area of the rectangle is left untouched.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Command for GfxRectCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        let (x1y1, x2y2) = match args {
            [(Some(x1), ArgSep::Long), (Some(y1), ArgSep::Long), (Some(x2), ArgSep::Long), (Some(y2), ArgSep::End)] => {
                (
                    parse_coordinates(x1, y1, machine).await?,
                    parse_coordinates(x2, y2, machine).await?,
                )
            }
            _ => {
                return Err(CallError::ArgumentError(
                    "GFX_RECT takes four integer arguments separated by commas".to_owned(),
                ))
            }
        };

        self.console.borrow_mut().draw_rect(x1y1, x2y2)?;
        Ok(())
    }
}

/// The `GFX_RECTF` command.
pub struct GfxRectfCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxRectfCommand {
    /// Creates a new `GFX_RECTF` command that draws a filled rectangle on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_RECTF", VarType::Void)
                .with_syntax("x1%, y1%, x2%, y2%")
                .with_category(CATEGORY)
                .with_description(
                    "Draws a filled rectangle from (x1,y1) to (x2,y2).
The outline and area of the rectangle are drawn using the foreground color as selected by COLOR.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Command for GfxRectfCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        let (x1y1, x2y2) = match args {
            [(Some(x1), ArgSep::Long), (Some(y1), ArgSep::Long), (Some(x2), ArgSep::Long), (Some(y2), ArgSep::End)] => {
                (
                    parse_coordinates(x1, y1, machine).await?,
                    parse_coordinates(x2, y2, machine).await?,
                )
            }
            _ => {
                return Err(CallError::ArgumentError(
                    "GFX_RECTF takes four integer arguments separated by commas".to_owned(),
                ))
            }
        };

        self.console.borrow_mut().draw_rect_filled(x1y1, x2y2)?;
        Ok(())
    }
}

/// The `GFX_SYNC` command.
pub struct GfxSyncCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxSyncCommand {
    /// Creates a new `GFX_SYNC` command that controls video syncing on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_SYNC", VarType::Void)
                .with_syntax("[enabled?]")
                .with_category(CATEGORY)
                .with_description(
                    "Controls the video syncing flag and/or forces a sync.
With no arguments, this command triggers a video sync without updating the video syncing flag.  \
When enabled? is specified, this updates the video syncing flag accordingly and triggers a video \
sync if enabled? is TRUE.
When video syncing is enabled, all console commands immediately refresh the console.  This is \
useful to see the effects of the commands right away, which is why this is the default mode in the \
interpreter.  However, this is a *very* inefficient way of drawing.
When video syncing is disabled, all console updates are buffered until video syncing is enabled \
again.  This is perfect to draw complex graphics efficiently.  If this is what you want to do, \
you should disable syncing first, render a frame, call GFX_SYNC to flush the frame, repeat until \
you are done, and then enable video syncing again.
WARNING: Be aware that if you disable video syncing in the interactive interpreter, you will not \
be able to see what you are typing any longer until you reenable video syncing.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Command for GfxSyncCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, args: &[(Option<Expr>, ArgSep)], machine: &mut Machine) -> CommandResult {
        match args {
            [] => self.console.borrow_mut().sync_now()?,
            [(Some(b), ArgSep::End)] => match b.eval(machine.get_mut_symbols()).await? {
                Value::Boolean(b) => self.console.borrow_mut().set_sync(b)?,
                _ => {
                    return Err(CallError::ArgumentError(
                        "Argument to GFX_SYNC must be a boolean".to_owned(),
                    ))
                }
            },
            _ => {
                return Err(CallError::ArgumentError(
                    "GFX_SYNC takes zero or one argument".to_owned(),
                ))
            }
        }
        Ok(())
    }
}

/// Adds all console-related commands for the given `console` to the `machine`.
pub fn add_all(machine: &mut Machine, console: Rc<RefCell<dyn Console>>) {
    machine.add_command(GfxLineCommand::new(console.clone()));
    machine.add_command(GfxPixelCommand::new(console.clone()));
    machine.add_command(GfxRectCommand::new(console.clone()));
    machine.add_command(GfxRectfCommand::new(console.clone()));
    machine.add_command(GfxSyncCommand::new(console));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;

    /// Verifies error conditions for a command named `name` that takes to X/Y pairs.
    fn check_errors_two_xy(name: &'static str) {
        for args in &["1, 2, , 4", "1, 2, 3", "1, 2, 3, 4, 5", "2; 3, 4"] {
            check_stmt_err(
                &format!("{} takes four integer arguments separated by commas", name),
                &format!("{} {}", name, args),
            );
        }

        for args in &["-1, 1, 1, 1", "1, -1, 1, 1", "1, 1, -1, 1", "1, 1, 1, -1"] {
            check_stmt_err("Coordinate -1 out of range", &format!("{} {}", name, args));
        }

        for args in &["\"a\", 1, 1, 1", "1, \"a\", 1, 1", "1, 1, \"a\", 1", "1, 1, 1, \"a\""] {
            check_stmt_err(
                "Coordinate Text(\"a\") must be an integer",
                &format!("{} {}", name, args),
            );
        }
    }

    #[test]
    fn test_gfx_line_ok() {
        Tester::default()
            .run("GFX_LINE 1, 2, 3, 4")
            .expect_output([CapturedOut::DrawLine(
                PixelsXY { x: 1, y: 2 },
                PixelsXY { x: 3, y: 4 },
            )])
            .check();
    }

    #[test]
    fn test_gfx_line_errors() {
        check_errors_two_xy("GFX_LINE");
    }

    #[test]
    fn test_gfx_pixel_ok() {
        Tester::default()
            .run("GFX_PIXEL 1, 2")
            .expect_output([CapturedOut::DrawPixel(PixelsXY { x: 1, y: 2 })])
            .check();
    }

    #[test]
    fn test_gfx_pixel_errors() {
        for cmd in &["GFX_PIXEL , 2", "GFX_PIXEL 1, 2, 3", "GFX_PIXEL 1", "GFX_PIXEL 1; 2"] {
            check_stmt_err("GFX_PIXEL takes two integer arguments separated by commas", cmd);
        }

        for cmd in &["GFX_PIXEL -1, 1", "GFX_PIXEL 1, -1"] {
            check_stmt_err("Coordinate -1 out of range", cmd);
        }

        for cmd in &["GFX_PIXEL \"a\", 1", "GFX_PIXEL 1, \"a\""] {
            check_stmt_err("Coordinate Text(\"a\") must be an integer", cmd);
        }
    }

    #[test]
    fn test_gfx_rect_ok() {
        Tester::default()
            .run("GFX_RECT 1, 2, 3, 4")
            .expect_output([CapturedOut::DrawRect(
                PixelsXY { x: 1, y: 2 },
                PixelsXY { x: 3, y: 4 },
            )])
            .check();
    }

    #[test]
    fn test_gfx_rect_errors() {
        check_errors_two_xy("GFX_RECT");
    }

    #[test]
    fn test_gfx_rectf_ok() {
        Tester::default()
            .run("GFX_RECTF 1, 2, 3, 4")
            .expect_output([CapturedOut::DrawRectFilled(
                PixelsXY { x: 1, y: 2 },
                PixelsXY { x: 3, y: 4 },
            )])
            .check();
    }

    #[test]
    fn test_gfx_rectf_errors() {
        check_errors_two_xy("GFX_RECTF");
    }

    #[test]
    fn test_gfx_sync_ok() {
        Tester::default().run("GFX_SYNC").expect_output([CapturedOut::SyncNow]).check();
        Tester::default().run("GFX_SYNC TRUE").expect_output([CapturedOut::SetSync(true)]).check();
        Tester::default()
            .run("GFX_SYNC FALSE")
            .expect_output([CapturedOut::SetSync(false)])
            .check();
    }

    #[test]
    fn test_gfx_sync_errors() {
        check_stmt_err("GFX_SYNC takes zero or one argument", "GFX_SYNC 2, 3");
        check_stmt_err("Argument to GFX_SYNC must be a boolean", "GFX_SYNC 2");
    }
}
