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
use endbasic_core::ast::{
    ArgSep, ArgSpan, BuiltinCallSpan, Expr, FunctionCallSpan, Value, VarType,
};
use endbasic_core::exec::Machine;
use endbasic_core::syms::{
    CallError, CallableMetadata, CallableMetadataBuilder, Command, CommandResult, Function,
    FunctionResult, Symbols,
};
use std::cell::RefCell;
use std::convert::TryFrom;
use std::rc::Rc;

/// Category description for all symbols provided by this module.
const CATEGORY: &str = "Graphics
The EndBASIC console overlays text and graphics in the same canvas.  The consequence of this \
design choice is that the console has two coordinate systems: the character-based system, used by
the commands described in HELP \"CONSOLE\", and the pixel-based system, used by the commands \
described in this section.";

/// Parses an expression that represents a single coordinate.
async fn parse_coordinate(expr: &Expr, machine: &mut Machine) -> Result<i16, CallError> {
    let value = expr.eval(machine.get_mut_symbols()).await?;
    let i =
        value.as_i32().map_err(|e| CallError::ArgumentError(expr.start_pos(), format!("{}", e)))?;
    match i16::try_from(i) {
        Ok(i) => Ok(i),
        Err(_) => Err(CallError::ArgumentError(
            expr.start_pos(),
            format!("Coordinate {} out of range", i),
        )),
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

/// Parses an expression that represents a radius.
async fn parse_radius(expr: &Expr, machine: &mut Machine) -> Result<u16, CallError> {
    let value = expr.eval(machine.get_mut_symbols()).await?;
    let i =
        value.as_i32().map_err(|e| CallError::ArgumentError(expr.start_pos(), format!("{}", e)))?;
    match u16::try_from(i) {
        Ok(i) => Ok(i),
        Err(_) if i < 0 => Err(CallError::ArgumentError(
            expr.start_pos(),
            format!("Radius {} must be positive", i),
        )),
        Err(_) => {
            Err(CallError::ArgumentError(expr.start_pos(), format!("Radius {} out of range", i)))
        }
    }
}

/// The `GFX_CIRCLE` command.
pub struct GfxCircleCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxCircleCommand {
    /// Creates a new `GFX_CIRCLE` command that draws an empty circle on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_CIRCLE", VarType::Void)
                .with_syntax("x%, y%, r%")
                .with_category(CATEGORY)
                .with_description(
                    "Draws a circle of radius r centered at (x,y).
The outline of the circle is drawn using the foreground color as selected by COLOR and the \
area of the circle is left untouched.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Command for GfxCircleCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        let (xy, r) = match span.args.as_slice() {
            [ArgSpan { expr: Some(x), sep: ArgSep::Long, .. }, ArgSpan { expr: Some(y), sep: ArgSep::Long, .. }, ArgSpan { expr: Some(r), sep: ArgSep::End, .. }] => {
                (parse_coordinates(x, y, machine).await?, parse_radius(r, machine).await?)
            }
            _ => return Err(CallError::SyntaxError),
        };

        self.console.borrow_mut().draw_circle(xy, r)?;
        Ok(())
    }
}

/// The `GFX_CIRCLEF` command.
pub struct GfxCirclefCommand {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxCirclefCommand {
    /// Creates a new `GFX_CIRCLEF` command that draws a filled circle on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_CIRCLEF", VarType::Void)
                .with_syntax("x%, y%, r%")
                .with_category(CATEGORY)
                .with_description(
                    "Draws a filled circle of radius r centered at (x,y).
The outline and area of the circle are drawn using the foreground color as selected by COLOR.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Command for GfxCirclefCommand {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        let (xy, r) = match span.args.as_slice() {
            [ArgSpan { expr: Some(x), sep: ArgSep::Long, .. }, ArgSpan { expr: Some(y), sep: ArgSep::Long, .. }, ArgSpan { expr: Some(r), sep: ArgSep::End, .. }] => {
                (parse_coordinates(x, y, machine).await?, parse_radius(r, machine).await?)
            }
            _ => return Err(CallError::SyntaxError),
        };

        self.console.borrow_mut().draw_circle_filled(xy, r)?;
        Ok(())
    }
}

/// The `GFX_HEIGHT` function.
pub struct GfxHeightFunction {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxHeightFunction {
    /// Creates a new instance of the function.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_HEIGHT", VarType::Integer)
                .with_syntax("")
                .with_category(CATEGORY)
                .with_description(
                    "Returns the height in pixels of the graphical console.
See GFX_WIDTH to query the other dimension.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Function for GfxHeightFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, _symbols: &mut Symbols) -> FunctionResult {
        if !span.args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        let size = self.console.borrow().size_pixels()?;
        Ok(Value::Integer(i32::from(size.height)))
    }
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

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        let (x1y1, x2y2) = match span.args.as_slice() {
            [ArgSpan { expr: Some(x1), sep: ArgSep::Long, .. }, ArgSpan { expr: Some(y1), sep: ArgSep::Long, .. }, ArgSpan { expr: Some(x2), sep: ArgSep::Long, .. }, ArgSpan { expr: Some(y2), sep: ArgSep::End, .. }] => {
                (
                    parse_coordinates(x1, y1, machine).await?,
                    parse_coordinates(x2, y2, machine).await?,
                )
            }
            _ => return Err(CallError::SyntaxError),
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

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        let xy = match span.args.as_slice() {
            [ArgSpan { expr: Some(x), sep: ArgSep::Long, .. }, ArgSpan { expr: Some(y), sep: ArgSep::End, .. }] => {
                parse_coordinates(x, y, machine).await?
            }
            _ => return Err(CallError::SyntaxError),
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

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        let (x1y1, x2y2) = match span.args.as_slice() {
            [ArgSpan { expr: Some(x1), sep: ArgSep::Long, .. }, ArgSpan { expr: Some(y1), sep: ArgSep::Long, .. }, ArgSpan { expr: Some(x2), sep: ArgSep::Long, .. }, ArgSpan { expr: Some(y2), sep: ArgSep::End, .. }] => {
                (
                    parse_coordinates(x1, y1, machine).await?,
                    parse_coordinates(x2, y2, machine).await?,
                )
            }
            _ => return Err(CallError::SyntaxError),
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

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        let (x1y1, x2y2) = match span.args.as_slice() {
            [ArgSpan { expr: Some(x1), sep: ArgSep::Long, .. }, ArgSpan { expr: Some(y1), sep: ArgSep::Long, .. }, ArgSpan { expr: Some(x2), sep: ArgSep::Long, .. }, ArgSpan { expr: Some(y2), sep: ArgSep::End, .. }] => {
                (
                    parse_coordinates(x1, y1, machine).await?,
                    parse_coordinates(x2, y2, machine).await?,
                )
            }
            _ => return Err(CallError::SyntaxError),
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
you are done, and then enable video syncing again.  Note that the textual cursor is not visible \
when video syncing is disabled.
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

    async fn exec(&self, span: &BuiltinCallSpan, machine: &mut Machine) -> CommandResult {
        match span.args.as_slice() {
            [] => {
                self.console.borrow_mut().sync_now()?;
                Ok(())
            }
            [ArgSpan { expr: Some(b), sep: ArgSep::End, .. }] => {
                match b.eval(machine.get_mut_symbols()).await? {
                    Value::Boolean(b) => {
                        let mut console = self.console.borrow_mut();
                        if b {
                            console.show_cursor()?;
                        } else {
                            console.hide_cursor()?;
                        }
                        console.set_sync(b)?;
                        Ok(())
                    }
                    _ => Err(CallError::ArgumentError(
                        b.start_pos(),
                        "Argument to GFX_SYNC must be a boolean".to_owned(),
                    )),
                }
            }
            _ => Err(CallError::SyntaxError),
        }
    }
}

/// The `GFX_WIDTH` function.
pub struct GfxWidthFunction {
    metadata: CallableMetadata,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxWidthFunction {
    /// Creates a new instance of the function.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_WIDTH", VarType::Integer)
                .with_syntax("")
                .with_category(CATEGORY)
                .with_description(
                    "Returns the width in pixels of the graphical console.
See GFX_HEIGHT to query the other dimension.",
                )
                .build(),
            console,
        })
    }
}

#[async_trait(?Send)]
impl Function for GfxWidthFunction {
    fn metadata(&self) -> &CallableMetadata {
        &self.metadata
    }

    async fn exec(&self, span: &FunctionCallSpan, _symbols: &mut Symbols) -> FunctionResult {
        if !span.args.is_empty() {
            return Err(CallError::SyntaxError);
        }
        let size = self.console.borrow().size_pixels()?;
        Ok(Value::Integer(i32::from(size.width)))
    }
}

/// Adds all console-related commands for the given `console` to the `machine`.
pub fn add_all(machine: &mut Machine, console: Rc<RefCell<dyn Console>>) {
    machine.add_command(GfxCircleCommand::new(console.clone()));
    machine.add_command(GfxCirclefCommand::new(console.clone()));
    machine.add_function(GfxHeightFunction::new(console.clone()));
    machine.add_command(GfxLineCommand::new(console.clone()));
    machine.add_command(GfxPixelCommand::new(console.clone()));
    machine.add_command(GfxRectCommand::new(console.clone()));
    machine.add_command(GfxRectfCommand::new(console.clone()));
    machine.add_command(GfxSyncCommand::new(console.clone()));
    machine.add_function(GfxWidthFunction::new(console));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::console::SizeInPixels;
    use crate::testutils::*;

    /// Verifies error conditions for a command named `name` that takes to X/Y pairs.
    fn check_errors_two_xy(name: &'static str) {
        for args in &["1, 2, , 4", "1, 2, 3", "1, 2, 3, 4, 5", "2; 3, 4"] {
            check_stmt_err(
                format!("1:1: In call to {}: expected x1%, y1%, x2%, y2%", name),
                &format!("{} {}", name, args),
            );
        }

        for args in &["-40000, 1, 1, 1", "1, -40000, 1, 1", "1, 1, -40000, 1", "1, 1, 1, -40000"] {
            let pos = name.len() + 1 + args.find('-').unwrap() + 1;
            check_stmt_err(
                format!("1:1: In call to {}: 1:{}: Coordinate -40000 out of range", name, pos),
                &format!("{} {}", name, args),
            );
        }

        for args in &["40000, 1, 1, 1", "1, 40000, 1, 1", "1, 1, 40000, 1", "1, 1, 1, 40000"] {
            let pos = name.len() + 1 + args.find('4').unwrap() + 1;
            check_stmt_err(
                format!("1:1: In call to {}: 1:{}: Coordinate 40000 out of range", name, pos),
                &format!("{} {}", name, args),
            );
        }

        for args in &["\"a\", 1, 1, 1", "1, \"a\", 1, 1", "1, 1, \"a\", 1", "1, 1, 1, \"a\""] {
            let stmt = &format!("{} {}", name, args);
            let pos = stmt.find('"').unwrap() + 1;
            check_stmt_err(
                format!("1:1: In call to {}: 1:{}: \"a\" is not a number", name, pos),
                stmt,
            );
        }
    }

    /// Verifies error conditions for a command named `name` that takes an X/Y pair and a radius.
    fn check_errors_xy_radius(name: &'static str) {
        for args in &["1, , 3", "1, 2", "1, 2, 3, 4", "2; 3, 4"] {
            check_stmt_err(
                format!("1:1: In call to {}: expected x%, y%, r%", name),
                &format!("{} {}", name, args),
            );
        }

        for args in &["-40000, 1, 1", "1, -40000, 1"] {
            let pos = name.len() + 1 + args.find('-').unwrap() + 1;
            check_stmt_err(
                format!("1:1: In call to {}: 1:{}: Coordinate -40000 out of range", name, pos),
                &format!("{} {}", name, args),
            );
        }
        check_stmt_err(
            format!(
                "1:1: In call to {}: 1:{}: Radius -40000 must be positive",
                name,
                name.len() + 8
            ),
            &format!("{} 1, 1, -40000", name),
        );

        for args in &["40000, 1, 1", "1, 40000, 1"] {
            let pos = name.len() + 1 + args.find('4').unwrap() + 1;
            check_stmt_err(
                format!("1:1: In call to {}: 1:{}: Coordinate 40000 out of range", name, pos),
                &format!("{} {}", name, args),
            );
        }
        check_stmt_err(
            format!("1:1: In call to {}: 1:{}: Radius 80000 out of range", name, name.len() + 8),
            &format!("{} 1, 1, 80000", name),
        );

        for args in &["\"a\", 1, 1", "1, \"a\", 1", "1, 1, \"a\""] {
            let stmt = &format!("{} {}", name, args);
            let pos = stmt.find('"').unwrap() + 1;
            check_stmt_err(
                format!("1:1: In call to {}: 1:{}: \"a\" is not a number", name, pos),
                stmt,
            );
        }

        check_stmt_err(
            format!("1:1: In call to {}: 1:{}: Radius -1 must be positive", name, name.len() + 8),
            &format!("{} 1, 1, -1", name),
        );
    }

    #[test]
    fn test_gfx_circle_ok() {
        Tester::default()
            .run("GFX_CIRCLE 0, 0, 0")
            .expect_output([CapturedOut::DrawCircle(PixelsXY { x: 0, y: 0 }, 0)])
            .check();

        Tester::default()
            .run("GFX_CIRCLE 1.1, 2.3, 2.5")
            .expect_output([CapturedOut::DrawCircle(PixelsXY { x: 1, y: 2 }, 3)])
            .check();

        Tester::default()
            .run("GFX_CIRCLE -31000, -32000, 31000")
            .expect_output([CapturedOut::DrawCircle(PixelsXY { x: -31000, y: -32000 }, 31000)])
            .check();
    }

    #[test]
    fn test_gfx_circle_errors() {
        check_errors_xy_radius("GFX_CIRCLE");
    }

    #[test]
    fn test_gfx_circlef_ok() {
        Tester::default()
            .run("GFX_CIRCLEF 0, 0, 0")
            .expect_output([CapturedOut::DrawCircleFilled(PixelsXY { x: 0, y: 0 }, 0)])
            .check();

        Tester::default()
            .run("GFX_CIRCLEF 1.1, 2.3, 2.5")
            .expect_output([CapturedOut::DrawCircleFilled(PixelsXY { x: 1, y: 2 }, 3)])
            .check();

        Tester::default()
            .run("GFX_CIRCLEF -31000, -32000, 31000")
            .expect_output([CapturedOut::DrawCircleFilled(
                PixelsXY { x: -31000, y: -32000 },
                31000,
            )])
            .check();
    }

    #[test]
    fn test_gfx_circlef_errors() {
        check_errors_xy_radius("GFX_CIRCLEF");
    }

    #[test]
    fn test_gfx_height() {
        let mut t = Tester::default();
        t.get_console().borrow_mut().set_size_pixels(SizeInPixels { width: 0, height: 768 });
        t.run("result = GFX_HEIGHT").expect_var("result", 768i32).check();

        check_expr_error(
            "1:10: In call to GFX_HEIGHT: Graphical console size not yet set",
            "GFX_HEIGHT",
        );

        check_expr_error(
            "1:10: In call to GFX_HEIGHT: expected no arguments nor parenthesis",
            "GFX_HEIGHT()",
        );
        check_expr_error(
            "1:10: In call to GFX_HEIGHT: expected no arguments nor parenthesis",
            "GFX_HEIGHT(1)",
        );
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

        Tester::default()
            .run("GFX_LINE -31000.3, -32000.2, 31000.4, 31999.8")
            .expect_output([CapturedOut::DrawLine(
                PixelsXY { x: -31000, y: -32000 },
                PixelsXY { x: 31000, y: 32000 },
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

        Tester::default()
            .run("GFX_PIXEL -31000, -32000")
            .expect_output([CapturedOut::DrawPixel(PixelsXY { x: -31000, y: -32000 })])
            .check();

        Tester::default()
            .run("GFX_PIXEL 30999.5, 31999.7")
            .expect_output([CapturedOut::DrawPixel(PixelsXY { x: 31000, y: 32000 })])
            .check();
    }

    #[test]
    fn test_gfx_pixel_errors() {
        for cmd in &["GFX_PIXEL , 2", "GFX_PIXEL 1, 2, 3", "GFX_PIXEL 1", "GFX_PIXEL 1; 2"] {
            check_stmt_err("1:1: In call to GFX_PIXEL: expected x%, y%", cmd);
        }

        for cmd in &["GFX_PIXEL -40000, 1", "GFX_PIXEL 1, -40000"] {
            check_stmt_err(
                format!(
                    "1:1: In call to GFX_PIXEL: 1:{}: Coordinate -40000 out of range",
                    cmd.find('-').unwrap() + 1
                ),
                cmd,
            );
        }

        for cmd in &["GFX_PIXEL \"a\", 1", "GFX_PIXEL 1, \"a\""] {
            let pos = cmd.find('"').unwrap() + 1;
            check_stmt_err(
                format!("1:1: In call to GFX_PIXEL: 1:{}: \"a\" is not a number", pos),
                cmd,
            );
        }
    }

    #[test]
    fn test_gfx_rect_ok() {
        Tester::default()
            .run("GFX_RECT 1.1, 2.3, 2.5, 3.9")
            .expect_output([CapturedOut::DrawRect(
                PixelsXY { x: 1, y: 2 },
                PixelsXY { x: 3, y: 4 },
            )])
            .check();

        Tester::default()
            .run("GFX_RECT -31000, -32000, 31000, 32000")
            .expect_output([CapturedOut::DrawRect(
                PixelsXY { x: -31000, y: -32000 },
                PixelsXY { x: 31000, y: 32000 },
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
            .run("GFX_RECTF 1.1, 2.3, 2.5, 3.9")
            .expect_output([CapturedOut::DrawRectFilled(
                PixelsXY { x: 1, y: 2 },
                PixelsXY { x: 3, y: 4 },
            )])
            .check();

        Tester::default()
            .run("GFX_RECTF -31000, -32000, 31000, 32000")
            .expect_output([CapturedOut::DrawRectFilled(
                PixelsXY { x: -31000, y: -32000 },
                PixelsXY { x: 31000, y: 32000 },
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
        Tester::default()
            .run("GFX_SYNC TRUE")
            .expect_output([CapturedOut::ShowCursor, CapturedOut::SetSync(true)])
            .check();
        Tester::default()
            .run("GFX_SYNC FALSE")
            .expect_output([CapturedOut::HideCursor, CapturedOut::SetSync(false)])
            .check();
    }

    #[test]
    fn test_gfx_sync_errors() {
        check_stmt_err("1:1: In call to GFX_SYNC: expected [enabled?]", "GFX_SYNC 2, 3");
        check_stmt_err(
            "1:1: In call to GFX_SYNC: 1:10: Argument to GFX_SYNC must be a boolean",
            "GFX_SYNC 2",
        );
    }

    #[test]
    fn test_gfx_width() {
        let mut t = Tester::default();
        t.get_console().borrow_mut().set_size_pixels(SizeInPixels { width: 12345, height: 0 });
        t.run("result = GFX_WIDTH").expect_var("result", 12345i32).check();

        check_expr_error(
            "1:10: In call to GFX_WIDTH: Graphical console size not yet set",
            "GFX_WIDTH",
        );

        check_expr_error(
            "1:10: In call to GFX_WIDTH: expected no arguments nor parenthesis",
            "GFX_WIDTH()",
        );
        check_expr_error(
            "1:10: In call to GFX_WIDTH: expected no arguments nor parenthesis",
            "GFX_WIDTH(1)",
        );
    }
}
