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
fn parse_coordinate(expr: &Expr, machine: &mut Machine) -> Result<usize, CallError> {
    match expr.eval(machine.get_mut_symbols())? {
        Value::Integer(i) if i >= 0 => Ok(i as usize),
        Value::Integer(i) => {
            Err(CallError::ArgumentError(format!("Coordinate {} out of range", i)))
        }
        _ => Err(CallError::ArgumentError(format!("Coordinate {:?} must be an integer", expr))),
    }
}

/// Parses a pair of expressions that represent an (x,y) coordinate pair.
fn parse_coordinates(
    xexpr: &Expr,
    yexpr: &Expr,
    machine: &mut Machine,
) -> Result<PixelsXY, CallError> {
    Ok(PixelsXY { x: parse_coordinate(xexpr, machine)?, y: parse_coordinate(yexpr, machine)? })
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
                (parse_coordinates(x1, y1, machine)?, parse_coordinates(x2, y2, machine)?)
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

/// Adds all console-related commands for the given `console` to the `machine`.
pub fn add_all(machine: &mut Machine, console: Rc<RefCell<dyn Console>>) {
    machine.add_command(GfxLineCommand::new(console));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;

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
        for cmd in &[
            "GFX_LINE 1, 2, , 4",
            "GFX_LINE 1, 2, 3",
            "GFX_LINE 1, 2, 3, 4, 5",
            "GFX_LINE 1, 2; 3, 4",
        ] {
            check_stmt_err("GFX_LINE takes four integer arguments separated by commas", cmd);
        }

        for cmd in &[
            "GFX_LINE -1, 1, 1, 1",
            "GFX_LINE 1, -1, 1, 1",
            "GFX_LINE 1, 1, -1, 1",
            "GFX_LINE 1, 1, 1, -1",
        ] {
            check_stmt_err("Coordinate -1 out of range", cmd);
        }

        for cmd in &[
            "GFX_LINE \"a\", 1, 1, 1",
            "GFX_LINE 1, \"a\", 1, 1",
            "GFX_LINE 1, 1, \"a\", 1",
            "GFX_LINE 1, 1, 1, \"a\"",
        ] {
            check_stmt_err("Coordinate Text(\"a\") must be an integer", cmd);
        }
    }
}
