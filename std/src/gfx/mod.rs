// EndBASIC
// Copyright 2021 Julio Merino
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

//! Commands for graphical console interaction.

use crate::console::{Console, PixelsXY};
use endbasic_core::{
    ArgSep, ArgSepSyntax, CallError, CallResult, Callable, CallableMetadata,
    CallableMetadataBuilder, ExprType, LineCol, RepeatedSyntax, RepeatedTypeSyntax,
    RequiredRefSyntax, RequiredValueSyntax, Scope, SingularArgSyntax,
};
use std::borrow::Cow;
use std::cell::RefCell;
use std::convert::TryFrom;
use std::rc::Rc;

use crate::MachineBuilder;

pub mod lcd;

/// Category description for all symbols provided by this module.
const CATEGORY: &str = "Graphics
The EndBASIC console overlays text and graphics in the same canvas.  The consequence of this \
design choice is that the console has two coordinate systems: the character-based system, used by
the commands described in HELP \"CONSOLE\", and the pixel-based system, used by the commands \
described in this section.";

/// Parses an expression that represents a single coordinate.
fn parse_coordinate(scope: &Scope<'_>, narg: u8) -> CallResult<i16> {
    parse_coordinate_value(scope.get_pos(narg), scope.get_integer(narg))
}

/// Parses an integer that represents a single coordinate.
fn parse_coordinate_value(pos: LineCol, i: i32) -> CallResult<i16> {
    match i16::try_from(i) {
        Ok(i) => Ok(i),
        Err(_) => Err(CallError::Syntax(pos, format!("Coordinate {} out of range", i))),
    }
}

/// Parses a pair of expressions that represent an (x,y) coordinate pair.
fn parse_coordinates(scope: &Scope<'_>, xarg: u8, yarg: u8) -> CallResult<PixelsXY> {
    Ok(PixelsXY { x: parse_coordinate(scope, xarg)?, y: parse_coordinate(scope, yarg)? })
}

/// Parses three pairs of expressions that represent triangle vertex coordinates.
fn parse_triangle_coordinates(
    scope: &Scope<'_>,
    x1arg: u8,
    y1arg: u8,
    x2arg: u8,
    y2arg: u8,
    x3arg: u8,
    y3arg: u8,
) -> CallResult<(PixelsXY, PixelsXY, PixelsXY)> {
    Ok((
        parse_coordinates(scope, x1arg, y1arg)?,
        parse_coordinates(scope, x2arg, y2arg)?,
        parse_coordinates(scope, x3arg, y3arg)?,
    ))
}

/// Parses a variable-length sequence of X/Y coordinate pairs.
fn parse_polygon_coordinates(scope: &Scope<'_>) -> CallResult<Vec<PixelsXY>> {
    match scope.nargs() {
        0 => return Ok(vec![]),
        1 => return parse_polygon_coordinates_from_array(scope),
        _ => (),
    }

    if !scope.nargs().is_multiple_of(2) {
        let narg = u8::try_from(scope.nargs() - 1).expect("Argument index must fit in u8");
        return Err(CallError::Syntax(
            scope.get_pos(narg),
            "Expected an even number of coordinates".to_owned(),
        ));
    }

    let mut points = Vec::with_capacity(scope.nargs() / 2);
    for i in (0..scope.nargs()).step_by(2) {
        let xarg = u8::try_from(i).expect("Argument index must fit in u8");
        let yarg = u8::try_from(i + 1).expect("Argument index must fit in u8");
        points.push(parse_coordinates(scope, xarg, yarg)?);
    }
    Ok(points)
}

/// Parses an array reference that contains a variable-length sequence of X/Y coordinate pairs.
fn parse_polygon_coordinates_from_array(scope: &Scope<'_>) -> CallResult<Vec<PixelsXY>> {
    debug_assert_eq!(1, scope.nargs());

    let array = scope.get_ref(0);
    let pos = scope.get_pos(0);
    if array.vtype != ExprType::Integer {
        return Err(CallError::Syntax(pos, "Expected an INTEGER array".to_owned()));
    }

    let dimensions = array.array_dimensions();
    match dimensions {
        [ncoords] => {
            if !ncoords.is_multiple_of(2) {
                return Err(CallError::Syntax(
                    pos,
                    "Expected an even number of coordinates".to_owned(),
                ));
            }

            let mut points = Vec::with_capacity(*ncoords / 2);
            for i in (0..*ncoords).step_by(2) {
                let x = array
                    .deref_array_integer(&[i as i32])
                    .map_err(|e| CallError::Syntax(pos, e))?;
                let y = array
                    .deref_array_integer(&[(i + 1) as i32])
                    .map_err(|e| CallError::Syntax(pos, e))?;
                points.push(PixelsXY {
                    x: parse_coordinate_value(pos, x)?,
                    y: parse_coordinate_value(pos, y)?,
                });
            }
            Ok(points)
        }

        [npoints, 2] => {
            let mut points = Vec::with_capacity(*npoints);
            for i in 0..*npoints {
                let x = array
                    .deref_array_integer(&[i as i32, 0])
                    .map_err(|e| CallError::Syntax(pos, e))?;
                let y = array
                    .deref_array_integer(&[i as i32, 1])
                    .map_err(|e| CallError::Syntax(pos, e))?;
                points.push(PixelsXY {
                    x: parse_coordinate_value(pos, x)?,
                    y: parse_coordinate_value(pos, y)?,
                });
            }
            Ok(points)
        }

        _ => Err(CallError::Syntax(
            pos,
            "Expected a flat array of coordinates or an Nx2 array of points".to_owned(),
        )),
    }
}

/// Parses an expression that represents a radius.
fn parse_radius(scope: &Scope<'_>, narg: u8) -> CallResult<u16> {
    let i = scope.get_integer(narg);
    match u16::try_from(i) {
        Ok(i) => Ok(i),
        Err(_) if i < 0 => {
            Err(CallError::Syntax(scope.get_pos(narg), format!("Radius {} must be positive", i)))
        }
        Err(_) => Err(CallError::Syntax(scope.get_pos(narg), format!("Radius {} out of range", i))),
    }
}

/// The `GFX_CIRCLE` command.
pub struct GfxCircleCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxCircleCommand {
    /// Creates a new `GFX_CIRCLE` command that draws an empty circle on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_CIRCLE")
                .with_syntax(&[(
                    &[
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("x"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("y"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("r"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::End,
                        ),
                    ],
                    None,
                )])
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

impl Callable for GfxCircleCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(3, scope.nargs());
        let xy = parse_coordinates(&scope, 0, 1)?;
        let r = parse_radius(&scope, 2)?;

        self.console.borrow_mut().draw_circle(xy, r)?;
        Ok(())
    }
}

/// The `GFX_CIRCLEF` command.
pub struct GfxCirclefCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxCirclefCommand {
    /// Creates a new `GFX_CIRCLEF` command that draws a filled circle on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_CIRCLEF")
                .with_syntax(&[(
                    &[
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("x"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("y"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("r"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::End,
                        ),
                    ],
                    None,
                )])
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

impl Callable for GfxCirclefCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(3, scope.nargs());
        let xy = parse_coordinates(&scope, 0, 1)?;
        let r = parse_radius(&scope, 2)?;

        self.console.borrow_mut().draw_circle_filled(xy, r)?;
        Ok(())
    }
}

/// The `GFX_HEIGHT` function.
pub struct GfxHeightFunction {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxHeightFunction {
    /// Creates a new instance of the function.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_HEIGHT")
                .with_return_type(ExprType::Integer)
                .with_syntax(&[(&[], None)])
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

impl Callable for GfxHeightFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(0, scope.nargs());
        let size = self.console.borrow().size_pixels()?;
        scope.return_integer(i32::from(size.height))
    }
}

/// The `GFX_LINE` command.
pub struct GfxLineCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxLineCommand {
    /// Creates a new `GFX_LINE` command that draws a line on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_LINE")
                .with_syntax(&[(
                    &[
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("x1"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("y1"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("x2"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("y2"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::End,
                        ),
                    ],
                    None,
                )])
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

impl Callable for GfxLineCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(4, scope.nargs());
        let x1y1 = parse_coordinates(&scope, 0, 1)?;
        let x2y2 = parse_coordinates(&scope, 2, 3)?;

        self.console.borrow_mut().draw_line(x1y1, x2y2)?;
        Ok(())
    }
}

/// The `GFX_PEEK` function.
pub struct GfxPeekFunction {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxPeekFunction {
    /// Creates a new instance of the function.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_PEEK")
                .with_return_type(ExprType::Integer)
                .with_syntax(&[(
                    &[
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("x"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("y"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::End,
                        ),
                    ],
                    None,
                )])
                .with_category(CATEGORY)
                .with_description(
                    "Returns the color number of the pixel at (x,y).
Returns -1 if the pixel lies outside of the graphical console or if its color cannot be mapped \
back to a COLOR value.",
                )
                .build(),
            console,
        })
    }
}

impl Callable for GfxPeekFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(2, scope.nargs());
        let xy = parse_coordinates(&scope, 0, 1)?;
        let color = self.console.borrow().peek_pixel(xy)?.map(i32::from).unwrap_or(-1);
        scope.return_integer(color)
    }
}

/// The `GFX_PIXEL` command.
pub struct GfxPixelCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxPixelCommand {
    /// Creates a new `GFX_PIXEL` command that draws a single pixel on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_PIXEL")
                .with_syntax(&[(
                    &[
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("x"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("y"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::End,
                        ),
                    ],
                    None,
                )])
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

impl Callable for GfxPixelCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(2, scope.nargs());
        let xy = parse_coordinates(&scope, 0, 1)?;

        self.console.borrow_mut().draw_pixel(xy)?;
        Ok(())
    }
}

/// The `GFX_POLY` command.
pub struct GfxPolyCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxPolyCommand {
    /// Creates a new `GFX_POLY` command that draws an outlined polygon on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_POLY")
                .with_syntax(&[
                    (&[], None),
                    (
                        &[SingularArgSyntax::RequiredRef(
                            RequiredRefSyntax {
                                name: Cow::Borrowed("points"),
                                require_array: true,
                                define_undefined: false,
                            },
                            ArgSepSyntax::End,
                        )],
                        None,
                    ),
                    (
                        &[
                            SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax {
                                    name: Cow::Borrowed("x1"),
                                    vtype: ExprType::Integer,
                                },
                                ArgSepSyntax::Exactly(ArgSep::Long),
                            ),
                            SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax {
                                    name: Cow::Borrowed("y1"),
                                    vtype: ExprType::Integer,
                                },
                                ArgSepSyntax::Exactly(ArgSep::Long),
                            ),
                        ],
                        Some(&RepeatedSyntax {
                            name: Cow::Borrowed("coord"),
                            type_syn: RepeatedTypeSyntax::TypedValue(ExprType::Integer),
                            sep: ArgSepSyntax::Exactly(ArgSep::Long),
                            require_one: false,
                            allow_missing: false,
                        }),
                    ),
                ])
                .with_category(CATEGORY)
                .with_description(
                    "Draws a polygon with vertices at (x1,y1), (x2,y2), ..., and (xN,yN).
The points can be specified either as individual coordinates or via an INTEGER array containing a \
flat list of coordinates or an Nx2 matrix of points.
The outline of the polygon is drawn using the foreground color as selected by COLOR and the area \
of the polygon is left untouched.",
                )
                .build(),
            console,
        })
    }
}

impl Callable for GfxPolyCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let points = parse_polygon_coordinates(&scope)?;

        self.console.borrow_mut().draw_poly(&points)?;
        Ok(())
    }
}

/// The `GFX_POLYF` command.
pub struct GfxPolyfCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxPolyfCommand {
    /// Creates a new `GFX_POLYF` command that draws a filled polygon on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_POLYF")
                .with_syntax(&[
                    (&[], None),
                    (
                        &[SingularArgSyntax::RequiredRef(
                            RequiredRefSyntax {
                                name: Cow::Borrowed("points"),
                                require_array: true,
                                define_undefined: false,
                            },
                            ArgSepSyntax::End,
                        )],
                        None,
                    ),
                    (
                        &[
                            SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax {
                                    name: Cow::Borrowed("x1"),
                                    vtype: ExprType::Integer,
                                },
                                ArgSepSyntax::Exactly(ArgSep::Long),
                            ),
                            SingularArgSyntax::RequiredValue(
                                RequiredValueSyntax {
                                    name: Cow::Borrowed("y1"),
                                    vtype: ExprType::Integer,
                                },
                                ArgSepSyntax::Exactly(ArgSep::Long),
                            ),
                        ],
                        Some(&RepeatedSyntax {
                            name: Cow::Borrowed("coord"),
                            type_syn: RepeatedTypeSyntax::TypedValue(ExprType::Integer),
                            sep: ArgSepSyntax::Exactly(ArgSep::Long),
                            require_one: false,
                            allow_missing: false,
                        }),
                    ),
                ])
                .with_category(CATEGORY)
                .with_description(
                    "Draws a filled polygon with vertices at (x1,y1), (x2,y2), ..., and (xN,yN).
The points can be specified either as individual coordinates or via an INTEGER array containing a \
flat list of coordinates or an Nx2 matrix of points.
The outline and area of the polygon are drawn using the foreground color as selected by COLOR.",
                )
                .build(),
            console,
        })
    }
}

impl Callable for GfxPolyfCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let points = parse_polygon_coordinates(&scope)?;

        self.console.borrow_mut().draw_poly_filled(&points)?;
        Ok(())
    }
}

/// The `GFX_RECT` command.
pub struct GfxRectCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxRectCommand {
    /// Creates a new `GFX_RECT` command that draws an empty rectangle on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_RECT")
                .with_syntax(&[(
                    &[
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("x1"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("y1"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("x2"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("y2"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::End,
                        ),
                    ],
                    None,
                )])
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

impl Callable for GfxRectCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(4, scope.nargs());
        let x1y1 = parse_coordinates(&scope, 0, 1)?;
        let x2y2 = parse_coordinates(&scope, 2, 3)?;

        self.console.borrow_mut().draw_rect(x1y1, x2y2)?;
        Ok(())
    }
}

/// The `GFX_RECTF` command.
pub struct GfxRectfCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxRectfCommand {
    /// Creates a new `GFX_RECTF` command that draws a filled rectangle on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_RECTF")
                .with_syntax(&[(
                    &[
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("x1"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("y1"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("x2"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("y2"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::End,
                        ),
                    ],
                    None,
                )])
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

impl Callable for GfxRectfCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(4, scope.nargs());
        let x1y1 = parse_coordinates(&scope, 0, 1)?;
        let x2y2 = parse_coordinates(&scope, 2, 3)?;

        self.console.borrow_mut().draw_rect_filled(x1y1, x2y2)?;
        Ok(())
    }
}

/// The `GFX_SYNC` command.
pub struct GfxSyncCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
}

/// The `GFX_TRI` command.
pub struct GfxTriCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxTriCommand {
    /// Creates a new `GFX_TRI` command that draws an empty triangle on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_TRI")
                .with_syntax(&[(
                    &[
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("x1"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("y1"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("x2"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("y2"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("x3"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("y3"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::End,
                        ),
                    ],
                    None,
                )])
                .with_category(CATEGORY)
                .with_description(
                    "Draws a triangle with vertices at (x1,y1), (x2,y2), and (x3,y3).
The outline of the triangle is drawn using the foreground color as selected by COLOR and the \
area of the triangle is left untouched.",
                )
                .build(),
            console,
        })
    }
}

impl Callable for GfxTriCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(6, scope.nargs());
        let (x1y1, x2y2, x3y3) = parse_triangle_coordinates(&scope, 0, 1, 2, 3, 4, 5)?;

        self.console.borrow_mut().draw_tri(x1y1, x2y2, x3y3)?;
        Ok(())
    }
}

/// The `GFX_TRIF` command.
pub struct GfxTrifCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxTrifCommand {
    /// Creates a new `GFX_TRIF` command that draws a filled triangle on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_TRIF")
                .with_syntax(&[(
                    &[
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("x1"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("y1"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("x2"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("y2"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("x3"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::Exactly(ArgSep::Long),
                        ),
                        SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("y3"),
                                vtype: ExprType::Integer,
                            },
                            ArgSepSyntax::End,
                        ),
                    ],
                    None,
                )])
                .with_category(CATEGORY)
                .with_description(
                    "Draws a filled triangle with vertices at (x1,y1), (x2,y2), and (x3,y3).
The outline and area of the triangle are drawn using the foreground color as selected by COLOR.",
                )
                .build(),
            console,
        })
    }
}

impl Callable for GfxTrifCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(6, scope.nargs());
        let (x1y1, x2y2, x3y3) = parse_triangle_coordinates(&scope, 0, 1, 2, 3, 4, 5)?;

        self.console.borrow_mut().draw_tri_filled(x1y1, x2y2, x3y3)?;
        Ok(())
    }
}

impl GfxSyncCommand {
    /// Creates a new `GFX_SYNC` command that controls video syncing on `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_SYNC")
                .with_syntax(&[
                    (&[], None),
                    (
                        &[SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("enabled"),
                                vtype: ExprType::Boolean,
                            },
                            ArgSepSyntax::End,
                        )],
                        None,
                    ),
                ])
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

impl Callable for GfxSyncCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        if scope.nargs() == 0 {
            self.console.borrow_mut().sync_now()?;
            Ok(())
        } else {
            debug_assert_eq!(1, scope.nargs());
            let enabled = scope.get_boolean(0);

            let mut console = self.console.borrow_mut();
            if enabled {
                console.show_cursor()?;
            } else {
                console.hide_cursor()?;
            }
            console.set_sync(enabled)?;
            Ok(())
        }
    }
}

/// The `GFX_WIDTH` function.
pub struct GfxWidthFunction {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
}

impl GfxWidthFunction {
    /// Creates a new instance of the function.
    pub fn new(console: Rc<RefCell<dyn Console>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("GFX_WIDTH")
                .with_return_type(ExprType::Integer)
                .with_syntax(&[(&[], None)])
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

impl Callable for GfxWidthFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(0, scope.nargs());
        let size = self.console.borrow().size_pixels()?;
        scope.return_integer(i32::from(size.width))
    }
}

/// Adds all console-related commands for the given `console` to the `machine`.
pub fn add_all(machine: &mut MachineBuilder, console: Rc<RefCell<dyn Console>>) {
    machine.add_callable(GfxCircleCommand::new(console.clone()));
    machine.add_callable(GfxCirclefCommand::new(console.clone()));
    machine.add_callable(GfxHeightFunction::new(console.clone()));
    machine.add_callable(GfxLineCommand::new(console.clone()));
    machine.add_callable(GfxPeekFunction::new(console.clone()));
    machine.add_callable(GfxPixelCommand::new(console.clone()));
    machine.add_callable(GfxPolyCommand::new(console.clone()));
    machine.add_callable(GfxPolyfCommand::new(console.clone()));
    machine.add_callable(GfxRectCommand::new(console.clone()));
    machine.add_callable(GfxRectfCommand::new(console.clone()));
    machine.add_callable(GfxSyncCommand::new(console.clone()));
    machine.add_callable(GfxTriCommand::new(console.clone()));
    machine.add_callable(GfxTrifCommand::new(console.clone()));
    machine.add_callable(GfxWidthFunction::new(console));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::console::SizeInPixels;
    use crate::testutils::*;

    /// Verifies error conditions for a command named `name` that takes two X/Y pairs.
    fn check_errors_two_xy(name: &'static str) {
        for args in &["1, 2, , 4", "1, 2, 3", "1, 2, 3, 4, 5", "2; 3, 4"] {
            check_stmt_compilation_err(
                format!("1:1: {} expected x1%, y1%, x2%, y2%", name),
                &format!("{} {}", name, args),
            );
        }

        for args in &["-40000, 1, 1, 1", "1, -40000, 1, 1", "1, 1, -40000, 1", "1, 1, 1, -40000"] {
            let pos = name.len() + 1 + args.find('-').unwrap() + 1;
            check_stmt_err(
                format!("1:{}: Coordinate -40000 out of range", pos),
                &format!("{} {}", name, args),
            );
        }

        for args in &["40000, 1, 1, 1", "1, 40000, 1, 1", "1, 1, 40000, 1", "1, 1, 1, 40000"] {
            let pos = name.len() + 1 + args.find('4').unwrap() + 1;
            check_stmt_err(
                format!("1:{}: Coordinate 40000 out of range", pos),
                &format!("{} {}", name, args),
            );
        }

        for args in &["\"a\", 1, 1, 1", "1, \"a\", 1, 1", "1, 1, \"a\", 1", "1, 1, 1, \"a\""] {
            let stmt = &format!("{} {}", name, args);
            let pos = stmt.find('"').unwrap() + 1;
            check_stmt_compilation_err(format!("1:{}: STRING is not a number", pos), stmt);
        }
    }

    /// Verifies error conditions for a command named `name` that takes three X/Y pairs.
    fn check_errors_three_xy(name: &'static str) {
        for args in &["1, 2, 3, 4, 5", "1, 2, 3, 4, 5, 6, 7", "1, 2, 3, 4, , 6"] {
            check_stmt_compilation_err(
                format!("1:1: {} expected x1%, y1%, x2%, y2%, x3%, y3%", name),
                &format!("{} {}", name, args),
            );
        }

        check_stmt_compilation_err(
            format!("1:{}: {} expected x1%, y1%, x2%, y2%, x3%, y3%", name.len() + 3, name),
            &format!("{} 2; 3, 4, 5, 6, 7", name),
        );

        for args in &[
            "-40000, 1, 1, 1, 1, 1",
            "1, -40000, 1, 1, 1, 1",
            "1, 1, -40000, 1, 1, 1",
            "1, 1, 1, -40000, 1, 1",
            "1, 1, 1, 1, -40000, 1",
            "1, 1, 1, 1, 1, -40000",
        ] {
            let pos = name.len() + 1 + args.find('-').unwrap() + 1;
            check_stmt_err(
                format!("1:{}: Coordinate -40000 out of range", pos),
                &format!("{} {}", name, args),
            );
        }

        for args in &[
            "40000, 1, 1, 1, 1, 1",
            "1, 40000, 1, 1, 1, 1",
            "1, 1, 40000, 1, 1, 1",
            "1, 1, 1, 40000, 1, 1",
            "1, 1, 1, 1, 40000, 1",
            "1, 1, 1, 1, 1, 40000",
        ] {
            let pos = name.len() + 1 + args.find('4').unwrap() + 1;
            check_stmt_err(
                format!("1:{}: Coordinate 40000 out of range", pos),
                &format!("{} {}", name, args),
            );
        }

        for args in &[
            "\"a\", 1, 1, 1, 1, 1",
            "1, \"a\", 1, 1, 1, 1",
            "1, 1, \"a\", 1, 1, 1",
            "1, 1, 1, \"a\", 1, 1",
            "1, 1, 1, 1, \"a\", 1",
            "1, 1, 1, 1, 1, \"a\"",
        ] {
            let stmt = &format!("{} {}", name, args);
            let pos = stmt.find('"').unwrap() + 1;
            check_stmt_compilation_err(format!("1:{}: STRING is not a number", pos), stmt);
        }
    }

    /// Verifies error conditions for a command named `name` that takes zero or more X/Y pairs.
    fn check_errors_poly(name: &'static str) {
        let syntax = format!(
            "1:{}: {} expected <> | <points> | <x1%, y1%[, coord1%, .., coordN%]>",
            name.len() + 2,
            name,
        );
        check_stmt_compilation_err(syntax, &format!("{} 1", name));
        check_stmt_err(
            format!("1:{}: Expected an even number of coordinates", name.len() + 14),
            &format!("{} 1, 2, 3, 4, 5", name),
        );

        check_stmt_compilation_err(
            format!(
                "1:{}: {} expected <> | <points> | <x1%, y1%[, coord1%, .., coordN%]>",
                name.len() + 3,
                name,
            ),
            &format!("{} 2; 3, 4", name),
        );
        check_stmt_compilation_err(
            format!(
                "1:{}: {} expected <> | <points> | <x1%, y1%[, coord1%, .., coordN%]>",
                name.len() + 8,
                name,
            ),
            &format!("{} 1, 2, , 4", name),
        );

        for args in &["-40000, 1", "1, -40000", "1, 1, -40000, 2", "1, 1, 2, -40000"] {
            let pos = name.len() + 1 + args.find('-').unwrap() + 1;
            check_stmt_err(
                format!("1:{}: Coordinate -40000 out of range", pos),
                &format!("{} {}", name, args),
            );
        }

        for args in &["40000, 1", "1, 40000", "1, 1, 40000, 2", "1, 1, 2, 40000"] {
            let pos = name.len() + 1 + args.find('4').unwrap() + 1;
            check_stmt_err(
                format!("1:{}: Coordinate 40000 out of range", pos),
                &format!("{} {}", name, args),
            );
        }

        for args in &["\"a\", 1", "1, \"a\"", "1, 1, \"a\", 2", "1, 1, 2, \"a\""] {
            let stmt = &format!("{} {}", name, args);
            let pos = stmt.find('"').unwrap() + 1;
            check_stmt_compilation_err(format!("1:{}: STRING is not a number", pos), stmt);
        }

        check_stmt_err(
            format!("1:{}: Expected an even number of coordinates", name.len() + 28),
            &format!("DIM points(5) AS INTEGER: {} points", name),
        );
        check_stmt_err(
            format!(
                "1:{}: Expected a flat array of coordinates or an Nx2 array of points",
                name.len() + 31
            ),
            &format!("DIM points(3, 3) AS INTEGER: {} points", name),
        );
        check_stmt_err(
            format!("1:{}: Expected an INTEGER array", name.len() + 28),
            &format!("DIM points(6) AS BOOLEAN: {} points", name),
        );
        check_stmt_err(
            format!("1:{}: Coordinate 40000 out of range", name.len() + 47),
            &format!("DIM points(2) AS INTEGER: points(0) = 40000: {} points", name),
        );
    }

    /// Verifies error conditions for a command named `name` that takes an X/Y pair and a radius.
    fn check_errors_xy_radius(name: &'static str) {
        for args in &["1, , 3", "1, 2", "1, 2, 3, 4"] {
            check_stmt_compilation_err(
                format!("1:1: {} expected x%, y%, r%", name),
                &format!("{} {}", name, args),
            );
        }
        check_stmt_compilation_err(
            format!("1:{}: {} expected x%, y%, r%", name.len() + 3, name),
            &format!("{} 2; 3, 4", name),
        );

        for args in &["-40000, 1, 1", "1, -40000, 1"] {
            let pos = name.len() + 1 + args.find('-').unwrap() + 1;
            check_stmt_err(
                format!("1:{}: Coordinate -40000 out of range", pos),
                &format!("{} {}", name, args),
            );
        }
        check_stmt_err(
            format!("1:{}: Radius -40000 must be positive", name.len() + 8),
            &format!("{} 1, 1, -40000", name),
        );

        for args in &["40000, 1, 1", "1, 40000, 1"] {
            let pos = name.len() + 1 + args.find('4').unwrap() + 1;
            check_stmt_err(
                format!("1:{}: Coordinate 40000 out of range", pos),
                &format!("{} {}", name, args),
            );
        }
        check_stmt_err(
            format!("1:{}: Radius 80000 out of range", name.len() + 8),
            &format!("{} 1, 1, 80000", name),
        );

        for args in &["\"a\", 1, 1", "1, \"a\", 1", "1, 1, \"a\""] {
            let stmt = &format!("{} {}", name, args);
            let pos = stmt.find('"').unwrap() + 1;
            check_stmt_compilation_err(format!("1:{}: STRING is not a number", pos), stmt);
        }

        check_stmt_err(
            format!("1:{}: Radius -1 must be positive", name.len() + 8),
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
        t.get_console().borrow_mut().set_size_pixels(SizeInPixels::new(1, 768));
        t.run("result = GFX_HEIGHT").expect_var("result", 768i32).check();

        check_expr_error("1:10: Graphical console size not yet set", "GFX_HEIGHT");

        check_expr_compilation_error("1:10: GFX_HEIGHT expected no arguments", "GFX_HEIGHT()");
        check_expr_compilation_error("1:10: GFX_HEIGHT expected no arguments", "GFX_HEIGHT(1)");
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
        for cmd in &["GFX_PIXEL , 2", "GFX_PIXEL 1, 2, 3", "GFX_PIXEL 1"] {
            check_stmt_compilation_err("1:1: GFX_PIXEL expected x%, y%", cmd);
        }
        check_stmt_compilation_err("1:12: GFX_PIXEL expected x%, y%", "GFX_PIXEL 1; 2");

        for cmd in &["GFX_PIXEL -40000, 1", "GFX_PIXEL 1, -40000"] {
            check_stmt_err(
                format!("1:{}: Coordinate -40000 out of range", cmd.find('-').unwrap() + 1),
                cmd,
            );
        }

        for cmd in &["GFX_PIXEL \"a\", 1", "GFX_PIXEL 1, \"a\""] {
            let pos = cmd.find('"').unwrap() + 1;
            check_stmt_compilation_err(format!("1:{}: STRING is not a number", pos), cmd);
        }
    }

    #[test]
    fn test_gfx_peek_ok() {
        let mut t = Tester::default();
        t.get_console().borrow_mut().set_peek_pixel(PixelsXY::new(1, 2), Some(7));
        t.run("result = GFX_PEEK(1, 2)").expect_var("result", 7i32).check();

        let mut t = Tester::default();
        t.get_console().borrow_mut().set_peek_pixel(PixelsXY::new(1, 2), None);
        t.run("result = GFX_PEEK(1, 2)").expect_var("result", -1i32).check();

        Tester::default()
            .run("result = GFX_PEEK(-31000.2, 31999.7)")
            .expect_var("result", -1i32)
            .check();
    }

    #[test]
    fn test_gfx_peek_errors() {
        for expr in &["GFX_PEEK()", "GFX_PEEK(1)", "GFX_PEEK(1, 2, 3)"] {
            check_expr_compilation_error("1:10: GFX_PEEK expected x%, y%", expr);
        }
        check_expr_compilation_error("1:20: Unexpected ;", "GFX_PEEK(1; 2)");

        for expr in &["GFX_PEEK(-40000, 1)", "GFX_PEEK(1, -40000)"] {
            let pos = expr.find('-').unwrap() + 10;
            check_expr_error(format!("1:{}: Coordinate -40000 out of range", pos), expr);
        }

        for expr in &["GFX_PEEK(40000, 1)", "GFX_PEEK(1, 40000)"] {
            let pos = expr.find('4').unwrap() + 10;
            check_expr_error(format!("1:{}: Coordinate 40000 out of range", pos), expr);
        }

        for expr in &[r#"GFX_PEEK("a", 1)"#, r#"GFX_PEEK(1, "a")"#] {
            let pos = expr.find('"').unwrap() + 10;
            check_expr_compilation_error(format!("1:{}: STRING is not a number", pos), expr);
        }
    }

    #[test]
    fn test_gfx_poly_ok() {
        Tester::default().run("GFX_POLY").expect_output([]).check();

        Tester::default()
            .run("GFX_POLY 1.1, 2.3")
            .expect_output([CapturedOut::DrawPixel(PixelsXY { x: 1, y: 2 })])
            .check();

        Tester::default()
            .run("GFX_POLY 1.1, 2.3, 2.5, 3.9")
            .expect_output([CapturedOut::DrawLine(
                PixelsXY { x: 1, y: 2 },
                PixelsXY { x: 3, y: 4 },
            )])
            .check();

        Tester::default()
            .run("GFX_POLY 1.1, 2.3, 2.5, 3.9, 4.4, 5.6")
            .expect_output([CapturedOut::DrawTri(
                PixelsXY { x: 1, y: 2 },
                PixelsXY { x: 3, y: 4 },
                PixelsXY { x: 4, y: 6 },
            )])
            .check();

        Tester::default()
            .run("GFX_POLY -31000, -32000, 31000, -32000, 0, 32000, -1, 0")
            .expect_output([CapturedOut::DrawPoly(vec![
                PixelsXY { x: -31000, y: -32000 },
                PixelsXY { x: 31000, y: -32000 },
                PixelsXY { x: 0, y: 32000 },
                PixelsXY { x: -1, y: 0 },
            ])])
            .check();

        Tester::default()
            .run(
                "DIM points(6) AS INTEGER\
                : points(0) = 1\
                : points(1) = 2\
                : points(2) = 3\
                : points(3) = 4\
                : points(4) = 5\
                : points(5) = 6\
                : GFX_POLY points",
            )
            .expect_output([CapturedOut::DrawTri(
                PixelsXY { x: 1, y: 2 },
                PixelsXY { x: 3, y: 4 },
                PixelsXY { x: 5, y: 6 },
            )])
            .check();

        Tester::default()
            .run(
                "DIM points(3, 2) AS INTEGER\
                : points(0, 0) = 1\
                : points(0, 1) = 2\
                : points(1, 0) = 3\
                : points(1, 1) = 4\
                : points(2, 0) = 5\
                : points(2, 1) = 6\
                : GFX_POLY points",
            )
            .expect_output([CapturedOut::DrawTri(
                PixelsXY { x: 1, y: 2 },
                PixelsXY { x: 3, y: 4 },
                PixelsXY { x: 5, y: 6 },
            )])
            .check();
    }

    #[test]
    fn test_gfx_poly_errors() {
        check_errors_poly("GFX_POLY");
    }

    #[test]
    fn test_gfx_polyf_ok() {
        Tester::default().run("GFX_POLYF").expect_output([]).check();

        Tester::default()
            .run("GFX_POLYF 1.1, 2.3")
            .expect_output([CapturedOut::DrawPixel(PixelsXY { x: 1, y: 2 })])
            .check();

        Tester::default()
            .run("GFX_POLYF 1.1, 2.3, 2.5, 3.9")
            .expect_output([CapturedOut::DrawLine(
                PixelsXY { x: 1, y: 2 },
                PixelsXY { x: 3, y: 4 },
            )])
            .check();

        Tester::default()
            .run("GFX_POLYF 1.1, 2.3, 2.5, 3.9, 4.4, 5.6")
            .expect_output([CapturedOut::DrawTriFilled(
                PixelsXY { x: 1, y: 2 },
                PixelsXY { x: 3, y: 4 },
                PixelsXY { x: 4, y: 6 },
            )])
            .check();

        Tester::default()
            .run("GFX_POLYF -31000, -32000, 31000, -32000, 0, 32000, -1, 0")
            .expect_output([CapturedOut::DrawPolyFilled(vec![
                PixelsXY { x: -31000, y: -32000 },
                PixelsXY { x: 31000, y: -32000 },
                PixelsXY { x: 0, y: 32000 },
                PixelsXY { x: -1, y: 0 },
            ])])
            .check();

        Tester::default()
            .run(
                "DIM points(6) AS INTEGER\
                : points(0) = 1\
                : points(1) = 2\
                : points(2) = 3\
                : points(3) = 4\
                : points(4) = 5\
                : points(5) = 6\
                : GFX_POLYF points",
            )
            .expect_output([CapturedOut::DrawTriFilled(
                PixelsXY { x: 1, y: 2 },
                PixelsXY { x: 3, y: 4 },
                PixelsXY { x: 5, y: 6 },
            )])
            .check();

        Tester::default()
            .run(
                "DIM points(3, 2) AS INTEGER\
                : points(0, 0) = 1\
                : points(0, 1) = 2\
                : points(1, 0) = 3\
                : points(1, 1) = 4\
                : points(2, 0) = 5\
                : points(2, 1) = 6\
                : GFX_POLYF points",
            )
            .expect_output([CapturedOut::DrawTriFilled(
                PixelsXY { x: 1, y: 2 },
                PixelsXY { x: 3, y: 4 },
                PixelsXY { x: 5, y: 6 },
            )])
            .check();
    }

    #[test]
    fn test_gfx_polyf_errors() {
        check_errors_poly("GFX_POLYF");
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
        check_stmt_compilation_err("1:1: GFX_SYNC expected <> | <enabled?>", "GFX_SYNC 2, 3");
        check_stmt_compilation_err("1:10: Expected BOOLEAN but found INTEGER", "GFX_SYNC 2");
    }

    #[test]
    fn test_gfx_tri_ok() {
        Tester::default()
            .run("GFX_TRI 1.1, 2.3, 2.5, 3.9, 4.4, 5.6")
            .expect_output([CapturedOut::DrawTri(
                PixelsXY { x: 1, y: 2 },
                PixelsXY { x: 3, y: 4 },
                PixelsXY { x: 4, y: 6 },
            )])
            .check();

        Tester::default()
            .run("GFX_TRI -31000, -32000, 31000, -32000, 0, 32000")
            .expect_output([CapturedOut::DrawTri(
                PixelsXY { x: -31000, y: -32000 },
                PixelsXY { x: 31000, y: -32000 },
                PixelsXY { x: 0, y: 32000 },
            )])
            .check();
    }

    #[test]
    fn test_gfx_tri_errors() {
        check_errors_three_xy("GFX_TRI");
    }

    #[test]
    fn test_gfx_trif_ok() {
        Tester::default()
            .run("GFX_TRIF 1.1, 2.3, 2.5, 3.9, 4.4, 5.6")
            .expect_output([CapturedOut::DrawTriFilled(
                PixelsXY { x: 1, y: 2 },
                PixelsXY { x: 3, y: 4 },
                PixelsXY { x: 4, y: 6 },
            )])
            .check();

        Tester::default()
            .run("GFX_TRIF -31000, -32000, 31000, -32000, 0, 32000")
            .expect_output([CapturedOut::DrawTriFilled(
                PixelsXY { x: -31000, y: -32000 },
                PixelsXY { x: 31000, y: -32000 },
                PixelsXY { x: 0, y: 32000 },
            )])
            .check();
    }

    #[test]
    fn test_gfx_trif_errors() {
        check_errors_three_xy("GFX_TRIF");
    }

    #[test]
    fn test_gfx_width() {
        let mut t = Tester::default();
        t.get_console().borrow_mut().set_size_pixels(SizeInPixels::new(12345, 1));
        t.run("result = GFX_WIDTH").expect_var("result", 12345i32).check();

        check_expr_error("1:10: Graphical console size not yet set", "GFX_WIDTH");

        check_expr_compilation_error("1:10: GFX_WIDTH expected no arguments", "GFX_WIDTH()");
        check_expr_compilation_error("1:10: GFX_WIDTH expected no arguments", "GFX_WIDTH(1)");
    }
}
