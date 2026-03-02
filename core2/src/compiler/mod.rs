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

//! Compiler for the EndBASIC language into bytecode.

use crate::ast::{ExprType, VarRef};
use crate::bytecode::RegisterScope;
use crate::callable::CallableMetadata;
use crate::parser;
use crate::reader::LineCol;
use std::io;

mod args;

mod codegen;

mod exprs;

mod ids;

mod syms;
pub use syms::SymbolKey;

mod top;
pub use top::{GlobalDef, GlobalDefKind, compile, compile_with_globals, only_metadata};

/// Errors that can occur during compilation.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Attempt to redefine an already-defined symbol.
    #[error("{0}: Cannot redefine {1}")]
    AlreadyDefined(LineCol, VarRef),

    /// Array name used without subscripts (as a scalar).
    #[error("{0}: {1} is an array and requires subscripts")]
    ArrayUsedAsScalar(LineCol, VarRef),

    /// Type mismatch in a binary operation.
    #[error("{0}: Cannot {1} {2} and {3}")]
    BinaryOpType(LineCol, &'static str, ExprType, ExprType),

    /// Callable invoked with incorrect syntax.
    #[error("{0}: {} expected {}", .1.name(), .1.syntax())]
    CallableSyntax(LineCol, CallableMetadata),

    /// Attempt to nest FUNCTION or SUB definitions.
    #[error("{0}: Cannot nest FUNCTION or SUB definitions")]
    CannotNestUserCallables(LineCol),

    /// Type annotation in a reference doesn't match the variable's type.
    #[error("{0}: Incompatible type annotation in {1} reference")]
    IncompatibleTypeAnnotationInReference(LineCol, VarRef),

    /// Type mismatch in an assignment.
    #[error("{0}: Cannot assign value of type {1} to variable of type {2}")]
    IncompatibleTypesInAssignment(LineCol, ExprType, ExprType),

    /// I/O error while reading the source.
    #[error("{0}: I/O error during compilation: {1}")]
    Io(LineCol, io::Error),

    /// Attempt to call something that is not a function.
    #[error("{0}: Cannot call {1} (not a function)")]
    NotAFunction(LineCol, VarRef),

    /// `EXIT` statement found outside its expected block.
    #[error("{0}: EXIT {1} outside of {1}")]
    MisplacedExit(LineCol, &'static str),

    /// Attempt to index something that is not an array.
    #[error("{0}: {1} is not an array")]
    NotAnArray(LineCol, VarRef),

    /// Expected a numeric type but got something else.
    #[error("{0}: {1} is not a number")]
    NotANumber(LineCol, ExprType),

    /// Constants pool has been exhausted.
    #[error("{0}: Out of constants")]
    OutOfConstants(LineCol),

    /// Register allocation has been exhausted.
    #[error("{0}: Out of {1} registers")]
    OutOfRegisters(LineCol, RegisterScope),

    /// Upcall table has been exhausted.
    #[error("{0}: Out of upcalls")]
    OutOfUpcalls(LineCol),

    /// Syntax error from the parser.
    #[error("{0}: {1}")]
    Parse(LineCol, String),

    /// Jump or call target is too far away.
    #[error("{0}: Jump/call target is {1} which is too far")]
    TargetTooFar(LineCol, usize),

    /// An array has too many dimensions.
    #[error("{0}: Array cannot have {1} dimensions")]
    TooManyArrayDimensions(LineCol, usize),

    /// Type mismatch where a specific type was expected.
    #[error("{0}: Expected {2} but found {1}")]
    TypeMismatch(LineCol, ExprType, ExprType),

    /// Reference to an undefined symbol.
    #[error("{0}: Undefined {2} symbol {1}")]
    UndefinedSymbol(LineCol, VarRef, RegisterScope),

    /// Wrong number of subscripts for an array access.
    #[error("{0}: Array requires {1} subscripts but got {2}")]
    WrongNumberOfSubscripts(LineCol, usize, usize),
}

impl Error {
    /// Annotates an error from the symbol table with the position it arised from.
    fn from_syms(value: syms::Error, pos: LineCol) -> Self {
        match value {
            syms::Error::AlreadyDefined(vref) => Error::AlreadyDefined(pos, vref),
            syms::Error::IncompatibleTypeAnnotationInReference(vref) => {
                Error::IncompatibleTypeAnnotationInReference(pos, vref)
            }
            syms::Error::OutOfRegisters(scope) => Error::OutOfRegisters(pos, scope),
            syms::Error::UndefinedSymbol(vref, scope) => Error::UndefinedSymbol(pos, vref, scope),
        }
    }
}

impl From<parser::Error> for Error {
    fn from(value: parser::Error) -> Self {
        match value {
            parser::Error::Bad(pos, message) => Self::Parse(pos, message),
            parser::Error::Io(pos, e) => Self::Io(pos, e),
        }
    }
}

/// Result type for compilation operations.
pub type Result<T> = std::result::Result<T, Error>;
