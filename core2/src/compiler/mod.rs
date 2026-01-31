// EndBASIC
// Copyright 2026 Julio Merino
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
pub use top::{compile, only_metadata};

/// Compilation errors.
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)] // The error messages and names are good enough.
pub enum Error {
    #[error("{0}: Cannot redefine {1}")]
    AlreadyDefined(LineCol, VarRef),

    #[error("{0}: Cannot {1} {2} and {3}")]
    BinaryOpType(LineCol, &'static str, ExprType, ExprType),

    #[error("{0}: {} expected {}", .1.name(), .1.syntax())]
    CallableSyntax(LineCol, CallableMetadata),

    #[error("{0}: Cannot nest FUNCTION or SUB definitions")]
    CannotNestUserCallables(LineCol),

    #[error("{0}: I/O error during compilation: {1}")]
    Io(LineCol, io::Error),

    #[error("{0}: Cannot call {1} (not a function)")]
    NotAFunction(LineCol, VarRef),

    #[error("{0}: {1} is not a number")]
    NotANumber(LineCol, ExprType),

    #[error("{0}: Out of constants")]
    OutOfConstants(LineCol),

    #[error("{0}: Out of {1} registers")]
    OutOfRegisters(LineCol, RegisterScope),

    #[error("{0}: Out of upcalls")]
    OutOfUpcalls(LineCol),

    #[error("{0}: {1}")]
    Parse(LineCol, String),

    #[error("{0}: Expected {2} but found {1}")]
    TypeMismatch(LineCol, ExprType, ExprType),

    #[error("{0}: Undefined {2} symbol {1}")]
    UndefinedSymbol(LineCol, VarRef, RegisterScope),
}

impl Error {
    /// Annotates an error from the symbol table with the position it arised from.
    fn from_syms(value: syms::Error, pos: LineCol) -> Self {
        match value {
            syms::Error::AlreadyDefined(vref) => Error::AlreadyDefined(pos, vref),
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
