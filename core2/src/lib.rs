// EndBASIC
// Copyright 2020 Julio Merino
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

//! The EndBASIC core language parser, compiler, and virtual machine.

mod ast;
mod bytecode;
mod callable;
mod compiler;
mod image;
mod lexer;
mod mem;
mod num;
mod parser;
mod reader;
mod vm;

pub use ast::{ArgSep, ExprType};
pub use bytecode::{ExitCode, InvalidExitCodeError, VarArgTag};
pub use callable::*;
pub use compiler::{Compiler, GlobalDef, GlobalDefKind, SymbolKey, only_metadata};
pub use mem::ConstantDatum;
pub use vm::{GetGlobalError, GetGlobalResult, StopReason, Vm};

#[cfg(test)]
mod testutils;
