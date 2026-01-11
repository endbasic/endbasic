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

//! Common compilers for callable arguments.

use crate::ast::{ArgSep, ArgSpan, CallSpan};
use crate::bytecode::{self, Register, RegisterScope};
use crate::callable::{CallableMetadata, CallableSyntax};
use crate::compiler::codegen::Codegen;
use crate::compiler::exprs::compile_expr;
use crate::compiler::syms::TempSymtable;
use crate::compiler::{Error, Result, SymbolKey};
use crate::reader::LineCol;

/// Finds the syntax definition that matches the given argument count.
///
/// Returns an error if no syntax matches, and panics if multiple syntaxes match (which would
/// indicate an ambiguous callable definition).
fn find_syntax(md: &CallableMetadata, pos: LineCol, nargs: usize) -> Result<&CallableSyntax> {
    let mut matches = md.syntaxes().iter().filter(|s| s.expected_nargs().contains(&nargs));
    let syntax = matches.next();
    match syntax {
        Some(syntax) => {
            debug_assert!(matches.next().is_none(), "Ambiguous syntax definitions");
            Ok(syntax)
        }
        None => Err(Error::CallableSyntax(pos, md.clone())),
    }
}

/// Compiles the arguments of a callable invocation.
///
/// Returns the first register containing the compiled arguments. Arguments are laid out as
/// pairs of type tag and value registers, allowing the callable to interpret them at runtime.
pub(super) fn compile_args(
    span: CallSpan,
    symtable: &mut TempSymtable<'_, '_, '_, '_, '_>,
    codegen: &mut Codegen,
) -> Result<Register> {
    let key = SymbolKey::from(&span.vref.name);
    let key_pos = span.vref_pos;

    let Some(md) = symtable.get_callable(&key) else {
        return Err(Error::UndefinedSymbol(key_pos, span.vref.clone(), RegisterScope::Global));
    };

    let mut scope = symtable.temp_scope();

    let _syntax = find_syntax(md, key_pos, span.args.len())?;

    // Arguments are represented as 1 or 2 consecutive registers.
    //
    // The first register always contains a `VarArgTag`, which indicates the type of
    // separator following the argument and, if an argument is present, its type.
    // The second register is only present if there is an argument.
    //
    // The caller must iterate over all tags until it finds `ArgSep::End`.
    let nargs = span.args.len();
    for ArgSpan { expr, sep, sep_pos } in span.args {
        let arg_pos = expr.as_ref().map(|e| e.start_pos()).unwrap_or(sep_pos);
        let temp_tag = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;

        let tag = match expr {
            None => bytecode::VarArgTag::Missing(sep),
            Some(expr) => {
                let temp_value = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;
                let etype = compile_expr(codegen, symtable, temp_value, expr)?;
                bytecode::VarArgTag::Immediate(sep, etype)
            }
        };
        codegen.emit(bytecode::make_load_integer(temp_tag, tag.make_u16()), arg_pos);
    }
    if nargs == 0 {
        let temp = scope.alloc().map_err(|e| Error::from_syms(e, key_pos))?;
        codegen.emit(
            bytecode::make_load_integer(temp, bytecode::VarArgTag::Missing(ArgSep::End).make_u16()),
            key_pos,
        );
    }

    scope.first().map_err(|e| Error::from_syms(e, key_pos))
}
