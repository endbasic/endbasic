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

//! Entry point to the compilation, handling top-level definitions.

use crate::ast::{ArgSep, AssignmentSpan, CallableSpan, EndSpan, ExprType, Statement};
use crate::bytecode::{self, RegisterScope};
use crate::callable::{ArgSepSyntax, CallableMetadata, RequiredValueSyntax, SingularArgSyntax};
use crate::compiler::args::compile_args;
use crate::compiler::codegen::{Codegen, Fixup};
use crate::compiler::exprs::{compile_expr, compile_expr_as_type};
use crate::compiler::ids::HashMapWithIds;
use crate::compiler::syms::{self, GlobalSymtable, LocalSymtable, SymbolKey};
use crate::compiler::{Error, Result};
use crate::image::Image;
use crate::reader::LineCol;
use crate::{Callable, CallableMetadataBuilder, parser};
use std::borrow::Cow;
use std::collections::HashMap;
use std::io;
use std::iter::Iterator;
use std::rc::Rc;

/// Bag of state required by various top-level compilation functions.
///
/// This type exists to minimize the number of complex arguments passed across functions.
/// If possible, avoid passing it and instead pass the minimum set of required fields.
#[derive(Default)]
struct Context {
    /// The code generator accumulating bytecode instructions.
    codegen: Codegen,

    /// Map of built-in callable names to their return types and assigned upcall IDs.
    upcalls: HashMapWithIds<SymbolKey, Option<ExprType>, u16>,

    /// Collection of user-defined callable definitions to be compiled after the main scope.
    user_callables: Vec<CallableSpan>,
}

impl Context {
    /// Gets the existing upcall ID for the given `key` or creates a new one.
    fn get_upcall(&mut self, key: SymbolKey, etype: Option<ExprType>, pos: LineCol) -> Result<u16> {
        if etype.is_some() {
            todo!("Function upcalls not implemented yet");
        }
        match self.upcalls.get(&key) {
            Some((_etype, id)) => Ok(id),
            None => match self.upcalls.insert(key, etype) {
                Some((_etype, id)) => Ok(id),
                None => Err(Error::OutOfUpcalls(pos)),
            },
        }
    }
}

/// Compiles an assignment statement `span` into the `codegen` block.
fn compile_assignment(
    codegen: &mut Codegen,
    symtable: &mut LocalSymtable<'_, '_, '_, '_>,
    span: AssignmentSpan,
) -> Result<()> {
    let vref_pos = span.vref_pos;

    let (reg, etype) = match symtable.get_local_or_global(&span.vref) {
        Ok((reg, etype)) => (reg, Some(etype)),

        Err(syms::Error::UndefinedSymbol(..)) => {
            let key = SymbolKey::from(span.vref.name.clone());
            let reg = symtable
                .put_local(key, span.vref.ref_type.unwrap_or(ExprType::Integer))
                .map_err(|e| Error::from_syms(e, span.vref_pos))?;
            match span.vref.ref_type {
                Some(etype) => (reg, Some(etype)),
                None => (reg, None),
            }
        }

        Err(e) => return Err(Error::from_syms(e, vref_pos)),
    };

    if let Some(etype) = etype {
        // The destination variable already exists.  Try to compile the expression into its target
        // type and fail otherwise with a better error message.
        match compile_expr_as_type(codegen, &mut symtable.frozen(), reg, span.expr, etype) {
            Err(Error::TypeMismatch(pos, actual, expected)) => {
                return Err(Error::IncompatibleTypesInAssignment(pos, actual, expected));
            }
            r => return r,
        }
    }

    // The destination variable doesn't exist yet but `symtable.put_local` already inserted it
    // with the default type we gave above as part of assigning it a register.  Use the
    // expression's type to fix up the type in the symbols table.
    let etype = compile_expr(codegen, &mut symtable.frozen(), reg, span.expr)?;
    symtable.fixup_local_type(&span.vref, etype).map_err(|e| Error::from_syms(e, vref_pos))
}

/// Compiles a single `stmt` into the `ctx`.
fn compile_stmt(
    ctx: &mut Context,
    symtable: &mut LocalSymtable<'_, '_, '_, '_>,
    stmt: Statement,
) -> Result<()> {
    match stmt {
        Statement::Assignment(span) => {
            compile_assignment(&mut ctx.codegen, symtable, span)?;
        }

        Statement::Call(span) => {
            let key = SymbolKey::from(&span.vref.name);
            let key_pos = span.vref_pos;

            let mut symtable = symtable.frozen();

            let Some(md) = symtable.get_callable(&key) else {
                return Err(Error::UndefinedSymbol(
                    key_pos,
                    span.vref.clone(),
                    RegisterScope::Global,
                ));
            };
            let is_user_defined = md.is_user_defined();

            let first_temp = compile_args(span, &mut symtable, &mut ctx.codegen)?;

            if is_user_defined {
                let addr = ctx.codegen.emit(bytecode::make_nop(), key_pos);
                ctx.codegen.add_fixup(addr, Fixup::Call(first_temp, key));
            } else {
                let upcall = ctx.get_upcall(key, None, key_pos)?;
                ctx.codegen.emit(bytecode::make_upcall(upcall, first_temp), key_pos);
            }
        }

        Statement::Callable(span) => {
            let mut syntax = vec![];
            for (i, param) in span.params.iter().enumerate() {
                let sep = if i == span.params.len() - 1 {
                    ArgSepSyntax::End
                } else {
                    ArgSepSyntax::Exactly(ArgSep::Long)
                };
                syntax.push(SingularArgSyntax::RequiredValue(
                    RequiredValueSyntax {
                        name: Cow::Owned(param.name.to_owned()),
                        vtype: param.ref_type.unwrap_or(ExprType::Integer),
                    },
                    sep,
                ));
            }

            let mut builder = CallableMetadataBuilder::new_dynamic(span.name.name.to_owned())
                .with_dynamic_syntax(vec![(syntax, None)]);
            if let Some(ctype) = span.name.ref_type {
                builder = builder.with_return_type(ctype);
            }

            symtable
                .define_user_callable(&span.name, builder.build())
                .map_err(|e| Error::from_syms(e, span.name_pos))?;
            ctx.user_callables.push(span);
        }

        Statement::Dim(span) => {
            let key = SymbolKey::from(span.name);
            let name_pos = span.name_pos;
            let reg = if span.shared {
                symtable.put_global(key, span.vtype)
            } else {
                symtable.put_local(key, span.vtype)
            }
            .map_err(|e| Error::from_syms(e, name_pos))?;
            let instr = match span.vtype {
                ExprType::Boolean => bytecode::make_load_integer(reg, 0),
                ExprType::Double => bytecode::make_load_integer(reg, 0),
                ExprType::Integer => bytecode::make_load_integer(reg, 0),
                ExprType::Text => bytecode::make_alloc(reg, ExprType::Text),
            };
            ctx.codegen.emit(instr, name_pos);
        }

        Statement::End(span) => {
            let mut symtable = symtable.frozen();
            let mut scope = symtable.temp_scope();
            let reg = scope.alloc().map_err(|e| Error::from_syms(e, span.pos))?;
            match span.code {
                Some(expr) => {
                    compile_expr_as_type(
                        &mut ctx.codegen,
                        &mut symtable,
                        reg,
                        expr,
                        ExprType::Integer,
                    )?;
                }
                None => {
                    ctx.codegen.emit(bytecode::make_load_integer(reg, 0), span.pos);
                }
            }
            ctx.codegen.emit(bytecode::make_end(reg), span.pos);
        }

        Statement::Gosub(span) => {
            let addr = ctx.codegen.emit(bytecode::make_nop(), span.target_pos);
            ctx.codegen.add_fixup(addr, Fixup::Gosub(SymbolKey::from(span.target)));
        }

        Statement::Goto(span) => {
            let addr = ctx.codegen.emit(bytecode::make_nop(), span.target_pos);
            ctx.codegen.add_fixup(addr, Fixup::Goto(SymbolKey::from(span.target)));
        }

        Statement::Label(span) => {
            ctx.codegen.define_label(SymbolKey::from(span.name), ctx.codegen.next_pc());
        }

        Statement::Return(span) => {
            ctx.codegen.emit(bytecode::make_return(), span.pos);
        }

        _ => todo!(),
    }
    Ok(())
}

/// Compiles a sequence of `stmts` that all live in the same `symtable` scope.
fn compile_scope<I>(
    ctx: &mut Context,
    mut symtable: LocalSymtable<'_, '_, '_, '_>,
    stmts: I,
) -> Result<()>
where
    I: Iterator<Item = std::result::Result<Statement, parser::Error>>,
{
    let enter = ctx.codegen.emit(bytecode::make_nop(), LineCol { line: 0, col: 0 });
    for stmt in stmts {
        compile_stmt(ctx, &mut symtable, stmt?)?;
    }
    let nlocals =
        symtable.leave_scope().map_err(|e| Error::from_syms(e, LineCol { line: 0, col: 0 }))?;
    ctx.codegen.add_fixup(enter, Fixup::Enter(nlocals));
    Ok(())
}

/// Compiles all user-defined callables that have been captured in `ctx`.
fn compile_user_callables(ctx: &mut Context, symtable: &mut GlobalSymtable) -> Result<()> {
    let user_callables: Vec<CallableSpan> = ctx.user_callables.drain(..).collect();
    debug_assert!(ctx.user_callables.is_empty());

    for callable in user_callables {
        let start_pc = ctx.codegen.next_pc();

        let key_pos = callable.name_pos;
        let key = SymbolKey::from(callable.name.name);

        let mut symtable = symtable.enter_scope();
        if let Some(vtype) = callable.name.ref_type {
            // The call protocol expects the return value to be in the _first_ local variable
            // so allocate it early.
            symtable.put_local(key.clone(), vtype).map_err(|e| Error::from_syms(e, key_pos))?;
        }

        compile_scope(ctx, symtable, callable.body.into_iter().map(Ok))?;
        if let Some(span) = ctx.user_callables.first() {
            return Err(Error::CannotNestUserCallables(span.name_pos));
        }

        ctx.codegen.emit(bytecode::make_return(), callable.end_pos);
        ctx.codegen.define_user_callable(key, start_pc);
    }

    Ok(())
}

/// Extracts the metadata of all provided `upcalls`.
pub fn only_metadata(
    upcalls_by_name: &HashMap<SymbolKey, Rc<dyn Callable>>,
) -> HashMap<&SymbolKey, &CallableMetadata> {
    let mut upcalls = HashMap::with_capacity(upcalls_by_name.len());
    for (name, callable) in upcalls_by_name {
        upcalls.insert(name, callable.metadata());
    }
    upcalls
}

/// Compiles the `input` into an `Image` that can be executed by the VM.
///
/// `upcalls` contains the metadata of all built-in callables that the compiled code can use.
pub fn compile(
    input: &mut dyn io::Read,
    upcalls: &HashMap<&SymbolKey, &CallableMetadata>,
) -> Result<Image> {
    let mut ctx = Context::default();

    let mut symtable = GlobalSymtable::new(upcalls);

    let program_end = Statement::End(EndSpan { code: None, pos: LineCol { line: 0, col: 0 } });
    compile_scope(&mut ctx, symtable.enter_scope(), parser::parse(input).chain([Ok(program_end)]))?;

    compile_user_callables(&mut ctx, &mut symtable)?;

    ctx.codegen.build_image(ctx.upcalls)
}
