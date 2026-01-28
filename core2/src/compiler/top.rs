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

use crate::ast::{ArgSep, CallableSpan, ExprType, Statement, VarRef};
use crate::bytecode::{self, RegisterScope};
use crate::callable::{ArgSepSyntax, CallableMetadata, RequiredValueSyntax, SingularArgSyntax};
use crate::compiler::args::compile_args;
use crate::compiler::codegen::{Codegen, Fixup};
use crate::compiler::exprs::compile_expr;
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

#[derive(Default)]
struct Context {
    codegen: Codegen,
    upcalls: HashMapWithIds<SymbolKey, Option<ExprType>, u16>,
    user_callables: Vec<CallableSpan>,
}

impl Context {
    fn get_upcall(&mut self, key: SymbolKey, etype: Option<ExprType>, pos: LineCol) -> Result<u16> {
        // TODO: Validate name and more...
        // DO NOT SUBMIT: No type tracking for return values.
        match self.upcalls.get(&key) {
            Some((_etype, id)) => Ok(id),
            None => match self.upcalls.insert(key, etype) {
                Some((_etype, id)) => Ok(id),
                None => Err(Error::OutOfUpcalls(pos)),
            },
        }
    }
}

fn compile_stmt(
    ctx: &mut Context,
    symtable: &mut LocalSymtable<'_, '_, '_, '_>,
    stmt: Statement,
) -> Result<()> {
    match stmt {
        Statement::Assignment(span) => {
            let vref_pos = span.vref_pos;
            match symtable.get_global(&span.vref) {
                Ok((reg, _etype)) => {
                    let etype =
                        compile_expr(&mut ctx.codegen, &mut symtable.frozen(), reg, span.expr)?;
                    symtable.fixup_global_type(&span.vref, etype)
                }
                Err(syms::Error::UndefinedSymbol(..)) => {
                    let reg = symtable
                        .put_local(&span.vref)
                        .map_err(|e| Error::from_syms(e, span.vref_pos))?;
                    let etype =
                        compile_expr(&mut ctx.codegen, &mut symtable.frozen(), reg, span.expr)?;
                    symtable.fixup_local_type(&span.vref, etype)
                }
                Err(e) => Err(e),
            }
            .map_err(|e| Error::from_syms(e, vref_pos))?
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
            let name_pos = span.name_pos;
            let vref = match span.vtype {
                ExprType::Boolean => VarRef::new(span.name, Some(ExprType::Boolean)),
                ExprType::Double => VarRef::new(span.name, Some(ExprType::Double)),
                ExprType::Integer => VarRef::new(span.name, Some(ExprType::Integer)),
                ExprType::Text => VarRef::new(span.name, Some(ExprType::Text)),
            };
            let reg =
                if span.shared { symtable.put_global(&vref) } else { symtable.put_local(&vref) }
                    .map_err(|e| Error::from_syms(e, name_pos))?;
            let instr = match span.vtype {
                ExprType::Boolean => bytecode::make_load_integer(reg, 0),
                ExprType::Double => bytecode::make_load_integer(reg, 0),
                ExprType::Integer => bytecode::make_load_integer(reg, 0),
                ExprType::Text => bytecode::make_alloc(reg, ExprType::Text),
            };
            ctx.codegen.emit(instr, name_pos);
        }

        Statement::End(_span) => {
            // DO NOT SUBMIT: This exits immediately without doing the LEAVE that's required
            // for the current scope. Is that OK?
            // DO NOT SUBMIT: Evaluate return code and propagate it.
            ctx.codegen.emit(bytecode::make_end(), LineCol { line: 0, col: 0 });
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

fn compile_scope<I: Iterator<Item = Statement>>(
    ctx: &mut Context,
    mut symtable: LocalSymtable<'_, '_, '_, '_>,
    stmts: I,
) -> Result<()> {
    let enter = ctx.codegen.emit(bytecode::make_nop(), LineCol { line: 0, col: 0 });
    for stmt in stmts {
        compile_stmt(ctx, &mut symtable, stmt)?;
    }
    ctx.codegen.emit(bytecode::make_leave(), LineCol { line: 0, col: 0 }); // DO NOT SUBMIT
    let nlocals =
        symtable.leave_scope().map_err(|e| Error::from_syms(e, LineCol { line: 0, col: 0 }))?;
    ctx.codegen.add_fixup(enter, Fixup::Enter(nlocals));
    Ok(())
}

fn compile_user_callables(ctx: &mut Context, symtable: &mut GlobalSymtable) -> Result<()> {
    let user_callables: Vec<CallableSpan> = ctx.user_callables.drain(..).collect();
    debug_assert!(ctx.user_callables.is_empty());

    for callable in user_callables {
        let start_pc = ctx.codegen.next_pc();

        let mut symtable = symtable.enter_scope();
        if callable.name.ref_type.is_some() {
            // The call protocol expects the return value to be in the _first_ local variable
            // so allocate it early.
            symtable
                .put_local(&callable.name)
                .map_err(|e| Error::from_syms(e, callable.name_pos))?;
        }

        compile_scope(ctx, symtable, callable.body.into_iter())?;
        if let Some(span) = ctx.user_callables.first() {
            return Err(Error::CannotNestUserCallables(span.name_pos));
        }

        ctx.codegen.emit(bytecode::make_return(), LineCol { line: 0, col: 0 }); // DO NOT SUBMIT
        ctx.codegen.define_user_callable(SymbolKey::from(callable.name.name), start_pc);
    }

    Ok(())
}

pub fn only_metadata(
    upcalls_by_name: &HashMap<SymbolKey, Rc<dyn Callable>>,
) -> HashMap<&SymbolKey, &CallableMetadata> {
    let mut upcalls = HashMap::with_capacity(upcalls_by_name.len());
    for (name, callable) in upcalls_by_name {
        upcalls.insert(name, callable.metadata());
    }
    upcalls
}

pub fn compile(
    input: &mut dyn io::Read,
    upcalls: &HashMap<&SymbolKey, &CallableMetadata>,
) -> Result<Image> {
    let mut ctx = Context::default();

    let mut symtable = GlobalSymtable::new(upcalls);

    compile_scope(
        &mut ctx,
        symtable.enter_scope(),
        parser::parse(input).map(|r| r.expect("DO NOT SUBMIT")),
    )?;
    ctx.codegen.emit(bytecode::make_end(), LineCol { line: 0, col: 0 }); // DO NOT SUBMIT

    compile_user_callables(&mut ctx, &mut symtable)?;

    Ok(ctx.codegen.build_image(ctx.upcalls))
}
