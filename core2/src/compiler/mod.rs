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

use crate::ast::{ArgSep, ArgSpan, CallableSpan, Expr, ExprType, Statement, VarRef};
use crate::bytecode::{self, Register, RegisterScope};
use crate::callable::Callable;
use crate::mem::Datum;
use crate::parser;
use crate::reader::LineCol;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::io;
use std::iter::Iterator;
use std::rc::Rc;

mod codegen;
use codegen::{Codegen, Fixup};

mod image;
pub(crate) use image::{DebugInfo, Image};

mod ids;
use ids::HashMapWithIds;

mod syms;
pub use syms::SymbolKey;
use syms::{GlobalSymtable, LocalSymtable, TempSymtable};

/// Compilation errors.
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)] // The error messages and names are good enough.
pub enum Error {
    #[error("{0}: Cannot redefine {1}")]
    AlreadyDefined(LineCol, VarRef),

    #[error("{0}: Cannot {1} {2} and {3}")]
    BinaryOpTypeError(LineCol, &'static str, ExprType, ExprType),

    #[error("{0}: Cannot nest FUNCTION or SUB definitions")]
    CannotNestUserCallables(LineCol),

    #[error("{0}: I/O error during compilation: {1}")]
    IoError(LineCol, io::Error),

    #[error("{0}: Cannot call {1} (not a function)")]
    NotAFunction(LineCol, VarRef),

    #[error("{0}: Out of constants")]
    OutOfConstants(LineCol),

    #[error("{0}: Out of {1} registers")]
    OutOfRegisters(LineCol, RegisterScope),

    #[error("{0}: Out of upcalls")]
    OutOfUpcalls(LineCol),

    #[error("{0}: {1}")]
    ParseError(LineCol, String),

    #[error("{0}: Undefined {2} symbol {1}")]
    UndefinedSymbol(LineCol, VarRef, RegisterScope),
}

impl Error {
    fn from_syms(value: syms::Error, pos: LineCol) -> Self {
        match value {
            syms::Error::AlreadyDefined(vref) => Error::AlreadyDefined(pos, vref),
            syms::Error::OutOfRegisters(scope) => Error::OutOfRegisters(pos, scope),
            syms::Error::UndefinedSymbol(vref, scope) => Error::UndefinedSymbol(pos, vref, scope),
        }
    }
}

type Result<T> = std::result::Result<T, Error>;

impl From<parser::Error> for Error {
    fn from(value: parser::Error) -> Self {
        match value {
            parser::Error::Bad(pos, message) => Self::ParseError(pos, message),
            parser::Error::Io(pos, e) => Self::IoError(pos, e),
        }
    }
}

struct Context<'a> {
    upcalls_by_name: &'a HashMap<SymbolKey, Rc<dyn Callable>>,
    upcalls: HashMapWithIds<SymbolKey, Option<ExprType>, u16>,
    user_callables: Vec<CallableSpan>,
}

impl<'a> Context<'a> {
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

fn compile_expr(
    codegen: &mut Codegen,
    symtable: &mut TempSymtable<'_, '_>,
    reg: Register,
    expr: Expr,
) -> Result<ExprType> {
    match expr {
        Expr::Boolean(span) => {
            let value = if span.value { 1 } else { 0 };
            codegen.emit(bytecode::make_load_integer(reg, value), span.pos);
            Ok(ExprType::Boolean)
        }

        Expr::Double(span) => {
            let index = codegen.get_constant(Datum::Double(span.value), span.pos)?;
            codegen.emit(bytecode::make_load_constant(reg, index), span.pos);
            Ok(ExprType::Double)
        }

        Expr::Integer(span) => {
            match u16::try_from(span.value) {
                Ok(i) => {
                    codegen.emit(bytecode::make_load_integer(reg, i), span.pos);
                }
                Err(_) => {
                    let index = codegen.get_constant(Datum::Integer(span.value), span.pos)?;
                    codegen.emit(bytecode::make_load_constant(reg, index), span.pos);
                }
            }
            Ok(ExprType::Integer)
        }

        Expr::Text(span) => {
            let index = codegen.get_constant(Datum::Text(span.value), span.pos)?;
            codegen.emit(bytecode::make_load_integer(reg, index), span.pos);
            Ok(ExprType::Text)
        }

        Expr::Add(span) => {
            let mut scope = symtable.temp_scope();

            let lpos = span.lhs.start_pos();
            let ltemp = scope.alloc().map_err(|e| Error::from_syms(e, lpos))?;
            let ltype = compile_expr(codegen, symtable, ltemp, span.lhs)?;

            let rpos = span.rhs.start_pos();
            let rtemp = scope.alloc().map_err(|e| Error::from_syms(e, rpos))?;
            let rtype = compile_expr(codegen, symtable, rtemp, span.rhs)?;

            let result = match (ltype, rtype) {
                (ExprType::Integer, ExprType::Integer) => {
                    codegen.emit(bytecode::make_add_integer(reg, ltemp, rtemp), span.pos);
                    Ok(ExprType::Integer)
                }

                (ExprType::Text, ExprType::Text) => {
                    codegen.emit(bytecode::make_concat(reg, ltemp, rtemp), span.pos);
                    Ok(ExprType::Text)
                }

                (_, _) => Err(Error::BinaryOpTypeError(span.pos, "+", ltype, rtype)),
            };

            result
        }

        Expr::Call(span) => {
            let key = SymbolKey::from(&span.vref.name);
            let (etype, _args) = match symtable.get_user_callable(&key) {
                Some((Some(etype), args)) => (*etype, args),
                Some((None, _args)) => {
                    return Err(Error::NotAFunction(span.vref_pos, span.vref));
                }
                None => {
                    return Err(Error::UndefinedSymbol(
                        span.vref_pos,
                        span.vref,
                        RegisterScope::Global,
                    ));
                }
            };
            let addr = codegen.emit(bytecode::make_nop(), span.vref_pos);
            codegen.add_fixup(addr, Fixup::Call(reg, key));
            Ok(etype)
        }

        Expr::Symbol(span) => {
            let (local, etype) = symtable
                .get_local_or_global(&span.vref)
                .map_err(|e| Error::from_syms(e, span.pos))?;
            codegen.emit(bytecode::make_move(reg, local), span.pos);
            Ok(etype)
        }

        _ => todo!(),
    }
}

fn compile_stmt<'a, 'b>(
    context: &mut Context,
    symtable: &'a mut LocalSymtable<'b>,
    codegen: &mut Codegen,
    stmt: Statement,
) -> Result<()> {
    match stmt {
        Statement::Assignment(span) => {
            let vref_pos = span.vref_pos;
            match symtable.get_global(&span.vref) {
                Ok((reg, _etype)) => {
                    let etype = compile_expr(codegen, &mut symtable.frozen(), reg, span.expr)?;
                    symtable.fixup_global_type(&span.vref, etype)
                }
                Err(syms::Error::UndefinedSymbol(..)) => {
                    let reg = symtable
                        .put_local(&span.vref)
                        .map_err(|e| Error::from_syms(e, span.vref_pos))?;
                    let etype = compile_expr(codegen, &mut symtable.frozen(), reg, span.expr)?;
                    symtable.fixup_local_type(&span.vref, etype)
                }
                Err(e) => Err(e),
            }
            .map_err(|e| Error::from_syms(e, vref_pos))?
        }

        Statement::Call(span) => {
            let key = SymbolKey::from(span.vref.name);
            let key_pos = span.vref_pos;

            let mut symtable = symtable.frozen();
            let mut scope = symtable.temp_scope();

            let first_temp = scope.first().map_err(|e| Error::from_syms(e, key_pos))?;

            // Arguments are represented as 1 or 2 consecutive registers.
            //
            // The first register always contains a `VarArgTag`, which indicates the type of
            // separator following the argument and, if an argument is present, its type.
            // The second register is only present if there is an argument.
            //
            // The caller must iterate over all tags until it finds `ArgSep::End`.
            let nargs = span.args.len();
            for ArgSpan { expr, sep, sep_pos: _ } in span.args {
                let temp_tag = scope.alloc().map_err(|e| Error::from_syms(e, key_pos))?;

                let tag = match expr {
                    None => bytecode::VarArgTag::Missing(sep),
                    Some(expr) => {
                        let temp_value = scope.alloc().map_err(|e| Error::from_syms(e, key_pos))?;
                        let etype = compile_expr(codegen, &mut symtable, temp_value, expr)?;
                        bytecode::VarArgTag::Immediate(sep, etype)
                    }
                };
                codegen.emit(bytecode::make_load_integer(temp_tag, tag.make_u16()), span.vref_pos);
            }
            if nargs == 0 {
                let temp = scope.alloc().map_err(|e| Error::from_syms(e, key_pos))?;
                codegen.emit(
                    bytecode::make_load_integer(
                        temp,
                        bytecode::VarArgTag::Missing(ArgSep::End).make_u16(),
                    ),
                    span.vref_pos,
                );
            }

            drop(scope);
            let upcall = context.get_upcall(key, None, span.vref_pos)?;
            codegen.emit(bytecode::make_upcall(upcall, first_temp), span.vref_pos);
        }

        Statement::Callable(span) => {
            symtable
                .define_user_callable(&span.name, span.params.clone())
                .map_err(|e| Error::from_syms(e, span.name_pos))?;
            context.user_callables.push(span);
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
            codegen.emit(instr, name_pos);
        }

        _ => todo!(),
    }
    Ok(())
}

fn compile_scope<'a, I: Iterator<Item = Statement>>(
    context: &mut Context,
    mut symtable: LocalSymtable<'a>,
    codegen: &mut Codegen,
    stmts: I,
) -> Result<()> {
    let enter = codegen.emit(bytecode::make_nop(), LineCol { line: 0, col: 0 });
    for stmt in stmts {
        compile_stmt(context, &mut symtable, codegen, stmt)?;
    }
    codegen.emit(bytecode::make_leave(), LineCol { line: 0, col: 0 }); // DO NOT SUBMIT
    let nlocals =
        symtable.leave_scope().map_err(|e| Error::from_syms(e, LineCol { line: 0, col: 0 }))?;
    codegen.add_fixup(enter, Fixup::Enter(nlocals));
    Ok(())
}

fn compile_user_callables(
    context: &mut Context,
    symtable: &mut GlobalSymtable,
    codegen: &mut Codegen,
) -> Result<()> {
    let user_callables: Vec<CallableSpan> = context.user_callables.drain(..).collect();
    debug_assert!(context.user_callables.is_empty());

    for callable in user_callables {
        let start_pc = codegen.next_pc();

        let mut symtable = symtable.enter_scope();
        if callable.name.ref_type.is_some() {
            // The call protocol expects the return value to be in the _first_ local variable
            // so allocate it early.
            symtable
                .put_local(&callable.name)
                .map_err(|e| Error::from_syms(e, callable.name_pos))?;
        }

        compile_scope(context, symtable, codegen, callable.body.into_iter())?;
        if let Some(span) = context.user_callables.first() {
            return Err(Error::CannotNestUserCallables(span.name_pos));
        }

        codegen.emit(bytecode::make_return(), LineCol { line: 0, col: 0 }); // DO NOT SUBMIT
        codegen.define_user_callable(SymbolKey::from(callable.name.name), start_pc);
    }

    Ok(())
}

pub fn compile(
    input: &mut dyn io::Read,
    upcalls_by_name: &HashMap<SymbolKey, Rc<dyn Callable>>,
) -> Result<Image> {
    let mut context =
        Context { upcalls_by_name, upcalls: HashMapWithIds::default(), user_callables: vec![] };
    let mut codegen = Codegen::default();

    let mut symtable = GlobalSymtable::default();

    compile_scope(
        &mut context,
        symtable.enter_scope(),
        &mut codegen,
        parser::parse(input).map(|r| r.expect("DO NOT SUBMIT")),
    )?;
    codegen.emit(bytecode::make_end(), LineCol { line: 0, col: 0 }); // DO NOT SUBMIT

    compile_user_callables(&mut context, &mut symtable, &mut codegen)?;

    Ok(codegen.build_image(context))
}
