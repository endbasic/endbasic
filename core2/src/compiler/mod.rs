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
use crate::bytecode::{self, Register};
use crate::callable::Callable;
use crate::mem::Datum;
use crate::parser;
use crate::reader::LineCol;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::io;
use std::iter::Iterator;
use std::rc::Rc;

mod image;
pub(crate) use image::{DebugInfo, Image};

mod ids;
use ids::HashMapWithIds;

mod syms;
pub use syms::SymbolKey;
use syms::Symtable;

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
    OutOfRegisters(LineCol, &'static str),

    #[error("{0}: Out of upcalls")]
    OutOfUpcalls(LineCol),

    #[error("{0}: {1}")]
    ParseError(LineCol, String),

    #[error("{0}: Undefined {2} symbol {1}")]
    UndefinedSymbol(LineCol, VarRef, &'static str),
}

fn map_bytecode_make_error(pos: LineCol, e: bytecode::MakeError) -> Error {
    match e {
        bytecode::MakeError::OutOfRegisters(scope) => Error::OutOfRegisters(pos, scope),
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

type Address = usize;

enum Fixup {
    Call(Register, SymbolKey),
    Enter(u8),
}

struct Context<'a> {
    upcalls_by_name: &'a HashMap<SymbolKey, Rc<dyn Callable>>,
    upcalls: HashMapWithIds<SymbolKey, Option<ExprType>, u16>,
    code: Vec<u32>,
    constants: HashMapWithIds<Datum, ExprType, u16>,
    symtable: Symtable,
    fixups: HashMap<Address, Fixup>,
    user_callables: Vec<CallableSpan>,
    user_callables_addresses: HashMap<SymbolKey, Address>,
    instr_linecols: Vec<LineCol>,
}

impl<'a> Context<'a> {
    fn get_constant(&mut self, constant: Datum, pos: LineCol) -> Result<u16> {
        match self.constants.get(&constant) {
            Some((_etype, id)) => Ok(id),
            None => {
                let etype = constant.etype();
                match self.constants.insert(constant, etype) {
                    Some((_etype, id)) => Ok(id),
                    None => Err(Error::OutOfConstants(pos)),
                }
            }
        }
    }

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

    fn emit(&mut self, op: u32, pos: LineCol) -> Address {
        self.code.push(op);
        self.instr_linecols.push(pos);
        self.code.len() - 1
    }

    fn to_image(self) -> Image {
        let mut callables = HashMap::default();
        for (key, pc) in self.user_callables_addresses {
            let previous = callables.insert(pc, key);
            debug_assert!(previous.is_none(), "An address can only start one callable");
        }

        Image::new(
            self.code,
            self.upcalls.keys_to_vec(),
            self.constants.keys_to_vec(),
            DebugInfo { instr_linecols: self.instr_linecols, callables },
        )
    }
}

fn compile_expr(context: &mut Context, reg: Register, expr: Expr) -> Result<ExprType> {
    match expr {
        Expr::Boolean(span) => {
            let value = if span.value { 1 } else { 0 };
            context.emit(bytecode::make_load_integer(reg, value), span.pos);
            Ok(ExprType::Boolean)
        }

        Expr::Double(span) => {
            let index = context.get_constant(Datum::Double(span.value), span.pos)?;
            context.emit(bytecode::make_load_constant(reg, index), span.pos);
            Ok(ExprType::Double)
        }

        Expr::Integer(span) => {
            match u16::try_from(span.value) {
                Ok(i) => {
                    context.emit(bytecode::make_load_integer(reg, i), span.pos);
                }
                Err(_) => {
                    let index = context.get_constant(Datum::Integer(span.value), span.pos)?;
                    context.emit(bytecode::make_load_constant(reg, index), span.pos);
                }
            }
            Ok(ExprType::Integer)
        }

        Expr::Text(span) => {
            let index = context.get_constant(Datum::Text(span.value), span.pos)?;
            context.emit(bytecode::make_load_integer(reg, index), span.pos);
            Ok(ExprType::Text)
        }

        Expr::Add(span) => {
            let ltemp = context.symtable.alloc_temp(span.lhs.start_pos())?;
            let ltype = compile_expr(context, ltemp, span.lhs)?;

            let rtemp = context.symtable.alloc_temp(span.rhs.start_pos())?;
            let rtype = compile_expr(context, rtemp, span.rhs)?;

            let result = match (ltype, rtype) {
                (ExprType::Integer, ExprType::Integer) => {
                    context.emit(bytecode::make_add_integer(reg, ltemp, rtemp), span.pos);
                    Ok(ExprType::Integer)
                }

                (ExprType::Text, ExprType::Text) => {
                    context.emit(bytecode::make_concat(reg, ltemp, rtemp), span.pos);
                    Ok(ExprType::Text)
                }

                (_, _) => Err(Error::BinaryOpTypeError(span.pos, "+", ltype, rtype)),
            };

            context.symtable.dealloc_temps(2);
            result
        }

        Expr::Call(span) => {
            let key = SymbolKey::from(&span.vref.name);
            let (etype, _args) = match context.symtable.get_user_callable(&key) {
                Some((Some(etype), args)) => (*etype, args),
                Some((None, _args)) => {
                    return Err(Error::NotAFunction(span.vref_pos, span.vref));
                }
                None => {
                    return Err(Error::UndefinedSymbol(span.vref_pos, span.vref, "callable"));
                }
            };
            let addr = context.emit(bytecode::make_nop(), span.vref_pos);
            context.fixups.insert(addr, Fixup::Call(reg, key));
            Ok(etype)
        }

        Expr::Symbol(span) => {
            let (local, etype) = context.symtable.get_local(&span.vref, span.pos)?;
            context.emit(bytecode::make_move(reg, local), span.pos);
            Ok(etype)
        }

        _ => todo!(),
    }
}

fn compile_stmt(context: &mut Context, stmt: Statement) -> Result<()> {
    match stmt {
        Statement::Assignment(span) => {
            let local = context.symtable.put_local(&span.vref, span.vref_pos)?;
            let etype = compile_expr(context, local, span.expr)?;
            context.symtable.fixup_local_type(&span.vref, etype, span.vref_pos)?;
        }

        Statement::Call(span) => {
            let key = SymbolKey::from(span.vref.name);

            let first_temp = context.symtable.first_temp(span.vref_pos)?;

            // Arguments are represented as 1 or 2 consecutive registers.
            //
            // The first register always contains a `VarArgTag`, which indicates the type of
            // separator following the argument and, if an argument is present, its type.
            // The second register is only present if there is an argument.
            //
            // The caller must iterate over all tags until it finds `ArgSep::End`.
            let mut nregs = 0;
            for ArgSpan { expr, sep, sep_pos: _ } in span.args {
                let temp_tag = context.symtable.alloc_temp(span.vref_pos)?;
                nregs += 1;

                let tag = match expr {
                    None => bytecode::VarArgTag::Missing(sep),
                    Some(expr) => {
                        let temp_value = context.symtable.alloc_temp(span.vref_pos)?;
                        nregs += 1;
                        let etype = compile_expr(context, temp_value, expr)?;
                        bytecode::VarArgTag::Immediate(sep, etype)
                    }
                };
                context.emit(bytecode::make_load_integer(temp_tag, tag.make_u16()), span.vref_pos);
            }
            if nregs == 0 {
                let temp = context.symtable.alloc_temp(span.vref_pos)?;
                context.emit(
                    bytecode::make_load_integer(
                        temp,
                        bytecode::VarArgTag::Missing(ArgSep::End).make_u16(),
                    ),
                    span.vref_pos,
                );
                nregs += 1;
            }

            context.symtable.dealloc_temps(u8::try_from(nregs).expect("DO NOT SUBMIT"));
            let upcall = context.get_upcall(key, None, span.vref_pos)?;
            context.emit(bytecode::make_upcall(upcall, first_temp), span.vref_pos);
        }

        Statement::Callable(span) => {
            context.symtable.define_user_callable(
                &span.name,
                span.params.clone(),
                span.name_pos,
            )?;
            context.user_callables.push(span);
        }

        _ => todo!(),
    }
    Ok(())
}

fn compile_scope<I: Iterator<Item = Statement>>(context: &mut Context, stmts: I) -> Result<()> {
    let enter = context.emit(bytecode::make_nop(), LineCol { line: 0, col: 0 });
    for stmt in stmts {
        compile_stmt(context, stmt)?;
    }
    context.emit(bytecode::make_leave(), LineCol { line: 0, col: 0 }); // DO NOT SUBMIT
    let nlocals = context.symtable.frame_size();
    context.fixups.insert(enter, Fixup::Enter(nlocals));
    Ok(())
}

fn compile_user_callables(context: &mut Context) -> Result<()> {
    let mut addresses = HashMap::with_capacity(context.user_callables.len());

    let user_callables: Vec<CallableSpan> = context.user_callables.drain(..).collect();
    debug_assert!(context.user_callables.is_empty());

    for callable in user_callables {
        let start_pc = context.code.len();

        context.symtable.enter_scope();
        if callable.name.ref_type.is_some() {
            // The call protocol expects the return value to be in the _first_ local variable
            // so allocate it early.
            context.symtable.put_local(&callable.name, callable.name_pos)?;
        }

        compile_scope(context, callable.body.into_iter())?;
        if let Some(span) = context.user_callables.first() {
            return Err(Error::CannotNestUserCallables(span.name_pos));
        }

        context.symtable.leave_scope();

        context.emit(bytecode::make_return(), LineCol { line: 0, col: 0 }); // DO NOT SUBMIT
        addresses.insert(SymbolKey::from(callable.name.name), start_pc);
    }

    context.user_callables_addresses = addresses;
    Ok(())
}

pub fn compile(
    input: &mut dyn io::Read,
    upcalls_by_name: &HashMap<SymbolKey, Rc<dyn Callable>>,
) -> Result<Image> {
    let mut context = Context {
        upcalls_by_name,
        upcalls: HashMapWithIds::default(),
        code: vec![],
        constants: HashMapWithIds::default(),
        symtable: Symtable::default(),
        fixups: HashMap::default(),
        user_callables: vec![],
        user_callables_addresses: HashMap::default(),
        instr_linecols: vec![],
    };

    context.symtable.enter_scope();
    compile_scope(&mut context, parser::parse(input).map(|r| r.expect("DO NOT SUBMIT")))?;
    context.symtable.leave_scope();
    context.emit(bytecode::make_end(), LineCol { line: 0, col: 0 }); // DO NOT SUBMIT

    compile_user_callables(&mut context)?;

    for (addr, fixup) in &context.fixups {
        let instr = match fixup {
            Fixup::Call(reg, key) => {
                let target = context.user_callables_addresses.get(key).expect("Must be present");
                // DO NOT SUBMIT: Validate int change.
                bytecode::make_call(*reg, (target - *addr) as u16)
            }
            Fixup::Enter(nargs) => bytecode::make_enter(*nargs),
        };
        context.code[*addr] = instr;
    }

    Ok(context.to_image())
}
