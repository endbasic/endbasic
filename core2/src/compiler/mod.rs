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

use crate::ast::{ArgSpan, Expr, Statement};
use crate::bytecode::{self, Register};
use crate::callable::Callable;
use crate::parser;
use crate::reader::LineCol;
use std::collections::HashMap;
use std::io;
use std::rc::Rc;

mod image;
pub(crate) use image::{Constant, Image};

mod ids;
use ids::IdAssigner;

mod syms;
pub use syms::SymbolKey;
use syms::Symtable;

/// Compilation errors.
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)] // The error messages and names are good enough.
pub enum Error {
    #[error("{0}: I/O error during compilation: {1}")]
    IoError(LineCol, io::Error),

    #[error("{0}: Out of {0} registers")]
    OutOfRegisters(LineCol, &'static str),

    #[error("{0}: {1}")]
    ParseError(LineCol, String),
}

fn map_bytecode_error(pos: LineCol, e: bytecode::Error) -> Error {
    match e {
        bytecode::Error::OutOfRegisters(scope) => Error::OutOfRegisters(pos, scope),
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
    Enter(u8),
}

struct Context<'a> {
    upcalls_by_name: &'a HashMap<SymbolKey, Rc<dyn Callable>>,
    upcalls: IdAssigner<SymbolKey, u16>,
    code: Vec<u32>,
    constants: IdAssigner<Constant, usize>,
    symtable: Symtable,
    fixups: HashMap<Address, Fixup>,
    num_temps: usize,
}

impl<'a> Context<'a> {
    fn constant(&mut self, constant: Constant) -> usize {
        self.constants.get(&constant)
    }

    fn upcall(&mut self, key: SymbolKey) -> u16 {
        // TODO: Validate name and more...
        self.upcalls.get(&key)
    }

    fn emit(&mut self, op: u32) -> Address {
        self.code.push(op);
        self.code.len() - 1
    }

    fn to_image(self) -> Image {
        Image {
            code: self.code,
            data: vec![],
            upcalls: self.upcalls.to_vec(),
            constants: self.constants.to_vec(),
        }
    }
}

fn compile_expr(context: &mut Context, reg: Register, expr: Expr) -> Result<()> {
    match expr {
        Expr::Integer(span) => {
            if span.value < (0x00ffffff as i32) {
                context.emit(bytecode::make_load_integer(reg, span.value as u16));
            } else {
                let index = context.constant(Constant::Integer(span.value));
                context.emit(bytecode::make_load_integer_constant(reg, index as u16));
            }
        }

        Expr::Add(span) => {
            let temp1 = context.symtable.alloc_temp(span.lhs.start_pos())?;
            compile_expr(context, temp1, span.lhs)?;
            let temp2 = context.symtable.alloc_temp(span.rhs.start_pos())?;
            compile_expr(context, temp2, span.rhs)?;
            context.emit(bytecode::make_add_integer(reg, temp1, temp2));
            context.symtable.dealloc_temps(2);
        }

        _ => todo!(),
    }

    Ok(())
}

pub fn compile(
    input: &mut dyn io::Read,
    upcalls_by_name: &HashMap<SymbolKey, Rc<dyn Callable>>,
) -> Result<Image> {
    let mut context = Context {
        upcalls_by_name,
        upcalls: IdAssigner::default(),
        code: vec![],
        constants: IdAssigner::default(),
        symtable: Symtable::default(),
        fixups: HashMap::default(),
        num_temps: 0,
    };

    let enter = context.emit(bytecode::make_nop());
    for stmt in parser::parse(input) {
        match stmt? {
            Statement::Assignment(span) => {
                let key = SymbolKey::from(span.vref.name);
                let local = context.symtable.local(&key, span.vref_pos)?;
                compile_expr(&mut context, local, span.expr)?;
            }

            Statement::Call(span) => {
                let key = SymbolKey::from(span.vref.name);
                let temp = context.symtable.alloc_temp(span.vref_pos)?;
                for ArgSpan { expr, sep, sep_pos } in span.args {
                    compile_expr(&mut context, temp, expr.unwrap())?;
                }
                context.symtable.dealloc_temps(1);
                let upcall = context.upcall(key);
                context.emit(bytecode::make_upcall(upcall, temp));
            }

            _ => todo!(),
        }
    }
    context.emit(bytecode::make_leave());
    context.fixups.insert(enter, Fixup::Enter(context.symtable.frame_size()));

    for (addr, fixup) in &context.fixups {
        let instr = match fixup {
            Fixup::Enter(nargs) => bytecode::make_enter(*nargs),
        };
        context.code[*addr] = instr;
    }

    Ok(context.to_image())
}
