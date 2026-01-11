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

//! Virtual machine for EndBASIC execution.

use crate::bytecode::{self, INSTR_FORMATTERS, Register};
use crate::callable::{Callable, Scope};
use crate::compiler::{Image, SymbolKey};
use std::collections::HashMap;
use std::rc::Rc;

const INSTR_HANDLERS: &[fn(&mut Context, u32)] = &[
    do_nop,
    do_enter,
    do_leave,
    do_upcall,
    do_move,
    do_load_integer,
    do_load_integer_constant,
    do_add_integer,
];

fn do_nop(context: &mut Context, op: u32) {
    bytecode::parse_nop(op);
    context.pc += 1;
}

fn do_enter(context: &mut Context, op: u32) {
    let nlocals = bytecode::parse_enter(op);
    context.regs.resize(context.regs.len() + usize::from(nlocals), 0);
    //context.fp = context.regs.len() - nlocals;
    context.pc += 1;
}

fn do_leave(context: &mut Context, op: u32) {
    bytecode::parse_leave(op);
    // TODO
    context.pc += 1;
}

fn do_upcall(context: &mut Context, op: u32) {
    let (index, nargs) = bytecode::parse_upcall(op);
    context.upcall = Some((index, nargs));
    context.pc += 1;
}

fn do_move(context: &mut Context, op: u32) {
    let (dest, src) = bytecode::parse_move(op);
    let value = context.get_reg(src);
    context.set_reg(dest, value);
    context.pc += 1;
}

fn do_load_integer(context: &mut Context, op: u32) {
    let (register, i) = bytecode::parse_load_integer(op);
    context.set_reg(register, i as u32);
    context.pc += 1;
}

fn do_load_integer_constant(context: &mut Context, op: u32) {
    let (register, index) = bytecode::parse_load_integer_constant(op);
    eprintln!("Load integer constant {} into r{}", index, register);
    context.pc += 1;
}

fn do_add_integer(context: &mut Context, op: u32) {
    let (dest, src1, src2) = bytecode::parse_add_integer(op);
    let lhs = context.get_reg(src1) as i32;
    let rhs = context.get_reg(src2) as i32;
    context.set_reg(dest, (lhs + rhs) as u32);
    context.pc += 1;
}

struct Frame {
    old_pc: usize,
    old_fp: usize,
}

pub struct Context {
    pc: usize,
    fp: usize,
    upcall: Option<(u16, Register)>,
    regs: Vec<u32>,
    //call_stack: Vec<Frame>,
}

impl Default for Context {
    fn default() -> Self {
        Self {
            pc: 0,
            fp: usize::from(Register::MAX_GLOBAL),
            upcall: None,
            regs: vec![0; usize::from(Register::MAX_GLOBAL)],
            //call_stack: vec![],
        }
    }
}

impl Context {
    fn get_reg(&self, reg: Register) -> u32 {
        let (is_global, mut index) = reg.to_parts();
        if !is_global {
            index += self.fp;
        }
        self.regs[index]
    }

    fn set_reg(&mut self, reg: Register, value: u32) {
        let (is_global, mut index) = reg.to_parts();
        if !is_global {
            index += self.fp;
        }
        self.regs[index] = value;
    }

    fn upcall_scope<'a>(&'a self, reg: Register) -> Scope<'a> {
        let (is_global, index) = reg.to_parts();
        assert!(!is_global);
        let start = self.fp + index;
        eprintln!("New scope starts at {}", start);
        Scope { regs: &self.regs[start..] }
    }
}

pub enum StopReason {
    Eof,
    Upcall,
}

fn disasm(code: &[u32]) {
    for instr in code {
        let opcode = ((*instr) >> 24) as usize;
        eprintln!("{}", INSTR_FORMATTERS[opcode](*instr));
    }
}

#[derive(Default)]
pub struct Vm {
    upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>>,
    upcalls: Vec<Rc<dyn Callable>>,
    image: Option<Image>,
}

impl Vm {
    pub fn new(upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>>) -> Self {
        Self { upcalls_by_name, upcalls: vec![], image: None }
    }

    pub fn load(&mut self, image: Image) -> Context {
        disasm(&image.code);
        self.upcalls = image.map_upcalls(&self.upcalls_by_name);
        self.image = Some(image);
        Context::default()
    }

    pub fn exec(&self, context: &mut Context) -> StopReason {
        context.upcall = None;

        let image = self.image.as_ref().unwrap();
        while context.pc < image.code.len() && context.upcall.is_none() {
            let op = image.code[context.pc];
            let opcode = (op >> 24) as usize;
            INSTR_HANDLERS[opcode](context, op);
        }

        if context.upcall.is_some() { StopReason::Upcall } else { StopReason::Eof }
    }

    pub async fn handle_upcall(&self, context: &mut Context) {
        let (index, nargs) = context.upcall.unwrap();
        eprintln!("Invoking upcall {} with nargs {}", index, nargs);
        self.upcalls[usize::from(index)].exec(context.upcall_scope(nargs)).await
    }
}
