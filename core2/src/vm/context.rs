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

//! Virtual processor for EndBASIC execution.

use crate::bytecode::{self, Opcode, Register, opcode_of};
use crate::image::Image;
use crate::mem::{Datum, Pointer};
use crate::num::unchecked_u24_as_usize;

/// Alias for the type representing a program address.
type Address = usize;

/// Internal representation of a `StopReason` that requires further annotation by the caller.
pub(super) enum InternalStopReason {
    /// Execution terminated due to an `END` instruction.
    Eof,

    /// Execution stopped due to an instruction-level exception.
    Exception(Address, String),

    /// Execution stopped due to an upcall that requires service from the caller.
    Upcall(u16, Register),
}

struct Frame {
    old_pc: Address,
    old_fp: usize,
    ret_reg: Option<Register>,
}

/// Execution context for the virtual machine.
///
/// This roughly corresponds to the concept of a "processor", making the VM the container of
/// various objects and the context the representation of the execution.
pub(super) struct Context {
    /// Program counter.
    pc: Address,

    /// Frame pointer.  Contains the offset of the first local register for the current
    /// scope.
    fp: usize,

    /// Stop signal.  If set, indicates why the execution stopped during instruction processing.
    stop: Option<InternalStopReason>,

    /// Register values.  The first N registers hold global variables.  After those, we find
    /// the registers for all local variables and for all scopes.
    regs: Vec<u64>,

    call_stack: Vec<Frame>,
}

impl Default for Context {
    fn default() -> Self {
        Self {
            pc: 0,
            fp: usize::from(Register::MAX_GLOBAL),
            stop: None,
            regs: vec![0; usize::from(Register::MAX_GLOBAL)],
            call_stack: vec![],
        }
    }
}

impl Context {
    /// Gets the value of register `reg`.
    ///
    /// Panics if the register is invalid.
    fn get_reg(&self, reg: Register) -> u64 {
        let (is_global, index) = reg.to_parts();
        let mut index = usize::from(index);
        if !is_global {
            index += self.fp;
        }
        self.regs[index]
    }

    /// Sets the value of register `reg` to `value`.
    ///
    /// Panics if the register is invalid.
    fn set_reg(&mut self, reg: Register, value: u64) {
        let (is_global, index) = reg.to_parts();
        let mut index = usize::from(index);
        if !is_global {
            index += self.fp;
        }
        self.regs[index] = value;
    }

    /// Dereferences a pointer.
    fn deref_ptr<'b>(&self, reg: Register, constants: &'b [Datum], heap: &'b [Datum]) -> &'b Datum {
        let raw_addr = self.get_reg(reg);
        match Pointer::from(raw_addr) {
            Pointer::Constant(index) => {
                let index = unsafe { unchecked_u24_as_usize(index) };
                &constants[index]
            }
            Pointer::Heap(index) => {
                let index = unsafe { unchecked_u24_as_usize(index) };
                &heap[index]
            }
        }
    }

    /// Registers that the instruction being processed threw an exception `message`.
    ///
    /// It's the responsibility of the execution loop to check for the presence of exceptions and
    /// to stop execution if needed.
    fn set_exception<S: Into<String>>(&mut self, message: S) {
        self.stop = Some(InternalStopReason::Exception(self.pc, message.into()));
    }

    // DO NOT SUBMIT: Revisit API.
    pub(super) fn get_local_regs(&self, reg: Register) -> &[u64] {
        let (is_global, index) = reg.to_parts();
        assert!(!is_global);
        let index = usize::from(index);
        let start = self.fp + index;
        &self.regs[start..]
    }

    /// Starts or resumes execution of `image`.
    ///
    /// Panics if the processor state is out of sync with `image` or if the contents of `image`
    /// are invalid.  We assume that the image comes from the result of an in-process compilation
    /// (not stored bytecode) and that the compiler guarantees that the image is valid.
    pub(super) fn exec(&mut self, image: &Image, heap: &mut Vec<Datum>) -> InternalStopReason {
        while self.stop.is_none() {
            let instr = image.code[self.pc];

            let opcode = unsafe { opcode_of(instr) };

            match opcode {
                Opcode::AddInteger => self.do_add_integer(instr),
                Opcode::Alloc => self.do_alloc(instr, heap),
                Opcode::Call => self.do_call(instr),
                Opcode::Concat => self.do_concat(instr, &image.constants, heap),
                Opcode::End => self.do_end(instr),
                Opcode::Enter => self.do_enter(instr),
                Opcode::Gosub => self.do_gosub(instr),
                Opcode::Jump => self.do_jump(instr),
                Opcode::Leave => self.do_leave(instr),
                Opcode::LoadConstant => self.do_load_constant(instr, &image.constants),
                Opcode::LoadInteger => self.do_load_integer(instr),
                Opcode::Move => self.do_move(instr),
                Opcode::Nop => self.do_nop(instr),
                Opcode::Return => self.do_return(instr),
                Opcode::Upcall => self.do_upcall(instr),
            }
        }
        self.stop.take().expect("The loop above can only exit when there is a stop reason")
    }
}

impl Context {
    pub(super) fn do_add_integer(&mut self, instr: u32) {
        let (dest, src1, src2) = bytecode::parse_add_integer(instr);
        let lhs = self.get_reg(src1) as i32;
        let rhs = self.get_reg(src2) as i32;
        match lhs.checked_add(rhs) {
            Some(result) => {
                self.set_reg(dest, result as u64);
                self.pc += 1;
            }
            None => {
                self.set_exception("Integer overflow");
            }
        }
    }

    pub(super) fn do_alloc(&mut self, instr: u32, heap: &mut Vec<Datum>) {
        let (dest, etype) = bytecode::parse_alloc(instr);
        heap.push(Datum::new(etype));
        let ptr = Pointer::for_heap((heap.len() - 1) as u32);
        self.set_reg(dest, ptr);
        self.pc += 1;
    }

    pub(super) fn do_call(&mut self, instr: u32) {
        let (reg, offset) = bytecode::parse_call(instr);
        self.call_stack.push(Frame { old_pc: self.pc, old_fp: self.fp, ret_reg: Some(reg) });
        self.pc += Address::from(offset);
        self.fp = self.regs.len();
    }

    pub(super) fn do_concat(&mut self, instr: u32, constants: &[Datum], heap: &mut Vec<Datum>) {
        let (dest, src1, src2) = bytecode::parse_concat(instr);
        let lhs = self.deref_ptr(src1, constants, heap);
        let rhs = self.deref_ptr(src2, constants, heap);
        let result = match (lhs, rhs) {
            (Datum::Text(lhs), Datum::Text(rhs)) => format!("{}{}", lhs, rhs),
            _ => unreachable!(),
        };
        heap.push(Datum::Text(result));
        let ptr = Pointer::for_heap((heap.len() - 1) as u32);
        self.set_reg(dest, ptr);
        self.pc += 1;
    }

    pub(super) fn do_end(&mut self, instr: u32) {
        bytecode::parse_end(instr);
        self.stop = Some(InternalStopReason::Eof);
    }

    pub(super) fn do_enter(&mut self, instr: u32) {
        let nlocals = bytecode::parse_enter(instr);
        self.regs.resize(self.regs.len() + usize::from(nlocals), 0);
        self.pc += 1;
    }

    pub(super) fn do_gosub(&mut self, instr: u32) {
        let offset = bytecode::parse_gosub(instr);
        self.call_stack.push(Frame { old_pc: self.pc, old_fp: self.fp, ret_reg: None });
        self.pc += Address::from(offset);
    }

    pub(super) fn do_jump(&mut self, instr: u32) {
        let offset = bytecode::parse_jump(instr);
        self.pc += Address::from(offset);
    }

    pub(super) fn do_leave(&mut self, instr: u32) {
        bytecode::parse_leave(instr);
        //self.regs.truncate(self.regs.len() - usize::from(nlocals));
        self.pc += 1;
    }

    pub(super) fn do_load_constant(&mut self, instr: u32, constants: &[Datum]) {
        let (register, i) = bytecode::parse_load_constant(instr);
        match &constants[usize::from(i)] {
            Datum::Boolean(_) => unreachable!("Booleans are always immediates"),
            Datum::Double(d) => self.set_reg(register, d.to_bits()),
            Datum::Integer(i) => self.set_reg(register, *i as u64),
            Datum::Text(_) => unreachable!("Strings cannot be loaded into registers"),
        }
        self.pc += 1;
    }

    pub(super) fn do_load_integer(&mut self, instr: u32) {
        let (register, i) = bytecode::parse_load_integer(instr);
        self.set_reg(register, i as u64);
        self.pc += 1;
    }

    pub(super) fn do_move(&mut self, instr: u32) {
        let (dest, src) = bytecode::parse_move(instr);
        let value = self.get_reg(src);
        self.set_reg(dest, value);
        self.pc += 1;
    }

    pub(super) fn do_nop(&mut self, instr: u32) {
        bytecode::parse_nop(instr);
        self.pc += 1;
    }

    pub(super) fn do_return(&mut self, instr: u32) {
        bytecode::parse_return(instr);
        let frame = match self.call_stack.pop() {
            Some(frame) => frame,
            None => {
                self.set_exception("RETURN without GOSUB or FUNCTION call");
                return;
            }
        };
        if let Some(ret_reg) = frame.ret_reg {
            let return_value = self.get_reg(Register::local(0).unwrap());
            self.pc = frame.old_pc + 1;
            self.fp = frame.old_fp;
            self.set_reg(ret_reg, return_value);
        } else {
            self.pc = frame.old_pc + 1;
            self.fp = frame.old_fp;
        }
    }

    pub(super) fn do_upcall(&mut self, instr: u32) {
        let (index, first_reg) = bytecode::parse_upcall(instr);
        self.stop = Some(InternalStopReason::Upcall(index, first_reg));
        self.pc += 1;
    }
}
