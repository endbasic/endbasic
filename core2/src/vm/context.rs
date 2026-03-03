// EndBASIC
// Copyright 2026 Julio Merino
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

//! Virtual processor for EndBASIC execution.

use crate::ExprType;
use crate::Scope;
use crate::bytecode::{self, ErrorHandlerMode, Opcode, Register, TaggedRegisterRef, opcode_of};
use crate::image::Image;
use crate::mem::{ArrayData, ConstantDatum, DatumPtr, HeapDatum};
use crate::num::unchecked_usize_as_u8;
use crate::reader::LineCol;

/// Alias for the type representing a program address.
type Address = usize;

/// Internal representation of a `StopReason` that requires further annotation by the caller.
pub(super) enum InternalStopReason {
    /// Execution terminated due to an `END` instruction.
    End(i32),

    /// Execution stopped due to an instruction-level exception.
    Exception(Address, String),

    /// Execution stopped due to an upcall that requires service from the caller.
    ///
    /// The fields are: upcall index, first argument register, and the PC of the UPCALL instruction.
    Upcall(u16, Register, Address),
}

/// Error handler configuration set by `ON ERROR`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ErrorHandler {
    /// Errors are not handled.
    None,

    /// Errors resume execution at the next statement.
    ResumeNext,

    /// Errors jump to a handler address.
    Jump(Address),
}

/// Represents a call frame in the stack.
struct Frame {
    /// Program counter of the instruction that caused the call.
    old_pc: Address,

    /// Frame pointer of the previous frame.
    old_fp: usize,

    /// Register to store the return value of the call, if any.
    ret_reg: Option<Register>,
}

/// Custom implementation of checked integer additions for error reporting purposes.
#[inline(always)]
fn checked_add_integer(lhs: i32, rhs: i32) -> Result<i32, &'static str> {
    lhs.checked_add(rhs).ok_or("Integer overflow")
}

/// Custom implementation of checked bitwise AND for error reporting purposes.
#[inline(always)]
fn checked_and_integer(lhs: i32, rhs: i32) -> Result<i32, &'static str> {
    Ok(lhs & rhs)
}

/// Custom implementation of checked integer divisions for error reporting purposes.
#[inline(always)]
fn checked_div_integer(lhs: i32, rhs: i32) -> Result<i32, &'static str> {
    if rhs == 0 { Err("Division by zero") } else { lhs.checked_div(rhs).ok_or("Integer underflow") }
}

/// Custom implementation of checked integer modulos for error reporting purposes.
#[inline(always)]
fn checked_mod_integer(lhs: i32, rhs: i32) -> Result<i32, &'static str> {
    if rhs == 0 { Err("Modulo by zero") } else { lhs.checked_rem(rhs).ok_or("Integer underflow") }
}

/// Custom implementation of checked integer multiplications for error reporting purposes.
#[inline(always)]
fn checked_mul_integer(lhs: i32, rhs: i32) -> Result<i32, &'static str> {
    lhs.checked_mul(rhs).ok_or("Integer overflow")
}

/// Custom implementation of checked bitwise OR for error reporting purposes.
#[inline(always)]
fn checked_or_integer(lhs: i32, rhs: i32) -> Result<i32, &'static str> {
    Ok(lhs | rhs)
}

/// Custom implementation of checked integer powers for error reporting purposes.
#[inline(always)]
fn checked_pow_integer(lhs: i32, exp: u32) -> Result<i32, &'static str> {
    lhs.checked_pow(exp).ok_or("Integer overflow")
}

/// Custom implementation of checked left shift for error reporting purposes.
#[inline(always)]
fn checked_shl_integer(lhs: i32, rhs: i32) -> Result<i32, String> {
    match u32::try_from(rhs) {
        Err(_) => Err(format!("Number of bits to << ({}) must be positive", rhs)),
        Ok(bits) => Ok(lhs.checked_shl(bits).unwrap_or(0)),
    }
}

/// Custom implementation of checked right shift for error reporting purposes.
#[inline(always)]
fn checked_shr_integer(lhs: i32, rhs: i32) -> Result<i32, String> {
    match u32::try_from(rhs) {
        Err(_) => Err(format!("Number of bits to >> ({}) must be positive", rhs)),
        Ok(bits) => Ok(match lhs.checked_shr(bits) {
            Some(i) => i,
            None if lhs < 0 => -1,
            None => 0,
        }),
    }
}
/// Custom implementation of checked integer subtractions for error reporting purposes.
#[inline(always)]
fn checked_sub_integer(lhs: i32, rhs: i32) -> Result<i32, &'static str> {
    lhs.checked_sub(rhs).ok_or("Integer underflow")
}

/// Custom implementation of checked bitwise XOR for error reporting purposes.
#[inline(always)]
fn checked_xor_integer(lhs: i32, rhs: i32) -> Result<i32, &'static str> {
    Ok(lhs ^ rhs)
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

    /// Current error handler configuration.
    err_handler: ErrorHandler,

    /// Register values.  The first N registers hold global variables.  After those, we find
    /// the registers for all local variables and for all scopes.
    regs: Vec<u64>,

    /// Stack of call frames for tracking subroutine and function calls.
    call_stack: Vec<Frame>,
}

impl Default for Context {
    fn default() -> Self {
        Self {
            pc: 0,
            fp: usize::from(Register::MAX_GLOBAL),
            stop: None,
            err_handler: ErrorHandler::None,
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

    /// Sets the program counter to `pc`.
    pub(super) fn set_pc(&mut self, pc: Address) {
        self.pc = pc;
    }

    /// Returns the current error handler configuration.
    pub(super) fn error_handler(&self) -> ErrorHandler {
        self.err_handler
    }

    /// Dereferences a pointer register as a string.
    fn deref_string<'b>(
        &self,
        reg: Register,
        constants: &'b [ConstantDatum],
        heap: &'b [HeapDatum],
    ) -> &'b str {
        let raw_addr = self.get_reg(reg);
        DatumPtr::from(raw_addr).resolve_string(constants, heap)
    }

    /// Returns the raw `u64` value stored in global register `index`.
    ///
    /// Used by the VM's `get_global_*` methods to read global variable values after execution.
    pub(super) fn get_global_reg_raw(&self, index: u8) -> u64 {
        self.regs[usize::from(index)]
    }

    /// Resolves array subscripts and computes the flat index for `arr_reg` with subscripts read
    /// from registers starting at `first_sub_reg`.
    ///
    /// Returns `Some((heap_idx, flat_idx))` on success, or `None` if an exception was set.
    fn resolve_array_index(
        &mut self,
        arr_reg: Register,
        first_sub_reg: Register,
        heap: &[HeapDatum],
    ) -> Option<(usize, usize)> {
        let arr_ptr = DatumPtr::from(self.get_reg(arr_reg));
        let heap_idx = arr_ptr.heap_index();
        let array = match &heap[heap_idx] {
            HeapDatum::Array(a) => a,
            _ => unreachable!("Register must point to an array"),
        };

        let ndims = array.dimensions.len();
        let (_, first_idx) = first_sub_reg.to_parts();
        let mut subscripts = Vec::with_capacity(ndims);
        for i in 0..unchecked_usize_as_u8(ndims) {
            let sub_reg = Register::local(first_idx + i).unwrap();
            subscripts.push(self.get_reg(sub_reg) as i32);
        }

        match array.flat_index(&subscripts) {
            Ok(flat_idx) => Some((heap_idx, flat_idx)),
            Err(e) => {
                self.set_exception(e);
                None
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

    /// Constructs a `Scope` for an upcall with arguments starting at `reg`.
    pub(super) fn upcall_scope<'a>(
        &'a mut self,
        reg: Register,
        constants: &'a [ConstantDatum],
        heap: &'a mut Vec<HeapDatum>,
        arg_linecols: &'a [LineCol],
        last_error: &'a Option<String>,
        data: &'a [Option<ConstantDatum>],
    ) -> Scope<'a> {
        let (is_global, index) = reg.to_parts();
        assert!(!is_global);
        let index = usize::from(index);

        Scope {
            regs: &mut self.regs,
            constants,
            heap,
            fp: self.fp + index,
            arg_linecols,
            last_error,
            data,
        }
    }

    /// Starts or resumes execution of `image`.
    ///
    /// Panics if the processor state is out of sync with `image` or if the contents of `image`
    /// are invalid.  We assume that the image comes from the result of an in-process compilation
    /// (not stored bytecode) and that the compiler guarantees that the image is valid.
    pub(super) fn exec(&mut self, image: &Image, heap: &mut Vec<HeapDatum>) -> InternalStopReason {
        while self.stop.is_none() {
            let instr = image.code[self.pc];

            match opcode_of(instr) {
                Opcode::AddDouble => self.do_add_double(instr),
                Opcode::AddInteger => self.do_add_integer(instr),
                Opcode::Alloc => self.do_alloc(instr, heap),
                Opcode::AllocArray => self.do_alloc_array(instr, heap),
                Opcode::BitwiseAnd => self.do_bitwise_and(instr),
                Opcode::BitwiseNot => self.do_bitwise_not(instr),
                Opcode::BitwiseOr => self.do_bitwise_or(instr),
                Opcode::BitwiseXor => self.do_bitwise_xor(instr),
                Opcode::Call => self.do_call(instr),
                Opcode::Concat => self.do_concat(instr, &image.constants, heap),
                Opcode::DivideDouble => self.do_divide_double(instr),
                Opcode::DivideInteger => self.do_divide_integer(instr),
                Opcode::DoubleToInteger => self.do_double_to_integer(instr),
                Opcode::EqualBoolean => self.do_equal_boolean(instr),
                Opcode::EqualDouble => self.do_equal_double(instr),
                Opcode::EqualInteger => self.do_equal_integer(instr),
                Opcode::EqualText => self.do_equal_text(instr, &image.constants, heap),
                Opcode::End => self.do_end(instr),
                Opcode::Enter => self.do_enter(instr),
                Opcode::Gosub => self.do_gosub(instr),
                Opcode::GreaterDouble => self.do_greater_double(instr),
                Opcode::GreaterEqualDouble => self.do_greater_equal_double(instr),
                Opcode::GreaterEqualInteger => self.do_greater_equal_integer(instr),
                Opcode::GreaterEqualText => {
                    self.do_greater_equal_text(instr, &image.constants, heap)
                }
                Opcode::GreaterInteger => self.do_greater_integer(instr),
                Opcode::GreaterText => self.do_greater_text(instr, &image.constants, heap),
                Opcode::IntegerToDouble => self.do_integer_to_double(instr),
                Opcode::Jump => self.do_jump(instr),
                Opcode::JumpIfFalse => self.do_jump_if_false(instr),
                Opcode::Leave => self.do_leave(instr),
                Opcode::LessDouble => self.do_less_double(instr),
                Opcode::LessEqualDouble => self.do_less_equal_double(instr),
                Opcode::LessEqualInteger => self.do_less_equal_integer(instr),
                Opcode::LessEqualText => self.do_less_equal_text(instr, &image.constants, heap),
                Opcode::LessInteger => self.do_less_integer(instr),
                Opcode::LessText => self.do_less_text(instr, &image.constants, heap),
                Opcode::LoadArray => self.do_load_array(instr, heap),
                Opcode::LoadConstant => self.do_load_constant(instr, &image.constants),
                Opcode::LoadInteger => self.do_load_integer(instr),
                Opcode::LoadRegisterPointer => self.do_load_register_ptr(instr),
                Opcode::ModuloDouble => self.do_modulo_double(instr),
                Opcode::ModuloInteger => self.do_modulo_integer(instr),
                Opcode::Move => self.do_move(instr),
                Opcode::MultiplyDouble => self.do_multiply_double(instr),
                Opcode::MultiplyInteger => self.do_multiply_integer(instr),
                Opcode::NegateDouble => self.do_negate_double(instr),
                Opcode::NegateInteger => self.do_negate_integer(instr),
                Opcode::NotEqualBoolean => self.do_not_equal_boolean(instr),
                Opcode::NotEqualDouble => self.do_not_equal_double(instr),
                Opcode::NotEqualInteger => self.do_not_equal_integer(instr),
                Opcode::NotEqualText => self.do_not_equal_text(instr, &image.constants, heap),
                Opcode::Nop => self.do_nop(instr),
                Opcode::PowerDouble => self.do_power_double(instr),
                Opcode::PowerInteger => self.do_power_integer(instr),
                Opcode::Return => self.do_return(instr),
                Opcode::SetErrorHandler => self.do_set_error_handler(instr),
                Opcode::ShiftLeft => self.do_shift_left(instr),
                Opcode::ShiftRight => self.do_shift_right(instr),
                Opcode::StoreArray => self.do_store_array(instr, heap),
                Opcode::SubtractDouble => self.do_subtract_double(instr),
                Opcode::SubtractInteger => self.do_subtract_integer(instr),
                Opcode::Upcall => self.do_upcall(instr),
            }
        }
        self.stop.take().expect("The loop above can only exit when there is a stop reason")
    }
}

impl Context {
    /// Applies a binary double operation using `parse` to decode the instruction and `op` to
    /// compute the result.
    fn do_binary_double_op<F>(
        &mut self,
        instr: u32,
        parse: fn(u32) -> (Register, Register, Register),
        op: F,
    ) where
        F: Fn(f64, f64) -> f64,
    {
        let (dest, src1, src2) = parse(instr);
        let lhs = f64::from_bits(self.get_reg(src1));
        let rhs = f64::from_bits(self.get_reg(src2));
        self.set_reg(dest, op(lhs, rhs).to_bits());
        self.pc += 1;
    }

    /// Applies a binary double predicate using `parse` to decode the instruction and `op` to
    /// compute the result.
    fn do_binary_double_predicate_op<F>(
        &mut self,
        instr: u32,
        parse: fn(u32) -> (Register, Register, Register),
        op: F,
    ) where
        F: Fn(f64, f64) -> bool,
    {
        let (dest, src1, src2) = parse(instr);
        let lhs = f64::from_bits(self.get_reg(src1));
        let rhs = f64::from_bits(self.get_reg(src2));
        self.set_reg(dest, if op(lhs, rhs) { 1 } else { 0 });
        self.pc += 1;
    }

    /// Applies a binary integer operation using `parse` to decode the instruction and `op` to
    /// compute the result.  `op` returns `Err` with a message on failure.
    fn do_binary_integer_op<F, E>(
        &mut self,
        instr: u32,
        parse: fn(u32) -> (Register, Register, Register),
        op: F,
    ) where
        F: Fn(i32, i32) -> Result<i32, E>,
        E: ToString,
    {
        let (dest, src1, src2) = parse(instr);
        let lhs = self.get_reg(src1) as i32;
        let rhs = self.get_reg(src2) as i32;
        match op(lhs, rhs) {
            Ok(result) => {
                self.set_reg(dest, result as u64);
                self.pc += 1;
            }
            Err(msg) => {
                self.set_exception(msg.to_string());
            }
        }
    }

    /// Applies a binary integer predicate using `parse` to decode the instruction and `op` to
    /// compute the result.
    fn do_binary_integer_predicate_op<F>(
        &mut self,
        instr: u32,
        parse: fn(u32) -> (Register, Register, Register),
        op: F,
    ) where
        F: Fn(i32, i32) -> bool,
    {
        let (dest, src1, src2) = parse(instr);
        let lhs = self.get_reg(src1) as i32;
        let rhs = self.get_reg(src2) as i32;
        self.set_reg(dest, if op(lhs, rhs) { 1 } else { 0 });
        self.pc += 1;
    }

    /// Applies a binary boolean operation using `parse` to decode the instruction and `op` to
    /// compute the result.
    fn do_binary_boolean_op<F>(
        &mut self,
        instr: u32,
        parse: fn(u32) -> (Register, Register, Register),
        op: F,
    ) where
        F: Fn(bool, bool) -> bool,
    {
        let (dest, src1, src2) = parse(instr);
        let lhs = self.get_reg(src1) != 0;
        let rhs = self.get_reg(src2) != 0;
        self.set_reg(dest, if op(lhs, rhs) { 1 } else { 0 });
        self.pc += 1;
    }

    /// Applies a binary text operation using `parse` to decode the instruction and `op` to
    /// compute the result.
    fn do_binary_text_op<F>(
        &mut self,
        instr: u32,
        constants: &[ConstantDatum],
        heap: &[HeapDatum],
        parse: fn(u32) -> (Register, Register, Register),
        op: F,
    ) where
        F: Fn(&str, &str) -> bool,
    {
        let (dest, src1, src2) = parse(instr);
        let lhs = self.deref_string(src1, constants, heap);
        let rhs = self.deref_string(src2, constants, heap);
        self.set_reg(dest, if op(lhs, rhs) { 1 } else { 0 });
        self.pc += 1;
    }

    /// Implements the `AddDouble` opcode.
    pub(super) fn do_add_double(&mut self, instr: u32) {
        self.do_binary_double_op(instr, bytecode::parse_add_double, |l, r| l + r);
    }

    /// Implements the `AddInteger` opcode.
    pub(super) fn do_add_integer(&mut self, instr: u32) {
        self.do_binary_integer_op(instr, bytecode::parse_add_integer, checked_add_integer);
    }

    /// Implements the `Alloc` opcode.
    pub(super) fn do_alloc(&mut self, instr: u32, heap: &mut Vec<HeapDatum>) {
        let (dest, etype) = bytecode::parse_alloc(instr);
        debug_assert_eq!(ExprType::Text, etype, "Alloc is only emitted for strings right now");
        heap.push(HeapDatum::Text(String::new()));
        let ptr = DatumPtr::for_heap((heap.len() - 1) as u32);
        self.set_reg(dest, ptr);
        self.pc += 1;
    }

    /// Implements the `AllocArray` opcode.
    pub(super) fn do_alloc_array(&mut self, instr: u32, heap: &mut Vec<HeapDatum>) {
        let (dest, packed, first_dim_reg) = bytecode::parse_alloc_array(instr);
        let subtype = packed.subtype();
        let ndims = usize::from(packed.ndims());

        let (_, first_idx) = first_dim_reg.to_parts();
        let mut dimensions = Vec::with_capacity(ndims);
        let mut total: usize = 1;
        for i in 0..ndims {
            let dim_reg = Register::local(first_idx + i as u8).unwrap();
            let dim = match usize::try_from(self.get_reg(dim_reg) as i32) {
                Ok(0) | Err(_) => {
                    self.set_exception(format!("Dimension {} must be positive", i));
                    return;
                }
                Ok(n) => n,
            };
            dimensions.push(dim);
            total *= dim;
        }

        let values = match subtype {
            ExprType::Boolean | ExprType::Double | ExprType::Integer => {
                vec![0; total]
            }
            ExprType::Text => {
                let mut values = Vec::with_capacity(total);
                for _ in 0..total {
                    heap.push(HeapDatum::Text(String::new()));
                    values.push(DatumPtr::for_heap((heap.len() - 1) as u32));
                }
                values
            }
        };
        let array = ArrayData { dimensions, values };
        heap.push(HeapDatum::Array(array));
        let ptr = DatumPtr::for_heap((heap.len() - 1) as u32);
        self.set_reg(dest, ptr);
        self.pc += 1;
    }

    /// Implements the `BitwiseAnd` opcode.
    pub(super) fn do_bitwise_and(&mut self, instr: u32) {
        self.do_binary_integer_op(instr, bytecode::parse_bitwise_and, checked_and_integer);
    }

    /// Implements the `BitwiseNot` opcode.
    pub(super) fn do_bitwise_not(&mut self, instr: u32) {
        let reg = bytecode::parse_bitwise_not(instr);
        let value = self.get_reg(reg) as i32;
        self.set_reg(reg, (!value) as u64);
        self.pc += 1;
    }

    /// Implements the `BitwiseOr` opcode.
    pub(super) fn do_bitwise_or(&mut self, instr: u32) {
        self.do_binary_integer_op(instr, bytecode::parse_bitwise_or, checked_or_integer);
    }

    /// Implements the `BitwiseXor` opcode.
    pub(super) fn do_bitwise_xor(&mut self, instr: u32) {
        self.do_binary_integer_op(instr, bytecode::parse_bitwise_xor, checked_xor_integer);
    }

    /// Implements the `Call` opcode.
    pub(super) fn do_call(&mut self, instr: u32) {
        let (reg, offset) = bytecode::parse_call(instr);
        self.call_stack.push(Frame { old_pc: self.pc, old_fp: self.fp, ret_reg: Some(reg) });
        self.pc = Address::from(offset);
        let (is_global, index) = reg.to_parts();
        debug_assert!(!is_global, "Function results are always stored to a temp register");
        self.fp += usize::from(index);
    }

    /// Implements the `Concat` opcode.
    pub(super) fn do_concat(
        &mut self,
        instr: u32,
        constants: &[ConstantDatum],
        heap: &mut Vec<HeapDatum>,
    ) {
        let (dest, src1, src2) = bytecode::parse_concat(instr);
        let lhs = self.deref_string(src1, constants, heap).to_owned();
        let rhs = self.deref_string(src2, constants, heap);
        let result = lhs + rhs;
        heap.push(HeapDatum::Text(result));
        let ptr = DatumPtr::for_heap((heap.len() - 1) as u32);
        self.set_reg(dest, ptr);
        self.pc += 1;
    }

    /// Implements the `DivideDouble` opcode.
    pub(super) fn do_divide_double(&mut self, instr: u32) {
        self.do_binary_double_op(instr, bytecode::parse_divide_double, |l, r| l / r);
    }

    /// Implements the `DivideInteger` opcode.
    pub(super) fn do_divide_integer(&mut self, instr: u32) {
        self.do_binary_integer_op(instr, bytecode::parse_divide_integer, checked_div_integer);
    }

    /// Implements the `DoubleToInteger` opcode.
    pub(super) fn do_double_to_integer(&mut self, instr: u32) {
        let reg = bytecode::parse_double_to_integer(instr);
        let dvalue = f64::from_bits(self.get_reg(reg));
        self.set_reg(reg, dvalue.round() as u64);
        self.pc += 1;
    }

    /// Implements the `EqualBoolean` opcode.
    pub(super) fn do_equal_boolean(&mut self, instr: u32) {
        self.do_binary_boolean_op(instr, bytecode::parse_equal_boolean, |l, r| l == r);
    }

    /// Implements the `EqualDouble` opcode.
    pub(super) fn do_equal_double(&mut self, instr: u32) {
        self.do_binary_double_predicate_op(instr, bytecode::parse_equal_double, |l, r| l == r);
    }

    /// Implements the `EqualInteger` opcode.
    pub(super) fn do_equal_integer(&mut self, instr: u32) {
        self.do_binary_integer_predicate_op(instr, bytecode::parse_equal_integer, |l, r| l == r);
    }

    /// Implements the `EqualText` opcode.
    pub(super) fn do_equal_text(
        &mut self,
        instr: u32,
        constants: &[ConstantDatum],
        heap: &[HeapDatum],
    ) {
        self.do_binary_text_op(instr, constants, heap, bytecode::parse_equal_text, |l, r| l == r);
    }

    /// Implements the `End` opcode.
    pub(super) fn do_end(&mut self, instr: u32) {
        let reg = bytecode::parse_end(instr);
        let code = self.get_reg(reg) as i32;
        self.stop = Some(InternalStopReason::End(code));
    }

    /// Implements the `Enter` opcode.
    pub(super) fn do_enter(&mut self, instr: u32) {
        let nlocals = bytecode::parse_enter(instr);
        self.regs.resize(self.regs.len() + usize::from(nlocals), 0);
        self.pc += 1;
    }

    /// Implements the `Gosub` opcode.
    pub(super) fn do_gosub(&mut self, instr: u32) {
        let offset = bytecode::parse_gosub(instr);
        self.call_stack.push(Frame { old_pc: self.pc, old_fp: self.fp, ret_reg: None });
        self.pc = Address::from(offset);
    }

    /// Implements the `GreaterDouble` opcode.
    pub(super) fn do_greater_double(&mut self, instr: u32) {
        self.do_binary_double_predicate_op(instr, bytecode::parse_greater_double, |l, r| l > r);
    }

    /// Implements the `GreaterEqualDouble` opcode.
    pub(super) fn do_greater_equal_double(&mut self, instr: u32) {
        self.do_binary_double_predicate_op(instr, bytecode::parse_greater_equal_double, |l, r| {
            l >= r
        });
    }

    /// Implements the `GreaterEqualInteger` opcode.
    pub(super) fn do_greater_equal_integer(&mut self, instr: u32) {
        self.do_binary_integer_predicate_op(
            instr,
            bytecode::parse_greater_equal_integer,
            |l, r| l >= r,
        );
    }

    /// Implements the `GreaterEqualText` opcode.
    pub(super) fn do_greater_equal_text(
        &mut self,
        instr: u32,
        constants: &[ConstantDatum],
        heap: &[HeapDatum],
    ) {
        self.do_binary_text_op(
            instr,
            constants,
            heap,
            bytecode::parse_greater_equal_text,
            |l, r| l >= r,
        );
    }

    /// Implements the `GreaterInteger` opcode.
    pub(super) fn do_greater_integer(&mut self, instr: u32) {
        self.do_binary_integer_predicate_op(instr, bytecode::parse_greater_integer, |l, r| l > r);
    }

    /// Implements the `GreaterText` opcode.
    pub(super) fn do_greater_text(
        &mut self,
        instr: u32,
        constants: &[ConstantDatum],
        heap: &[HeapDatum],
    ) {
        self.do_binary_text_op(instr, constants, heap, bytecode::parse_greater_text, |l, r| l > r);
    }

    /// Implements the `IntegerToDouble` opcode.
    pub(super) fn do_integer_to_double(&mut self, instr: u32) {
        let reg = bytecode::parse_integer_to_double(instr);
        let ivalue = self.get_reg(reg) as i32;
        self.set_reg(reg, (ivalue as f64).to_bits());
        self.pc += 1;
    }

    /// Implements the `Jump` opcode.
    pub(super) fn do_jump(&mut self, instr: u32) {
        let offset = bytecode::parse_jump(instr);
        self.pc = Address::from(offset);
    }

    /// Implements the `JumpIfFalse` opcode.
    pub(super) fn do_jump_if_false(&mut self, instr: u32) {
        let (cond_reg, target) = bytecode::parse_jump_if_false(instr);
        if self.get_reg(cond_reg) != 0 {
            self.pc += 1;
        } else {
            self.pc = Address::from(target);
        }
    }

    /// Implements the `Leave` opcode.
    pub(super) fn do_leave(&mut self, instr: u32) {
        bytecode::parse_leave(instr);
        self.regs.truncate(self.fp);
        self.pc += 1;
    }

    /// Implements the `LessDouble` opcode.
    pub(super) fn do_less_double(&mut self, instr: u32) {
        self.do_binary_double_predicate_op(instr, bytecode::parse_less_double, |l, r| l < r);
    }

    /// Implements the `LessEqualDouble` opcode.
    pub(super) fn do_less_equal_double(&mut self, instr: u32) {
        self.do_binary_double_predicate_op(instr, bytecode::parse_less_equal_double, |l, r| l <= r);
    }

    /// Implements the `LessEqualInteger` opcode.
    pub(super) fn do_less_equal_integer(&mut self, instr: u32) {
        self.do_binary_integer_predicate_op(instr, bytecode::parse_less_equal_integer, |l, r| {
            l <= r
        });
    }

    /// Implements the `LessEqualText` opcode.
    pub(super) fn do_less_equal_text(
        &mut self,
        instr: u32,
        constants: &[ConstantDatum],
        heap: &[HeapDatum],
    ) {
        self.do_binary_text_op(instr, constants, heap, bytecode::parse_less_equal_text, |l, r| {
            l <= r
        });
    }

    /// Implements the `LessInteger` opcode.
    pub(super) fn do_less_integer(&mut self, instr: u32) {
        self.do_binary_integer_predicate_op(instr, bytecode::parse_less_integer, |l, r| l < r);
    }

    /// Implements the `LessText` opcode.
    pub(super) fn do_less_text(
        &mut self,
        instr: u32,
        constants: &[ConstantDatum],
        heap: &[HeapDatum],
    ) {
        self.do_binary_text_op(instr, constants, heap, bytecode::parse_less_text, |l, r| l < r);
    }

    /// Implements the `LoadArray` opcode.
    pub(super) fn do_load_array(&mut self, instr: u32, heap: &[HeapDatum]) {
        let (dest, arr_reg, first_sub_reg) = bytecode::parse_load_array(instr);

        if let Some((heap_idx, flat_idx)) = self.resolve_array_index(arr_reg, first_sub_reg, heap) {
            let array = match &heap[heap_idx] {
                HeapDatum::Array(a) => a,
                _ => unreachable!("Register must point to an array"),
            };
            self.set_reg(dest, array.values[flat_idx]);
            self.pc += 1;
        }
    }

    /// Implements the `LoadConstant` opcode.
    pub(super) fn do_load_constant(&mut self, instr: u32, constants: &[ConstantDatum]) {
        let (register, i) = bytecode::parse_load_constant(instr);
        match &constants[usize::from(i)] {
            ConstantDatum::Boolean(_) => unreachable!("Booleans are always immediates"),
            ConstantDatum::Double(d) => self.set_reg(register, d.to_bits()),
            ConstantDatum::Integer(i) => self.set_reg(register, *i as u64),
            ConstantDatum::Text(_) => unreachable!("Strings cannot be loaded into registers"),
        }
        self.pc += 1;
    }

    /// Implements the `LoadInteger` opcode.
    pub(super) fn do_load_integer(&mut self, instr: u32) {
        let (register, i) = bytecode::parse_load_integer(instr);
        self.set_reg(register, i as u64);
        self.pc += 1;
    }

    /// Implements the `LoadRegisterPointer` opcode.
    pub(super) fn do_load_register_ptr(&mut self, instr: u32) {
        let (dest, vtype, src) = bytecode::parse_load_register_ptr(instr);
        let tagged_ref = TaggedRegisterRef::new(src, self.fp, vtype);
        self.set_reg(dest, tagged_ref.as_u64());
        self.pc += 1;
    }

    /// Implements the `ModuloDouble` opcode.
    pub(super) fn do_modulo_double(&mut self, instr: u32) {
        self.do_binary_double_op(instr, bytecode::parse_modulo_double, |l, r| l % r);
    }

    /// Implements the `ModuloInteger` opcode.
    pub(super) fn do_modulo_integer(&mut self, instr: u32) {
        self.do_binary_integer_op(instr, bytecode::parse_modulo_integer, checked_mod_integer);
    }

    /// Implements the `Move` opcode.
    pub(super) fn do_move(&mut self, instr: u32) {
        let (dest, src) = bytecode::parse_move(instr);
        let value = self.get_reg(src);
        self.set_reg(dest, value);
        self.pc += 1;
    }

    /// Implements the `MultiplyDouble` opcode.
    pub(super) fn do_multiply_double(&mut self, instr: u32) {
        self.do_binary_double_op(instr, bytecode::parse_multiply_double, |l, r| l * r);
    }

    /// Implements the `MultiplyInteger` opcode.
    pub(super) fn do_multiply_integer(&mut self, instr: u32) {
        self.do_binary_integer_op(instr, bytecode::parse_multiply_integer, checked_mul_integer);
    }

    /// Implements the `NegateDouble` opcode.
    pub(super) fn do_negate_double(&mut self, instr: u32) {
        let reg = bytecode::parse_negate_double(instr);
        let value = f64::from_bits(self.get_reg(reg));
        self.set_reg(reg, (-value).to_bits());
        self.pc += 1;
    }

    /// Implements the `NegateInteger` opcode.
    pub(super) fn do_negate_integer(&mut self, instr: u32) {
        let reg = bytecode::parse_negate_integer(instr);
        let value = self.get_reg(reg) as i32;
        match value.checked_neg() {
            Some(result) => {
                self.set_reg(reg, result as u64);
                self.pc += 1;
            }
            None => {
                self.set_exception("Integer overflow");
            }
        }
    }

    /// Implements the `NotEqualBoolean` opcode.
    pub(super) fn do_not_equal_boolean(&mut self, instr: u32) {
        self.do_binary_boolean_op(instr, bytecode::parse_not_equal_boolean, |l, r| l != r);
    }

    /// Implements the `NotEqualDouble` opcode.
    pub(super) fn do_not_equal_double(&mut self, instr: u32) {
        self.do_binary_double_predicate_op(instr, bytecode::parse_not_equal_double, |l, r| l != r);
    }

    /// Implements the `NotEqualInteger` opcode.
    pub(super) fn do_not_equal_integer(&mut self, instr: u32) {
        self.do_binary_integer_predicate_op(instr, bytecode::parse_not_equal_integer, |l, r| {
            l != r
        });
    }

    /// Implements the `NotEqualText` opcode.
    pub(super) fn do_not_equal_text(
        &mut self,
        instr: u32,
        constants: &[ConstantDatum],
        heap: &[HeapDatum],
    ) {
        self.do_binary_text_op(instr, constants, heap, bytecode::parse_not_equal_text, |l, r| {
            l != r
        });
    }

    /// Implements the `Nop` opcode.
    pub(super) fn do_nop(&mut self, instr: u32) {
        bytecode::parse_nop(instr);
        self.pc += 1;
    }

    /// Implements the `PowerDouble` opcode.
    pub(super) fn do_power_double(&mut self, instr: u32) {
        self.do_binary_double_op(instr, bytecode::parse_power_double, |l, r| l.powf(r));
    }

    /// Implements the `PowerInteger` opcode.
    pub(super) fn do_power_integer(&mut self, instr: u32) {
        let (dest, src1, src2) = bytecode::parse_power_integer(instr);
        let lhs = self.get_reg(src1) as i32;
        let rhs = self.get_reg(src2) as i32;
        let exp = match u32::try_from(rhs) {
            Ok(exp) => exp,
            Err(_) => {
                self.set_exception(format!("Exponent {} cannot be negative", rhs));
                return;
            }
        };
        match checked_pow_integer(lhs, exp) {
            Ok(result) => {
                self.set_reg(dest, result as u64);
                self.pc += 1;
            }
            Err(msg) => {
                self.set_exception(msg);
            }
        }
    }

    /// Implements the `Return` opcode.
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

    /// Implements the `SetErrorHandler` opcode.
    pub(super) fn do_set_error_handler(&mut self, instr: u32) {
        let (mode, target) = bytecode::parse_set_error_handler(instr);
        self.err_handler = match mode {
            ErrorHandlerMode::None => ErrorHandler::None,
            ErrorHandlerMode::ResumeNext => ErrorHandler::ResumeNext,
            ErrorHandlerMode::Jump => ErrorHandler::Jump(usize::from(target)),
        };
        self.pc += 1;
    }

    /// Implements the `ShiftLeft` opcode.
    pub(super) fn do_shift_left(&mut self, instr: u32) {
        self.do_binary_integer_op(instr, bytecode::parse_shift_left, checked_shl_integer);
    }

    /// Implements the `ShiftRight` opcode.
    pub(super) fn do_shift_right(&mut self, instr: u32) {
        self.do_binary_integer_op(instr, bytecode::parse_shift_right, checked_shr_integer);
    }

    /// Implements the `StoreArray` opcode.
    pub(super) fn do_store_array(&mut self, instr: u32, heap: &mut [HeapDatum]) {
        let (arr_reg, val_reg, first_sub_reg) = bytecode::parse_store_array(instr);

        let value = self.get_reg(val_reg);
        if let Some((heap_idx, flat_idx)) = self.resolve_array_index(arr_reg, first_sub_reg, heap) {
            let array = match &mut heap[heap_idx] {
                HeapDatum::Array(a) => a,
                _ => unreachable!("Register must point to an array"),
            };
            array.values[flat_idx] = value;
            self.pc += 1;
        }
    }

    /// Implements the `SubtractDouble` opcode.
    pub(super) fn do_subtract_double(&mut self, instr: u32) {
        self.do_binary_double_op(instr, bytecode::parse_subtract_double, |l, r| l - r);
    }

    /// Implements the `SubtractInteger` opcode.
    pub(super) fn do_subtract_integer(&mut self, instr: u32) {
        self.do_binary_integer_op(instr, bytecode::parse_subtract_integer, checked_sub_integer);
    }

    /// Implements the `Upcall` opcode.
    pub(super) fn do_upcall(&mut self, instr: u32) {
        let (index, first_reg) = bytecode::parse_upcall(instr);
        let upcall_pc = self.pc;
        self.pc += 1;
        self.stop = Some(InternalStopReason::Upcall(index, first_reg, upcall_pc));
    }
}
