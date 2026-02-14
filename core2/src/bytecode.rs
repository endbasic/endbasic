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

//! Bytecode for a compiled EndBASIC program.

use crate::ast::{ArgSep, ExprType};
use crate::num::{
    unchecked_u32_as_u8, unchecked_u32_as_u16, unchecked_u32_as_usize, unchecked_u64_as_u8,
};
use std::convert::TryFrom;
use std::fmt;

/// Representation of the various register scopes.
#[derive(Debug)]
pub enum RegisterScope {
    /// Global scope for variables visible from any scope.
    Global,

    /// Local scope for variables visible only within a function or subroutine.
    Local,

    /// Temporary scope for intermediate values during expression evaluation.
    Temp,
}

impl fmt::Display for RegisterScope {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Global => write!(f, "global"),
            Self::Local => write!(f, "local"),
            Self::Temp => write!(f, "temp"),
        }
    }
}

/// Error to indicate that we have run out of registers.
#[derive(Debug, thiserror::Error)]
#[error("Out of registers")]
pub(crate) struct OutOfRegistersError(());

/// Error types for bytecode parsing.
#[derive(Debug, thiserror::Error)]
pub(crate) enum ParseError {
    /// The type tag in the bytecode is not recognized.
    #[error("{0}: Invalid type tag {0}")]
    InvalidTypeTag(u64),
}

/// Result type for bytecode parsing operations.
pub(crate) type ParseResult<T> = Result<T, ParseError>;

/// Conversions between a primitive type and a `u32` for insertion into an instruction.
trait RawValue: Sized {
    /// Converts a `u32` to the primitive type `Self`.
    ///
    /// This operation is only performed to _parse_ bytecode and we assume that the bytecode is
    /// correctly formed.  As a result, this does not perform any range checks.
    fn from_u32(v: u32) -> Self;

    /// Converts the primitive type `Self` to a u32.
    ///
    /// This operation is only performed to _generate_ bytecode during compilation, and all
    /// instruction definitions need to have fields that always fit in a u32.  Consequently,
    /// this operation is always safe.
    fn to_u32(self) -> u32;
}

/// Implements `RawValue` for an unsigned primitive type that is narrower than `u32`.
macro_rules! impl_raw_value {
    ( $ty:ty, $from_u32_conv:ident ) => {
        impl RawValue for $ty {
            fn from_u32(v: u32) -> Self {
                $from_u32_conv(v)
            }

            fn to_u32(self) -> u32 {
                u32::from(self)
            }
        }
    };
}

impl_raw_value!(u8, unchecked_u32_as_u8);
impl_raw_value!(u16, unchecked_u32_as_u16);

/// Representation of a register number.
///
/// Registers are represented as `u8` integers where the first `Self::MAX_GLOBAL` values
/// correspond to global registers and the numbers after those correspond to local registers.
///
/// During compilation, local register numbers are assigned starting from "logical 0" for
/// every scope in the call stack.  During execution, local register numbers must be interpreted
/// in the context of the Frame Pointer (FP) register, which indicates the offset in the register
/// bank where local registers start for the current scope.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Register(pub(crate) u8);

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "R{}", self.0)
    }
}

impl RawValue for Register {
    fn from_u32(v: u32) -> Self {
        Self(unchecked_u32_as_u8(v))
    }

    fn to_u32(self) -> u32 {
        u32::from(self.0)
    }
}

impl Register {
    /// Maximum number of supported global registers.
    pub(crate) const MAX_GLOBAL: u8 = 64;

    /// Constructs an instance of `Register` to represent the global register `reg`.  Returns an
    /// error if we have run out of global registers.
    pub(crate) fn global(reg: u8) -> Result<Self, OutOfRegistersError> {
        if reg < Self::MAX_GLOBAL { Ok(Self(reg)) } else { Err(OutOfRegistersError(())) }
    }

    /// Constructs an instance of `Register` to represent the local register `reg`.  Returns an
    /// error if we have run out of local registers.
    pub(crate) fn local(reg: u8) -> Result<Self, OutOfRegistersError> {
        match reg.checked_add(Self::MAX_GLOBAL) {
            Some(num) => Ok(Self(num)),
            None => Err(OutOfRegistersError(())),
        }
    }

    /// Breaks apart the internal register representation and returns a tuple indicating if the
    /// register is global or not and its logical index.
    pub(crate) fn to_parts(self) -> (bool, u8) {
        if self.0 < Self::MAX_GLOBAL { (true, self.0) } else { (false, self.0 - Self::MAX_GLOBAL) }
    }

    /// Creates a new tagged pointer for this register.
    ///
    /// A tagged pointer carries the type of the value pointed to by the register as well as the
    /// absolute address of the register in the register bank.  This address is calculated using
    /// the current value of `fp`.
    pub(crate) fn to_tagged_ptr(self, fp: usize, vtype: ExprType) -> u64 {
        let (is_global, index) = self.to_parts();
        let mut index = usize::from(index);
        if !is_global {
            index += fp;
        }

        let index = u32::try_from(index).expect("Cannot support that many registers");
        u64::from(vtype as u8) << 32 | u64::from(index)
    }

    /// Parses a tagged pointer previously created by `to_tagged_ptr`, returning the absolute
    /// address of the register and the type of the value pointed at.
    ///
    /// Panics if the tag is not value.
    pub(crate) fn parse_tagged_ptr(ptr: u64) -> (usize, ExprType) {
        let vtype: ExprType = {
            #[allow(unsafe_code)]
            unsafe {
                let v = unchecked_u64_as_u8(ptr >> 32);
                assert!(v <= ExprType::Text as u8);
                std::mem::transmute(v)
            }
        };

        let index = unchecked_u32_as_usize((ptr & 0xffffffff) as u32);

        (index, vtype)
    }
}

impl RawValue for ExprType {
    fn from_u32(v: u32) -> Self {
        #[allow(unsafe_code)]
        unsafe {
            let v = unchecked_u32_as_u8(v);
            assert!(v <= ExprType::Text as u8);
            std::mem::transmute(v)
        }
    }

    fn to_u32(self) -> u32 {
        u32::from(self as u8)
    }
}

/// Generates functions to construct an instruction's bytecode representation for the compiler's
/// benefit, to parse it for the VM's benefit, and to format it for debugging purposes.
macro_rules! instr {
    ( $opcode:expr, $name:expr,
      $make:ident, $parse:ident, $format:ident,
    ) => {
        pub(crate) fn $make() -> u32 {
            ($opcode as u32) << 24
        }

        pub(crate) fn $parse(op: u32) {
            debug_assert_eq!($opcode as u32, op >> 24);
        }

        pub(crate) fn $format(op: u32) -> String {
            $parse(op);
            $name.to_owned()
        }
    };

    ( $opcode:expr, $name: expr,
      $make:ident, $parse:ident, $format:ident,
      $type1:ty, $mask1:expr, $offset1:expr,
    ) => {
        pub(crate) fn $make(v1: $type1) -> u32 {
            let v1 = (RawValue::to_u32(v1) & $mask1) << $offset1;
            (($opcode as u32) << 24) | v1
        }

        pub(crate) fn $parse(op: u32) -> $type1 {
            debug_assert_eq!($opcode as u32, op >> 24);
            let v1 = RawValue::from_u32((op >> $offset1) & $mask1);
            v1
        }

        pub(crate) fn $format(op: u32) -> String {
            let v1 = $parse(op);
            format!("{:11} {}", $name, v1)
        }
    };

    ( $opcode:expr, $name:expr,
      $make:ident, $parse:ident, $format:ident,
      $type1:ty, $mask1:expr, $offset1:expr,
      $type2:ty, $mask2:expr, $offset2:expr,
    ) => {
        pub(crate) fn $make(v1: $type1, v2: $type2) -> u32 {
            let v1 = (RawValue::to_u32(v1) & $mask1) << $offset1;
            let v2 = (RawValue::to_u32(v2) & $mask2) << $offset2;
            (($opcode as u32) << 24) | v1 | v2
        }

        pub(crate) fn $parse(op: u32) -> ($type1, $type2) {
            debug_assert_eq!($opcode as u32, op >> 24);
            let v1 = RawValue::from_u32((op >> $offset1) & $mask1);
            let v2 = RawValue::from_u32((op >> $offset2) & $mask2);
            (v1, v2)
        }

        pub(crate) fn $format(op: u32) -> String {
            let (v1, v2) = $parse(op);
            format!("{:11} {}, {}", $name, v1, v2)
        }
    };

    ( $opcode:expr, $name:expr,
      $make:ident, $parse:ident, $format:ident,
      $type1:ty, $mask1:expr, $offset1:expr,
      $type2:ty, $mask2:expr, $offset2:expr,
      $type3:ty, $mask3:expr, $offset3:expr,
    ) => {
        pub(crate) fn $make(v1: $type1, v2: $type2, v3: $type3) -> u32 {
            let v1 = (RawValue::to_u32(v1) & $mask1) << $offset1;
            let v2 = (RawValue::to_u32(v2) & $mask2) << $offset2;
            let v3 = (RawValue::to_u32(v3) & $mask3) << $offset3;
            (($opcode as u32) << 24) | v1 | v2 | v3
        }

        pub(crate) fn $parse(op: u32) -> ($type1, $type2, $type3) {
            debug_assert_eq!($opcode as u32, op >> 24);
            let v1 = RawValue::from_u32((op >> $offset1) & $mask1);
            let v2 = RawValue::from_u32((op >> $offset2) & $mask2);
            let v3 = RawValue::from_u32((op >> $offset3) & $mask3);
            (v1, v2, v3)
        }

        pub(crate) fn $format(op: u32) -> String {
            let (v1, v2, v3) = $parse(op);
            format!("{:11} {}, {}, {}", $name, v1, v2, v3)
        }
    };
}

/// Enumeration of all valid instruction types (opcodes).
///
/// The specific numbers assigned to each instruction are not important at this moment because
/// we expect bytecode execution to always be coupled with generation (which means there is no
/// need to worry about stable values over time).
#[repr(u8)]
pub(crate) enum Opcode {
    /// Adds two doubles and stores the result into a third one.
    AddDouble,

    /// Adds two integers and stores the result into a third one.
    AddInteger,

    /// Allocates an object on the heap.
    Alloc,

    /// Calls an address relative to the PC.
    Call,

    /// Concatenates two strings and stores the pointer to the result into a third one.
    Concat,

    /// Converts the double value in a register to an integer.
    DoubleToInteger,

    /// Allocates local registers (locals and temporaries) when entering a scope.
    Enter,

    /// Jumps to a subroutine at an address relative to the PC.
    Gosub,

    /// Converts the integer value in a register to a double.
    IntegerToDouble,

    /// Jumps to an address relative to the PC.
    Jump,

    /// Loads a constant into a register.
    LoadConstant,

    /// Loads an integer immediate into a register.
    LoadInteger,

    /// Loads a register pointer into a register.
    LoadRegisterPointer,

    /// Moves (copies) data between two registers.
    Move,

    /// The "null" instruction, used by the compiler to pad the code for fixups.
    Nop,

    /// Returns from a previous `Call`.
    Return,

    /// Requests the execution of an upcall, stopping VM execution.
    Upcall,

    /// Terminates execution.
    // KEEP THIS LAST.
    End,
}

#[rustfmt::skip]
instr!(
    Opcode::AddDouble, "ADDD",
    make_add_double, parse_add_double, format_add_double,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::AddInteger, "ADDI",
    make_add_integer, parse_add_integer, format_add_integer,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::Alloc, "ALLOC",
    make_alloc, parse_alloc, format_alloc,
    Register, 0x000000ff, 8,  // Destination register in which to store the heap pointer.
    ExprType, 0x000000ff, 0,  // Type of the object to allocate.
);

#[rustfmt::skip]
instr!(
    Opcode::Call, "CALL",
    make_call, parse_call, format_call,
    Register, 0x000000ff, 16,  // Destination register for the return value, if any.
    u16, 0x0000ffff, 0,  // Target address.
);

#[rustfmt::skip]
instr!(
    Opcode::Concat, "CONCAT",
    make_concat, parse_concat, format_concat,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::DoubleToInteger, "DTOI",
    make_double_to_integer, parse_double_to_integer, format_double_to_integer,
    Register, 0x000000ff, 0,  // Register with the value to convert.
);

#[rustfmt::skip]
instr!(
    Opcode::End, "END",
    make_end, parse_end, format_end,
    Register, 0x000000ff, 0,  // Register with the return code.
);

#[rustfmt::skip]
instr!(
    Opcode::Enter, "ENTER",
    make_enter, parse_enter, format_enter,
    u8, 0x000000ff, 0,  // Number of local registers to allocate.
);

#[rustfmt::skip]
instr!(
    Opcode::Gosub, "GOSUB",
    make_gosub, parse_gosub, format_gosub,
    u16, 0x0000ffff, 0,  // Target address.
);

#[rustfmt::skip]
instr!(
    Opcode::IntegerToDouble, "ITOD",
    make_integer_to_double, parse_integer_to_double, format_integer_to_double,
    Register, 0x000000ff, 0,  // Register with the value to convert.
);

#[rustfmt::skip]
instr!(
    Opcode::Jump, "JUMP",
    make_jump, parse_jump, format_jump,
    u16, 0x0000ffff, 0,  // Target address.
);

#[rustfmt::skip]
instr!(
    Opcode::LoadConstant, "LOADC",
    make_load_constant, parse_load_constant, format_load_constant,
    Register, 0x000000ff, 16,  // Destination register to load the constant into.
    u16, 0x0000ffff, 0,  // Index of the constant to load.
);

#[rustfmt::skip]
instr!(
    Opcode::LoadInteger, "LOADI",
    make_load_integer, parse_load_integer, format_load_integer,
    Register, 0x000000ff, 16,  // Destination register to load the immediate into.
    u16, 0x0000ffff, 0,  // Immediate value.
);

#[rustfmt::skip]
instr!(
    Opcode::LoadRegisterPointer, "LOADRP",
    make_load_register_ptr, parse_load_register_ptr, format_load_register_ptr,
    Register, 0x000000ff, 16,  // Destination register to load the immediate into.
    ExprType, 0x000000ff, 8,  // Type of the value pointed to.
    Register, 0x000000ff, 0,  // Register to load.
);

#[rustfmt::skip]
instr!(
    Opcode::Move, "MOVE",
    make_move, parse_move, format_move,
    Register, 0x000000ff, 8,  // Destination register.
    Register, 0x000000ff, 0,  // Source register.
);

#[rustfmt::skip]
instr!(
    Opcode::Nop, "NOP",
    make_nop, parse_nop, format_nop,
);

#[rustfmt::skip]
instr!(
    Opcode::Return, "RETURN",
    make_return, parse_return, format_return,
);

#[rustfmt::skip]
instr!(
    Opcode::Upcall, "UPCALL",
    make_upcall, parse_upcall, format_upcall,
    u16, 0x0000ffff, 8,  // Index of the upcall to execute.
    Register, 0x000000ff, 0,  // First register with arguments.
);

/// Returns the opcode of an instruction.
pub(crate) fn opcode_of(instr: u32) -> Opcode {
    #[allow(unsafe_code)]
    unsafe {
        let num = unchecked_u32_as_u8(instr >> 24);
        debug_assert!(num <= Opcode::End as u8);
        std::mem::transmute::<u8, Opcode>(num)
    }
}

/// Tags used as integer register values to identify the type stored in another register at
/// runtime.
///
/// This is used in function and command calls that receive variadic arguments (such as `PRINT`)
/// to identify the types of the arguments (which can be missing) and separators.
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(u8)]
pub enum VarArgTag {
    /// The argument is missing.  This is only possible for command invocations.
    Missing(ArgSep) = 0,

    /// The argument is an immediate of the given type.
    Immediate(ArgSep, ExprType) = 1,

    /// The argument is a pointer.
    Pointer(ArgSep) = 2,
}

impl VarArgTag {
    /// Parses a register `value` into a variadic argument tag.
    // This is not `TryFrom` because that makes this interface public and forces us to make the
    // result type public as well, but we don't need it to be.
    pub(crate) fn parse_u64(value: u64) -> ParseResult<Self> {
        if value & !(0x0fff) != 0 {
            return Err(ParseError::InvalidTypeTag(value));
        };

        let key_u8 = ((value & 0x0f00) >> 8) as u8;
        let sep_u8 = ((value & 0x00f0) >> 4) as u8;
        let other_u8 = (value & 0x000f) as u8;

        let Ok(sep) = ArgSep::try_from(sep_u8) else {
            return Err(ParseError::InvalidTypeTag(value));
        };

        match key_u8 {
            0 => {
                if other_u8 == 0 {
                    Ok(Self::Missing(sep))
                } else {
                    Err(ParseError::InvalidTypeTag(value))
                }
            }
            1 => match ExprType::try_from(other_u8) {
                Ok(etype) => Ok(Self::Immediate(sep, etype)),
                Err(_) => Err(ParseError::InvalidTypeTag(value)),
            },
            2 => {
                if other_u8 == 0 {
                    Ok(Self::Pointer(sep))
                } else {
                    Err(ParseError::InvalidTypeTag(value))
                }
            }
            _ => Err(ParseError::InvalidTypeTag(value)),
        }
    }

    /// Makes a new tag for the type of a variadic argument.
    pub(crate) fn make_u16(self) -> u16 {
        let (key_u8, sep, other_u8): (u8, ArgSep, u8) = match self {
            Self::Missing(sep) => (0, sep, 0),
            Self::Immediate(sep, etype) => (1, sep, etype as u8),
            Self::Pointer(sep) => (2, sep, 0),
        };
        u16::from(key_u8) << 8 | u16::from(sep as u8) << 4 | u16::from(other_u8)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! test_instr {
        ( $name:ident, $make:ident, $parse:ident ) => {
            #[test]
            fn $name() {
                let instr = $make();
                $parse(instr);
            }
        };

        ( $name:ident, $make:ident, $parse:ident, $v1:expr ) => {
            #[test]
            fn $name() {
                let instr = $make($v1);
                assert_eq!($v1, $parse(instr));
            }
        };

        ( $name:ident, $make:ident, $parse:ident, $v1:expr, $v2:expr ) => {
            #[test]
            fn $name() {
                let instr = $make($v1, $v2);
                assert_eq!(($v1, $v2), $parse(instr));
            }
        };

        ( $name:ident, $make:ident, $parse:ident, $v1:expr, $v2:expr, $v3:expr ) => {
            #[test]
            fn $name() {
                let instr = $make($v1, $v2, $v3);
                assert_eq!(($v1, $v2, $v3), $parse(instr));
            }
        };
    }

    test_instr!(
        test_add_double,
        make_add_double,
        parse_add_double,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_add_integer,
        make_add_integer,
        parse_add_integer,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_alloc,
        make_alloc,
        parse_alloc,
        Register::local(1).unwrap(),
        ExprType::Integer
    );

    test_instr!(test_call, make_call, parse_call, Register::local(3).unwrap(), 12345);

    test_instr!(
        test_concat,
        make_concat,
        parse_concat,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_double_to_integer,
        make_double_to_integer,
        parse_double_to_integer,
        Register::local(1).unwrap()
    );

    test_instr!(test_end, make_end, parse_end, Register::local(1).unwrap());

    test_instr!(test_enter, make_enter, parse_enter, 10);

    test_instr!(test_gosub, make_gosub, parse_gosub, 12345);

    test_instr!(
        test_integer_to_double,
        make_integer_to_double,
        parse_integer_to_double,
        Register::local(1).unwrap()
    );

    test_instr!(test_jump, make_jump, parse_jump, 12345);

    test_instr!(
        test_load_constant,
        make_load_constant,
        parse_load_constant,
        Register::local(1).unwrap(),
        12345
    );

    test_instr!(
        test_load_integer,
        make_load_integer,
        parse_load_integer,
        Register::local(1).unwrap(),
        12345
    );

    test_instr!(
        test_load_register_ptr,
        make_load_register_ptr,
        parse_load_register_ptr,
        Register::local(1).unwrap(),
        ExprType::Double,
        Register::local(2).unwrap()
    );

    test_instr!(
        test_move,
        make_move,
        parse_move,
        Register::local(1).unwrap(),
        Register::local(2).unwrap()
    );

    test_instr!(test_nop, make_nop, parse_nop);

    test_instr!(test_return, make_return, parse_return);

    test_instr!(test_upcall, make_upcall, parse_upcall, 12345, Register::local(3).unwrap());

    #[test]
    fn test_var_arg_tag_ok() {
        for sep in [ArgSep::As, ArgSep::End, ArgSep::Long, ArgSep::Short] {
            for vat in [
                VarArgTag::Missing(sep),
                VarArgTag::Pointer(sep),
                VarArgTag::Immediate(sep, ExprType::Boolean),
                VarArgTag::Immediate(sep, ExprType::Double),
                VarArgTag::Immediate(sep, ExprType::Integer),
                VarArgTag::Immediate(sep, ExprType::Text),
            ] {
                assert_eq!(vat, VarArgTag::parse_u64(u64::from(VarArgTag::make_u16(vat))).unwrap());
            }
        }
    }

    #[test]
    fn test_var_arg_tag_errors() {
        // Larger than 12 bits.
        VarArgTag::parse_u64(1 << 12).unwrap_err();

        // Invalid tag type.
        VarArgTag::parse_u64(0x00000500).unwrap_err();

        // Missing tag with invalid payload.
        VarArgTag::parse_u64(0x00000001).unwrap_err();

        // Missing tag with invalid separator.
        VarArgTag::parse_u64(0x00000040).unwrap_err();

        // ExprType tag with invalid payload.
        VarArgTag::parse_u64(0x00000104).unwrap_err();

        // ExprType tag with invalid separator.
        VarArgTag::parse_u64(0x00000140).unwrap_err();

        // Pointer tag with invalid payload.
        VarArgTag::parse_u64(0x00000201).unwrap_err();

        // Pointer tag with invalid separator.
        VarArgTag::parse_u64(0x00000240).unwrap_err();
    }
}
