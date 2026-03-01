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

/// Error to indicate that an array has too many dimensions.
#[derive(Debug, thiserror::Error)]
#[error("Too many dimensions")]
pub(crate) struct TooManyArrayDimensionsError(());

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
}

/// A tagged reference to a variable (register) encoding the register's absolute address
/// and the type of the value it holds.
///
/// The encoding stores the `ExprType` tag in the upper 32 bits and the absolute register
/// address in the lower 32 bits of a `u64`.
///
/// This is distinct from `DatumPtr`, which points to data in the constant pool or heap
/// rather than to a register in the register file.
pub(crate) struct TaggedRegisterRef(u64);

impl TaggedRegisterRef {
    /// Creates a new tagged register reference from a register, frame pointer, and type.
    pub(crate) fn new(reg: Register, fp: usize, vtype: ExprType) -> Self {
        let (is_global, index) = reg.to_parts();
        let mut index = usize::from(index);
        if !is_global {
            index += fp;
        }

        let index = u32::try_from(index).expect("Cannot support that many registers");
        Self(u64::from(vtype as u8) << 32 | u64::from(index))
    }

    /// Parses a tagged register reference from a raw `u64`, returning the absolute register
    /// index and the type of the value it holds.
    ///
    /// Panics if the type tag is invalid.
    pub(crate) fn parse(self) -> (usize, ExprType) {
        let vtype: ExprType = {
            #[allow(unsafe_code)]
            unsafe {
                let v = unchecked_u64_as_u8(self.0 >> 32);
                assert!(v <= ExprType::Text as u8);
                std::mem::transmute(v)
            }
        };

        let index = unchecked_u32_as_usize((self.0 & 0xffffffff) as u32);

        (index, vtype)
    }

    /// Returns the raw `u64` encoding.
    pub(crate) fn as_u64(&self) -> u64 {
        self.0
    }

    /// Wraps a raw `u64` as a `TaggedRegisterRef`.
    pub(crate) fn from_u64(v: u64) -> Self {
        Self(v)
    }
}

/// A packed representation of an array's element type and number of dimensions.
///
/// The encoding stores the `ExprType` in the upper 4 bits and the dimension count in the
/// lower 4 bits of a single `u8`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct PackedArrayType(u8);

impl PackedArrayType {
    /// Creates a new packed array type from a subtype and dimension count.
    pub(crate) fn new(
        subtype: ExprType,
        ndims: usize,
    ) -> Result<Self, TooManyArrayDimensionsError> {
        if ndims > 15 {
            return Err(TooManyArrayDimensionsError(()));
        }
        let ndims = ndims as u8;
        Ok(Self(((subtype as u8) << 4) | (ndims & 0x0f)))
    }

    /// Returns the element type.
    pub(crate) fn subtype(self) -> ExprType {
        ExprType::from_u32(u32::from(self.0 >> 4))
    }

    /// Returns the number of dimensions.
    pub(crate) fn ndims(self) -> u8 {
        self.0 & 0x0f
    }
}

impl fmt::Display for PackedArrayType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}]{}", self.ndims(), self.subtype().annotation())
    }
}

impl RawValue for PackedArrayType {
    fn from_u32(v: u32) -> Self {
        Self(unchecked_u32_as_u8(v))
    }

    fn to_u32(self) -> u32 {
        u32::from(self.0)
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

    /// Allocates a multidimensional array on the heap.
    AllocArray,

    /// Computes the bitwise AND of two integers and stores the result into a third one.
    BitwiseAnd,

    /// Computes the bitwise NOT of an integer value in place.
    BitwiseNot,

    /// Computes the bitwise OR of two integers and stores the result into a third one.
    BitwiseOr,

    /// Computes the bitwise XOR of two integers and stores the result into a third one.
    BitwiseXor,

    /// Calls an address relative to the PC.
    Call,

    /// Concatenates two strings and stores the pointer to the result into a third one.
    Concat,

    /// Divides two doubles and stores the result into a third one.
    DivideDouble,

    /// Divides two integers and stores the result into a third one.
    DivideInteger,

    /// Converts the double value in a register to an integer.
    DoubleToInteger,

    /// Compares two booleans for equality and stores the result into a third one.
    EqualBoolean,

    /// Compares two doubles for equality and stores the result into a third one.
    EqualDouble,

    /// Compares two integers for equality and stores the result into a third one.
    EqualInteger,

    /// Compares two strings for equality and stores the result into a third one.
    EqualText,

    /// Allocates local registers (locals and temporaries) when entering a scope.
    Enter,

    /// Jumps to a subroutine at an address relative to the PC.
    Gosub,

    /// Compares two doubles for greater-than and stores the result into a third one.
    GreaterDouble,

    /// Compares two doubles for greater-than-or-equal and stores the result into a third one.
    GreaterEqualDouble,

    /// Compares two integers for greater-than-or-equal and stores the result into a third one.
    GreaterEqualInteger,

    /// Compares two strings for greater-than-or-equal and stores the result into a third one.
    GreaterEqualText,

    /// Compares two integers for greater-than and stores the result into a third one.
    GreaterInteger,

    /// Compares two strings for greater-than and stores the result into a third one.
    GreaterText,

    /// Converts the integer value in a register to a double.
    IntegerToDouble,

    /// Jumps to an address relative to the PC.
    Jump,

    /// Deallocates the registers allocated by the preamble ENTER, unwinding to the FP.
    Leave,

    /// Compares two doubles for less-than and stores the result into a third one.
    LessDouble,

    /// Compares two doubles for less-than-or-equal and stores the result into a third one.
    LessEqualDouble,

    /// Compares two integers for less-than-or-equal and stores the result into a third one.
    LessEqualInteger,

    /// Compares two strings for less-than-or-equal and stores the result into a third one.
    LessEqualText,

    /// Compares two integers for less-than and stores the result into a third one.
    LessInteger,

    /// Compares two strings for less-than and stores the result into a third one.
    LessText,

    /// Loads an element from an array.
    LoadArray,

    /// Loads a constant into a register.
    LoadConstant,

    /// Loads an integer immediate into a register.
    LoadInteger,

    /// Loads a register pointer into a register.
    LoadRegisterPointer,

    /// Computes the modulo of two doubles and stores the result into a third one.
    ModuloDouble,

    /// Computes the modulo of two integers and stores the result into a third one.
    ModuloInteger,

    /// Moves (copies) data between two registers.
    Move,

    /// Multiplies two doubles and stores the result into a third one.
    MultiplyDouble,

    /// Multiplies two integers and stores the result into a third one.
    MultiplyInteger,

    /// Negates a double value in place.
    NegateDouble,

    /// Negates an integer value in place.
    NegateInteger,

    /// Compares two booleans for inequality and stores the result into a third one.
    NotEqualBoolean,

    /// Compares two doubles for inequality and stores the result into a third one.
    NotEqualDouble,

    /// Compares two integers for inequality and stores the result into a third one.
    NotEqualInteger,

    /// Compares two strings for inequality and stores the result into a third one.
    NotEqualText,

    /// The "null" instruction, used by the compiler to pad the code for fixups.
    Nop,

    /// Computes the power of two doubles and stores the result into a third one.
    PowerDouble,

    /// Computes the power of two integers and stores the result into a third one.
    PowerInteger,

    /// Returns from a previous `Call`.
    Return,

    /// Shifts an integer left by a number of bits without rotation, storing the result into
    /// a third register.
    ShiftLeft,

    /// Shifts an integer right by a number of bits without rotation, storing the result into
    /// a third register.
    ShiftRight,

    /// Stores a value into an array element.
    StoreArray,

    /// Subtracts two doubles and stores the result into a third one.
    SubtractDouble,

    /// Subtracts two integers and stores the result into a third one.
    SubtractInteger,

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
    Opcode::AllocArray, "ALLOCA",
    make_alloc_array, parse_alloc_array, format_alloc_array,
    Register, 0x000000ff, 16,  // Destination register to store the array pointer.
    PackedArrayType, 0x000000ff, 8,  // Packed element type and dimension count.
    Register, 0x000000ff, 0,  // First register containing dimension sizes.
);

#[rustfmt::skip]
instr!(
    Opcode::BitwiseAnd, "AND",
    make_bitwise_and, parse_bitwise_and, format_bitwise_and,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::BitwiseNot, "NOT",
    make_bitwise_not, parse_bitwise_not, format_bitwise_not,
    Register, 0x000000ff, 0,  // Register with the value to NOT in place.
);

#[rustfmt::skip]
instr!(
    Opcode::BitwiseOr, "OR",
    make_bitwise_or, parse_bitwise_or, format_bitwise_or,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::BitwiseXor, "XOR",
    make_bitwise_xor, parse_bitwise_xor, format_bitwise_xor,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
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
    Opcode::DivideDouble, "DIVD",
    make_divide_double, parse_divide_double, format_divide_double,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::DivideInteger, "DIVI",
    make_divide_integer, parse_divide_integer, format_divide_integer,
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
    Opcode::EqualBoolean, "CMPEQB",
    make_equal_boolean, parse_equal_boolean, format_equal_boolean,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::EqualDouble, "CMPEQD",
    make_equal_double, parse_equal_double, format_equal_double,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::EqualInteger, "CMPEQI",
    make_equal_integer, parse_equal_integer, format_equal_integer,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::EqualText, "CMPEQS",
    make_equal_text, parse_equal_text, format_equal_text,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
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
    Opcode::GreaterDouble, "CMPGTD",
    make_greater_double, parse_greater_double, format_greater_double,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::GreaterEqualDouble, "CMPGED",
    make_greater_equal_double, parse_greater_equal_double, format_greater_equal_double,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::GreaterEqualInteger, "CMPGEI",
    make_greater_equal_integer, parse_greater_equal_integer, format_greater_equal_integer,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::GreaterEqualText, "CMPGES",
    make_greater_equal_text, parse_greater_equal_text, format_greater_equal_text,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::GreaterInteger, "CMPGTI",
    make_greater_integer, parse_greater_integer, format_greater_integer,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::GreaterText, "CMPGTS",
    make_greater_text, parse_greater_text, format_greater_text,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
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
    Opcode::Leave, "LEAVE",
    make_leave, parse_leave, format_leave,
);

#[rustfmt::skip]
instr!(
    Opcode::LessDouble, "CMPLTD",
    make_less_double, parse_less_double, format_less_double,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::LessEqualDouble, "CMPLED",
    make_less_equal_double, parse_less_equal_double, format_less_equal_double,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::LessEqualInteger, "CMPLEI",
    make_less_equal_integer, parse_less_equal_integer, format_less_equal_integer,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::LessEqualText, "CMPLES",
    make_less_equal_text, parse_less_equal_text, format_less_equal_text,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::LessInteger, "CMPLTI",
    make_less_integer, parse_less_integer, format_less_integer,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::LessText, "CMPLTS",
    make_less_text, parse_less_text, format_less_text,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::LoadArray, "LOADA",
    make_load_array, parse_load_array, format_load_array,
    Register, 0x000000ff, 16,  // Destination register for the loaded value.
    Register, 0x000000ff, 8,  // Register containing the array pointer.
    Register, 0x000000ff, 0,  // First register containing subscript values.
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
    Opcode::ModuloDouble, "MODD",
    make_modulo_double, parse_modulo_double, format_modulo_double,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::ModuloInteger, "MODI",
    make_modulo_integer, parse_modulo_integer, format_modulo_integer,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
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
    Opcode::MultiplyDouble, "MULD",
    make_multiply_double, parse_multiply_double, format_multiply_double,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::MultiplyInteger, "MULI",
    make_multiply_integer, parse_multiply_integer, format_multiply_integer,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::NegateDouble,
    "NEGD",
    make_negate_double,
    parse_negate_double,
    format_negate_double,
    Register,
    0x000000ff,
    0, // Register with the value to negate in place.
);

#[rustfmt::skip]
instr!(
    Opcode::NegateInteger, "NEGI",
    make_negate_integer, parse_negate_integer, format_negate_integer,
    Register, 0x000000ff, 0,  // Register with the value to negate in place.
);

#[rustfmt::skip]
instr!(
    Opcode::NotEqualBoolean, "CMPNEB",
    make_not_equal_boolean, parse_not_equal_boolean, format_not_equal_boolean,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::NotEqualDouble, "CMPNED",
    make_not_equal_double, parse_not_equal_double, format_not_equal_double,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::NotEqualInteger, "CMPNEI",
    make_not_equal_integer, parse_not_equal_integer, format_not_equal_integer,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::NotEqualText, "CMPNES",
    make_not_equal_text, parse_not_equal_text, format_not_equal_text,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::Nop, "NOP",
    make_nop, parse_nop, format_nop,
);

#[rustfmt::skip]
instr!(
    Opcode::PowerDouble, "POWD",
    make_power_double, parse_power_double, format_power_double,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::PowerInteger, "POWI",
    make_power_integer, parse_power_integer, format_power_integer,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::Return, "RETURN",
    make_return, parse_return, format_return,
);

#[rustfmt::skip]
instr!(
    Opcode::ShiftLeft, "SHL",
    make_shift_left, parse_shift_left, format_shift_left,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Value to shift.
    Register, 0x000000ff, 0,  // Number of bits to shift by.
);

#[rustfmt::skip]
instr!(
    Opcode::ShiftRight, "SHR",
    make_shift_right, parse_shift_right, format_shift_right,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Value to shift.
    Register, 0x000000ff, 0,  // Number of bits to shift by.
);

#[rustfmt::skip]
instr!(
    Opcode::StoreArray, "STOREA",
    make_store_array, parse_store_array, format_store_array,
    Register, 0x000000ff, 16,  // Register containing the array pointer.
    Register, 0x000000ff, 8,  // Register containing the value to store.
    Register, 0x000000ff, 0,  // First register containing subscript values.
);

#[rustfmt::skip]
instr!(
    Opcode::SubtractDouble, "SUBD",
    make_subtract_double, parse_subtract_double, format_subtract_double,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

#[rustfmt::skip]
instr!(
    Opcode::SubtractInteger, "SUBI",
    make_subtract_integer, parse_subtract_integer, format_subtract_integer,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
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

    test_instr!(
        test_alloc_array,
        make_alloc_array,
        parse_alloc_array,
        Register::local(1).unwrap(),
        PackedArrayType::new(ExprType::Integer, 3).unwrap(),
        Register::local(2).unwrap()
    );

    test_instr!(
        test_bitwise_and,
        make_bitwise_and,
        parse_bitwise_and,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(test_bitwise_not, make_bitwise_not, parse_bitwise_not, Register::local(1).unwrap());

    test_instr!(
        test_bitwise_or,
        make_bitwise_or,
        parse_bitwise_or,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_bitwise_xor,
        make_bitwise_xor,
        parse_bitwise_xor,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
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
        test_divide_double,
        make_divide_double,
        parse_divide_double,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_divide_integer,
        make_divide_integer,
        parse_divide_integer,
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

    test_instr!(
        test_equal_boolean,
        make_equal_boolean,
        parse_equal_boolean,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_equal_double,
        make_equal_double,
        parse_equal_double,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_equal_integer,
        make_equal_integer,
        parse_equal_integer,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_equal_text,
        make_equal_text,
        parse_equal_text,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(test_end, make_end, parse_end, Register::local(1).unwrap());

    test_instr!(test_enter, make_enter, parse_enter, 10);

    test_instr!(test_gosub, make_gosub, parse_gosub, 12345);

    test_instr!(
        test_greater_double,
        make_greater_double,
        parse_greater_double,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_greater_equal_double,
        make_greater_equal_double,
        parse_greater_equal_double,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_greater_equal_integer,
        make_greater_equal_integer,
        parse_greater_equal_integer,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_greater_equal_text,
        make_greater_equal_text,
        parse_greater_equal_text,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_greater_integer,
        make_greater_integer,
        parse_greater_integer,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_greater_text,
        make_greater_text,
        parse_greater_text,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_integer_to_double,
        make_integer_to_double,
        parse_integer_to_double,
        Register::local(1).unwrap()
    );

    test_instr!(test_jump, make_jump, parse_jump, 12345);

    test_instr!(test_leave, make_leave, parse_leave);

    test_instr!(
        test_less_double,
        make_less_double,
        parse_less_double,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_less_equal_double,
        make_less_equal_double,
        parse_less_equal_double,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_less_equal_integer,
        make_less_equal_integer,
        parse_less_equal_integer,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_less_equal_text,
        make_less_equal_text,
        parse_less_equal_text,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_less_integer,
        make_less_integer,
        parse_less_integer,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_less_text,
        make_less_text,
        parse_less_text,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_load_array,
        make_load_array,
        parse_load_array,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

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
        test_modulo_double,
        make_modulo_double,
        parse_modulo_double,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_modulo_integer,
        make_modulo_integer,
        parse_modulo_integer,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_move,
        make_move,
        parse_move,
        Register::local(1).unwrap(),
        Register::local(2).unwrap()
    );

    test_instr!(
        test_multiply_double,
        make_multiply_double,
        parse_multiply_double,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_multiply_integer,
        make_multiply_integer,
        parse_multiply_integer,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_negate_double,
        make_negate_double,
        parse_negate_double,
        Register::local(1).unwrap()
    );

    test_instr!(
        test_negate_integer,
        make_negate_integer,
        parse_negate_integer,
        Register::local(1).unwrap()
    );

    test_instr!(
        test_not_equal_boolean,
        make_not_equal_boolean,
        parse_not_equal_boolean,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_not_equal_double,
        make_not_equal_double,
        parse_not_equal_double,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_not_equal_integer,
        make_not_equal_integer,
        parse_not_equal_integer,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_not_equal_text,
        make_not_equal_text,
        parse_not_equal_text,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(test_nop, make_nop, parse_nop);

    test_instr!(
        test_power_double,
        make_power_double,
        parse_power_double,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_power_integer,
        make_power_integer,
        parse_power_integer,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(test_return, make_return, parse_return);

    test_instr!(
        test_shift_left,
        make_shift_left,
        parse_shift_left,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_shift_right,
        make_shift_right,
        parse_shift_right,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_store_array,
        make_store_array,
        parse_store_array,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_subtract_double,
        make_subtract_double,
        parse_subtract_double,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(
        test_subtract_integer,
        make_subtract_integer,
        parse_subtract_integer,
        Register::local(1).unwrap(),
        Register::local(2).unwrap(),
        Register::local(3).unwrap()
    );

    test_instr!(test_upcall, make_upcall, parse_upcall, 12345, Register::local(3).unwrap());

    #[test]
    fn test_packed_array_type_round_trip() {
        for subtype in [ExprType::Boolean, ExprType::Double, ExprType::Integer, ExprType::Text] {
            for ndims in [1, 2, 5, 15] {
                let packed = PackedArrayType::new(subtype, ndims).unwrap();
                assert_eq!(subtype, packed.subtype());
                assert_eq!(ndims, usize::from(packed.ndims()));
            }
        }
    }

    #[test]
    fn test_packed_array_type_display() {
        let p = PackedArrayType::new(ExprType::Integer, 2).unwrap();
        assert_eq!("[2]%", format!("{}", p));
        let p = PackedArrayType::new(ExprType::Text, 1).unwrap();
        assert_eq!("[1]$", format!("{}", p));
    }

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
