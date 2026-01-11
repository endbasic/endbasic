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

use crate::convert::cast;
use std::fmt;

/// Error types for bytecode manipulation.
#[derive(Debug, thiserror::Error)]
pub(crate) enum Error {
    #[error("{0}: Out of {0} registers")]
    OutOfRegisters(&'static str),
}

/// Result type for bytecode manipulation.
pub(crate) type Result<T> = std::result::Result<T, Error>;

/// Conversions between a primitive type and a `u32` for insertion into an instruction.
trait RawValue {
    /// Converts a `u32` to the primitive type `Self`.
    ///
    /// This operation is only performed to _parse_ bytecode and we assume that the bytecode is
    /// correctly formed.  As a result, this does not perform any range checks and is unsafe.
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
    ( $ty:ty ) => {
        impl RawValue for $ty {
            fn from_u32(v: u32) -> Self {
                cast(v)
            }

            fn to_u32(self) -> u32 {
                u32::from(self)
            }
        }
    };
}

impl_raw_value!(u8);
impl_raw_value!(u16);

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
        Self(cast(v))
    }

    fn to_u32(self) -> u32 {
        u32::from(self.0)
    }
}

impl Register {
    /// Maximum number of supported global registers.
    pub(crate) const MAX_GLOBAL: u8 = 128;

    /// Constructs an instance of `Register` to represent the global register `reg`.  Returns an
    /// error if we have run out of global registers.
    pub(crate) fn global(reg: u8) -> Result<Self> {
        if reg < Self::MAX_GLOBAL { Ok(Self(reg)) } else { Err(Error::OutOfRegisters("global")) }
    }

    /// Constructs an instance of `Register` to represent the local register `reg`.  Returns an
    /// error if we have run out of local registers.
    pub(crate) fn local(reg: u8) -> Result<Self> {
        match reg.checked_add(Self::MAX_GLOBAL) {
            Some(num) => Ok(Self(num)),
            None => Err(Error::OutOfRegisters("local")),
        }
    }

    /// Breaks apart the internal register representation and returns a tuple indicating if the
    /// register is global or not and its logical index.
    pub(crate) fn to_parts(self) -> (bool, usize) {
        let num = usize::from(self.0);
        let max = usize::from(Self::MAX_GLOBAL);
        if num < max { (true, num) } else { (false, num - max) }
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
            format!("{} {}", $name, v1)
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
            format!("{} {}, {}", $name, v1, v2)
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
            format!("{} {}, {}, {}", $name, v1, v2, v3)
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
    /// The "null" instruction, used by the compiler to pad the code for fixups.
    Nop,

    /// Allocates local registers (locals and temporaries) when entering a scope.
    Enter,
    /// Deallocates all registers allocated by a previous `Enter`.
    Leave,

    /// Requests the execution of an upcall, stopping VM execution.
    Upcall,

    /// Moves (copies) data between two registers.
    Move,

    /// Loads an integer immediate into a register.
    LoadInteger,
    /// Loads the index of an integer constant into a register.
    LoadIntegerConstant,

    /// Adds two registers and stores the result into a third one.
    AddInteger,
}

#[rustfmt::skip]
instr!(
    Opcode::Nop, "NOP",
    make_nop, parse_nop, format_nop,
);

#[rustfmt::skip]
instr!(
    Opcode::Enter, "ENTER",
    make_enter, parse_enter, format_enter,
    u8, 0x000000ff, 0,  // Number of local registers to allocate.
);
#[rustfmt::skip]
instr!(
    Opcode::Leave, "LEAVE",
    make_leave, parse_leave, format_leave,
);

#[rustfmt::skip]
instr!(
    Opcode::Upcall, "UPCALL",
    make_upcall, parse_upcall, format_upcall,
    u16, 0x0000ffff, 8,  // Index of the upcall to execute.
    Register, 0x000000ff, 0,  // First register with arguments.
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
    Opcode::LoadInteger, "LOADIIMM",
    make_load_integer, parse_load_integer, format_load_integer,
    Register, 0x000000ff, 16,  // Destination register to load the immediate into.
    u16, 0x0000ffff, 0,  // Immediate value.
);
#[rustfmt::skip]
instr!(
    Opcode::LoadIntegerConstant, "LOADICONST",
    make_load_integer_constant, parse_load_integer_constant, format_load_integer_constant,
    Register, 0x000000ff, 16,  // Destination register to load the constant index into.
    u16, 0x0000ffff, 0,  // Constant index.
);

#[rustfmt::skip]
instr!(
    Opcode::AddInteger, "ADDI",
    make_add_integer, parse_add_integer, format_add_integer,
    Register, 0x000000ff, 16,  // Destination register to store the result of the operation.
    Register, 0x000000ff, 8,  // Left hand side value.
    Register, 0x000000ff, 0,  // Right hand side value.
);

/// Mapping of instruction opcodes (indexes in the array) to their formatters.  Used to implement
/// debugging primitives for the bytecode.
pub(crate) const INSTR_FORMATTERS: &[fn(u32) -> String] = &[
    format_nop,
    format_enter,
    format_leave,
    format_upcall,
    format_move,
    format_load_integer,
    format_load_integer_constant,
    format_add_integer,
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nop() {
        let instr = make_nop();
        parse_nop(instr);
    }

    #[test]
    fn test_enter() {
        let instr = make_enter(10);
        assert_eq!(10, parse_enter(instr));
    }

    #[test]
    fn test_leave() {
        let instr = make_leave();
        parse_leave(instr);
    }

    #[test]
    fn test_upcall() {
        let instr = make_upcall(512);
        assert_eq!(512, parse_upcall(instr));
    }

    #[test]
    fn test_move() {
        let instr = make_move(10, 20);
        assert_eq!((10, 20), parse_move(instr));
    }

    #[test]
    fn test_load_integer() {
        let instr = make_load_integer(1, 12345);
        assert_eq!((1, 12345), parse_load_integer(instr));
    }

    #[test]
    fn test_load_integer_constant() {
        let instr = make_load_integer_constant(1, 2);
        assert_eq!((1, 2), parse_load_integer_constant(instr));
    }

    #[test]
    fn test_add_integer() {
        let instr = make_add_integer(1, 2, 3);
        assert_eq!((1, 2, 3), parse_add_integer(instr));
    }
}
