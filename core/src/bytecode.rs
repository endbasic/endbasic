// EndBASIC
// Copyright 2022 Julio Merino
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

//! Low-level representation of an EndBASIC program for execution.

use crate::ast::{ExprType, Value};
use crate::reader::LineCol;
use crate::syms::SymbolKey;

/// Convenience type to represent a program address.
pub type Address = usize;

/// Components of an array definition.
#[derive(Debug, PartialEq)]
#[cfg_attr(test, derive(Clone))]
pub struct DimArrayISpan {
    /// Name of the array to define.
    pub name: SymbolKey,

    /// Position of the name.
    pub name_pos: LineCol,

    /// Number of values in the stack representing the dimensions of the array.
    pub dimensions: usize,

    /// Type of the array to be defined.
    pub subtype: ExprType,

    /// Position of the subtype.
    pub subtype_pos: LineCol,
}

/// Components of an unconditional jump instruction.
#[derive(Debug, Eq, PartialEq)]
pub struct JumpISpan {
    /// The address to jump to.
    pub addr: Address,
}

/// Components of a conditional jump that depends on whether a variable is defined.
#[cfg_attr(test, derive(Debug, Eq, PartialEq))]
pub struct JumpIfDefinedISpan {
    /// The variable to check for nonexistence.
    pub var: SymbolKey,

    /// The address to jump to.
    pub addr: Address,
}

/// Components of a change to the error handler.
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug, Eq, PartialEq))]
pub enum ErrorHandlerISpan {
    /// Jumps to the included address on error.
    Jump(Address),

    /// Sets the error handler to the default.
    None,

    /// Sets the error handler to resume execution at to the next instruction.
    ResumeNext,
}

/// Components of a request to unset a variable.
#[cfg_attr(test, derive(Debug, Eq, PartialEq))]
pub struct UnsetISpan {
    /// Name of the variable to unset.
    pub name: SymbolKey,

    /// Position of where this instruction was requested.
    pub pos: LineCol,
}

/// Representation of all possible instructions in the bytecode.
#[cfg_attr(test, derive(Debug, PartialEq))]
pub enum Instruction {
    /// Represents a binary logical "and" operation.
    LogicalAnd(LineCol),

    /// Represents a binary logical "or" operation.
    LogicalOr(LineCol),

    /// Represents a binary logical "xor" operation.
    LogicalXor(LineCol),

    /// Represents a unary logical "not" operation.
    LogicalNot(LineCol),

    /// Represents a binary bitwise "and" operation.
    BitwiseAnd(LineCol),

    /// Represents a binary bitwise "or" operation.
    BitwiseOr(LineCol),

    /// Represents a binary bitwise "xor" operation.
    BitwiseXor(LineCol),

    /// Represents a unary bitwise "not" operation.
    BitwiseNot(LineCol),

    /// Represents a left bitshift.
    ShiftLeft(LineCol),

    /// Represents a right bitshift.
    ShiftRight(LineCol),

    /// Represents an equality comparison for booleans.
    EqualBooleans(LineCol),

    /// Represents an inequality comparison for booleans.
    NotEqualBooleans(LineCol),

    /// Represents an equality comparison for doubles.
    EqualDoubles(LineCol),

    /// Represents an inequality comparison for doubles.
    NotEqualDoubles(LineCol),

    /// Represents a less-than comparison for doubles.
    LessDoubles(LineCol),

    /// Represents a less-or-equal comparison for doubles.
    LessEqualDoubles(LineCol),

    /// Represents a greater-than comparison for doubles.
    GreaterDoubles(LineCol),

    /// Represents a greater-or-equal comparison for doubles.
    GreaterEqualDoubles(LineCol),

    /// Represents an equality comparison for integers.
    EqualIntegers(LineCol),

    /// Represents an inequality comparison for integers.
    NotEqualIntegers(LineCol),

    /// Represents a less-than comparison for integers.
    LessIntegers(LineCol),

    /// Represents a less-or-equal comparison for integers.
    LessEqualIntegers(LineCol),

    /// Represents a greater-than comparison for integers.
    GreaterIntegers(LineCol),

    /// Represents a greater-or-equal comparison for integers.
    GreaterEqualIntegers(LineCol),

    /// Represents an equality comparison for strings.
    EqualStrings(LineCol),

    /// Represents an inequality comparison for strings.
    NotEqualStrings(LineCol),

    /// Represents a less-than comparison for strings.
    LessStrings(LineCol),

    /// Represents a less-or-equal comparison for strings.
    LessEqualStrings(LineCol),

    /// Represents a greater-than comparison for strings.
    GreaterStrings(LineCol),

    /// Represents a greater-or-equal comparison for strings.
    GreaterEqualStrings(LineCol),

    /// Represents an arithmetic addition operation for doubles.
    AddDoubles(LineCol),

    /// Represents an arithmetic subtraction operation for doubles.
    SubtractDoubles(LineCol),

    /// Represents an arithmetic multiplication operation for doubles.
    MultiplyDoubles(LineCol),

    /// Represents an arithmetic division operation for doubles.
    DivideDoubles(LineCol),

    /// Represents an arithmetic modulo operation for doubles.
    ModuloDoubles(LineCol),

    /// Represents an arithmetic power operation for doubles.
    PowerDoubles(LineCol),

    /// Represents an arithmetic sign flip operation for a double.
    NegateDouble(LineCol),

    /// Represents an arithmetic addition operation for integers.
    AddIntegers(LineCol),

    /// Represents an arithmetic subtraction operation for integers.
    SubtractIntegers(LineCol),

    /// Represents an arithmetic multiplication operation for integers.
    MultiplyIntegers(LineCol),

    /// Represents an arithmetic division operation for integers.
    DivideIntegers(LineCol),

    /// Represents an arithmetic modulo operation for integers.
    ModuloIntegers(LineCol),

    /// Represents an arithmetic power operation for integers.
    PowerIntegers(LineCol),

    /// Represents an arithmetic sign flip operation for an integer.
    NegateInteger(LineCol),

    /// Represents the concatenation of strings.
    ConcatStrings(LineCol),

    /// Represents an assignment to an element of an array with the given number of subscripts.
    ArrayAssignment(SymbolKey, LineCol, usize),

    /// Represents a load of an array's element into the stack.
    ArrayLoad(SymbolKey, LineCol, usize),

    /// Represents an assignment of a value to a variable.
    Assign(SymbolKey),

    /// Represents a call to a builtin command such as `PRINT` with the given number of arguments.
    ///
    /// The arguments in the stack are interspersed with the separators used to separate them from.
    /// each other, because those separators have meaning.
    BuiltinCall(SymbolKey, LineCol, usize),

    /// Represents an unconditional call to a location that will return.
    Call(JumpISpan),

    /// Represents a call to the given function with the given number of arguments.
    FunctionCall(SymbolKey, ExprType, LineCol, usize),

    /// Represents a variable definition.
    Dim(SymbolKey, ExprType),

    /// Represents an array definition.
    DimArray(DimArrayISpan),

    /// Represents a request to terminate the program.  If the boolean is true, the exit ode is
    /// at the top of the stack.
    End(bool),

    /// Represents a conversion of a float to an integer with rounding.
    DoubleToInteger,

    /// Represents a conversion of an integer to a float.
    IntegerToDouble,

    /// Represents an unconditional jump.
    Jump(JumpISpan),

    /// Represents an conditional jump that jumps if the variable is defined.
    JumpIfDefined(JumpIfDefinedISpan),

    /// Represents an conditional jump that jumps if the condition is met.
    JumpIfTrue(Address),

    /// Represents an conditional jump that jumps if the condition is not met.
    JumpIfNotTrue(Address),

    /// Represents a load of a boolean variable's value from main memory into the stack.
    LoadBoolean(SymbolKey, LineCol),

    /// Represents a load of a double variable's value from main memory into the stack.
    LoadDouble(SymbolKey, LineCol),

    /// Represents a load of an integer variable's value from main memory into the stack.
    LoadInteger(SymbolKey, LineCol),

    /// Represents a load of a string variable's value from main memory into the stack.
    LoadString(SymbolKey, LineCol),

    /// Represents a load of a variable's reference into the stack.
    LoadRef(SymbolKey, ExprType, LineCol),

    /// Represents an instruction that does nothing.
    Nop,

    /// Represents a load of a literal boolean value into the top of the stack.
    PushBoolean(bool, LineCol),

    /// Represents a load of a literal double value into the top of the stack.
    PushDouble(f64, LineCol),

    /// Represents a load of a literal integer value into the top of the stack.
    PushInteger(i32, LineCol),

    /// Represents a load of a literal string value into the top of the stack.
    PushString(String, LineCol),

    /// Represents a return after a call.
    Return(LineCol),

    /// Represents a change in the error handler state.
    SetErrorHandler(ErrorHandlerISpan),

    /// Represents a request to unset a variable.
    Unset(UnsetISpan),
}

impl Instruction {
    pub(crate) fn is_statement(&self) -> bool {
        match self {
            Instruction::LogicalAnd(_)
            | Instruction::LogicalOr(_)
            | Instruction::LogicalXor(_)
            | Instruction::LogicalNot(_)
            | Instruction::BitwiseAnd(_)
            | Instruction::BitwiseOr(_)
            | Instruction::BitwiseXor(_)
            | Instruction::BitwiseNot(_)
            | Instruction::ArrayLoad(_, _, _)
            | Instruction::ShiftLeft(_)
            | Instruction::ShiftRight(_)
            | Instruction::EqualBooleans(_)
            | Instruction::NotEqualBooleans(_)
            | Instruction::EqualDoubles(_)
            | Instruction::NotEqualDoubles(_)
            | Instruction::LessDoubles(_)
            | Instruction::LessEqualDoubles(_)
            | Instruction::GreaterDoubles(_)
            | Instruction::GreaterEqualDoubles(_)
            | Instruction::EqualIntegers(_)
            | Instruction::NotEqualIntegers(_)
            | Instruction::LessIntegers(_)
            | Instruction::LessEqualIntegers(_)
            | Instruction::GreaterIntegers(_)
            | Instruction::GreaterEqualIntegers(_)
            | Instruction::EqualStrings(_)
            | Instruction::NotEqualStrings(_)
            | Instruction::LessStrings(_)
            | Instruction::LessEqualStrings(_)
            | Instruction::GreaterStrings(_)
            | Instruction::GreaterEqualStrings(_)
            | Instruction::AddDoubles(_)
            | Instruction::SubtractDoubles(_)
            | Instruction::MultiplyDoubles(_)
            | Instruction::DivideDoubles(_)
            | Instruction::ModuloDoubles(_)
            | Instruction::PowerDoubles(_)
            | Instruction::NegateDouble(_)
            | Instruction::AddIntegers(_)
            | Instruction::SubtractIntegers(_)
            | Instruction::MultiplyIntegers(_)
            | Instruction::DivideIntegers(_)
            | Instruction::ModuloIntegers(_)
            | Instruction::PowerIntegers(_)
            | Instruction::NegateInteger(_)
            | Instruction::ConcatStrings(_)
            | Instruction::FunctionCall(_, _, _, _)
            | Instruction::DoubleToInteger
            | Instruction::IntegerToDouble
            | Instruction::LoadBoolean(_, _)
            | Instruction::LoadDouble(_, _)
            | Instruction::LoadInteger(_, _)
            | Instruction::LoadString(_, _)
            | Instruction::LoadRef(_, _, _)
            | Instruction::PushBoolean(_, _)
            | Instruction::PushDouble(_, _)
            | Instruction::PushInteger(_, _)
            | Instruction::PushString(_, _) => false,

            Instruction::ArrayAssignment(_, _, _)
            | Instruction::Assign(_)
            | Instruction::BuiltinCall(_, _, _)
            | Instruction::Call(_)
            | Instruction::Dim(_, _)
            | Instruction::DimArray(_)
            | Instruction::End(_)
            | Instruction::Jump(_)
            | Instruction::JumpIfDefined(_)
            | Instruction::JumpIfTrue(_)
            | Instruction::JumpIfNotTrue(_)
            | Instruction::Nop
            | Instruction::Return(_)
            | Instruction::SetErrorHandler(_)
            | Instruction::Unset(_) => true,
        }
    }
}

/// Representation of a compiled program.
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct Image {
    /// Collection of instructions in the program.
    ///
    /// The indices of this vector correspond to the program counter.
    pub instrs: Vec<Instruction>,

    /// Collection of data values in the program.
    pub data: Vec<Option<Value>>,
}
