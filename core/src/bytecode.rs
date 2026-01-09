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

/// Components of a builtin command call.
#[derive(Debug, PartialEq)]
#[cfg_attr(test, derive(Clone))]
pub struct BuiltinCallISpan {
    /// Name of the builtin to call.
    pub name: SymbolKey,

    /// Position of the name.
    pub name_pos: LineCol,

    /// Runtime index to execute this call.
    pub upcall_index: usize,

    /// Number of arguments on the stack for the call.
    ///
    /// The arguments in the stack are interspersed with the separators used to separate them from
    /// each other because those separators have meaning.
    pub nargs: usize,
}

/// Components of a variable definition.
#[derive(Debug, PartialEq)]
#[cfg_attr(test, derive(Clone))]
pub struct DimISpan {
    /// Name of the variable to define.
    pub name: SymbolKey,

    /// Whether the variable is global or not.
    pub shared: bool,

    /// Type of the variable to be defined.
    pub vtype: ExprType,
}

/// Components of an array definition.
#[derive(Debug, PartialEq)]
#[cfg_attr(test, derive(Clone))]
pub struct DimArrayISpan {
    /// Name of the array to define.
    pub name: SymbolKey,

    /// Position of the name.
    pub name_pos: LineCol,

    /// Whether the array is global or not.
    pub shared: bool,

    /// Number of values in the stack representing the dimensions of the array.
    pub dimensions: usize,

    /// Type of the array to be defined.
    pub subtype: ExprType,

    /// Position of the subtype.
    pub subtype_pos: LineCol,
}

/// Components of a builtin function call.
#[derive(Debug, PartialEq)]
#[cfg_attr(test, derive(Clone))]
pub struct FunctionCallISpan {
    /// Name of the builtin to call.
    pub name: SymbolKey,

    /// Position of the name.
    pub name_pos: LineCol,

    /// Runtime index to execute this call.
    pub upcall_index: usize,

    /// Return type of the function.
    pub return_type: ExprType,

    /// Number of arguments on the stack for the call.
    pub nargs: usize,
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
    BuiltinCall(BuiltinCallISpan),

    /// Represents an unconditional call to a location that will return.
    Call(JumpISpan),

    /// Represents a call to the given function with the given number of arguments.
    FunctionCall(FunctionCallISpan),

    /// Represents a variable definition.
    Dim(DimISpan),

    /// Represents an array definition.
    DimArray(DimArrayISpan),

    /// Represents a request to terminate the program.  If the boolean is true, the exit ode is
    /// at the top of the stack.
    End(bool),

    /// Represents a request to create a new scope for symbols.
    EnterScope,

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

    /// Represents a request to leave the current scope for symbols.
    LeaveScope,

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
    /// Returns the textual representation of the instruction.
    pub fn repr(&self) -> (&'static str, Option<String>) {
        match self {
            Instruction::BitwiseAnd(_pos) => ("AND%", None),
            Instruction::BitwiseOr(_pos) => ("OR%", None),
            Instruction::BitwiseXor(_pos) => ("XOR%", None),
            Instruction::BitwiseNot(_pos) => ("NOT%", None),

            Instruction::LogicalAnd(_pos) => ("AND?", None),
            Instruction::LogicalOr(_pos) => ("OR?", None),
            Instruction::LogicalXor(_pos) => ("XOR?", None),
            Instruction::LogicalNot(_pos) => ("NOT?", None),

            Instruction::ShiftLeft(_pos) => ("SHL%", None),
            Instruction::ShiftRight(_pos) => ("SHR%", None),

            Instruction::EqualBooleans(_pos) => ("CMPE?", None),
            Instruction::NotEqualBooleans(_pos) => ("CMPNE?", None),

            Instruction::EqualDoubles(_pos) => ("CMPE#", None),
            Instruction::NotEqualDoubles(_pos) => ("CMPNE#", None),
            Instruction::LessDoubles(_pos) => ("CMPL#", None),
            Instruction::LessEqualDoubles(_pos) => ("CMPLE#", None),
            Instruction::GreaterDoubles(_pos) => ("CMPG#", None),
            Instruction::GreaterEqualDoubles(_pos) => ("CMPGE#", None),

            Instruction::EqualIntegers(_pos) => ("CMPE%", None),
            Instruction::NotEqualIntegers(_pos) => ("CMPNE%", None),
            Instruction::LessIntegers(_pos) => ("CMPL%", None),
            Instruction::LessEqualIntegers(_pos) => ("CMPLE%", None),
            Instruction::GreaterIntegers(_pos) => ("CMPG%", None),
            Instruction::GreaterEqualIntegers(_pos) => ("CMPGE%", None),

            Instruction::EqualStrings(_pos) => ("CMPE$", None),
            Instruction::NotEqualStrings(_pos) => ("CMPNE$", None),
            Instruction::LessStrings(_pos) => ("CMPL$", None),
            Instruction::LessEqualStrings(_pos) => ("CMPLE$", None),
            Instruction::GreaterStrings(_pos) => ("CMPG$", None),
            Instruction::GreaterEqualStrings(_pos) => ("CMPGE$", None),

            Instruction::AddDoubles(_pos) => ("ADD#", None),
            Instruction::SubtractDoubles(_pos) => ("SUB#", None),
            Instruction::MultiplyDoubles(_pos) => ("MUL#", None),
            Instruction::DivideDoubles(_pos) => ("DIV#", None),
            Instruction::ModuloDoubles(_pos) => ("MOD#", None),
            Instruction::PowerDoubles(_pos) => ("POW#", None),
            Instruction::NegateDouble(_pos) => ("NEG#", None),

            Instruction::AddIntegers(_pos) => ("ADD%", None),
            Instruction::SubtractIntegers(_pos) => ("SUB%", None),
            Instruction::MultiplyIntegers(_pos) => ("MUL%", None),
            Instruction::DivideIntegers(_pos) => ("DIV%", None),
            Instruction::ModuloIntegers(_pos) => ("MOD%", None),
            Instruction::PowerIntegers(_pos) => ("POW%", None),
            Instruction::NegateInteger(_pos) => ("NEG%", None),

            Instruction::ConcatStrings(_pos) => ("CONCAT$", None),

            Instruction::ArrayAssignment(key, _pos, nargs) => {
                ("SETA", Some(format!("{}, {}", key, nargs)))
            }

            Instruction::ArrayLoad(key, _pos, nargs) => {
                ("LOADA", Some(format!("{}, {}", key, nargs)))
            }

            Instruction::Assign(key) => ("SETV", Some(key.to_string())),

            Instruction::BuiltinCall(span) => {
                ("CALLB", Some(format!("{} ({}), {}", span.upcall_index, span.name, span.nargs)))
            }

            Instruction::Call(span) => ("CALLA", Some(format!("{:04x}", span.addr))),

            Instruction::FunctionCall(span) => {
                let opcode = match span.return_type {
                    ExprType::Boolean => "CALLF?",
                    ExprType::Double => "CALLF#",
                    ExprType::Integer => "CALLF%",
                    ExprType::Text => "CALLF$",
                };
                (opcode, Some(format!("{} ({}), {}", span.upcall_index, span.name, span.nargs)))
            }

            Instruction::Dim(span) => {
                let opcode = match (span.shared, span.vtype) {
                    (false, ExprType::Boolean) => "DIMV?",
                    (false, ExprType::Double) => "DIMV#",
                    (false, ExprType::Integer) => "DIMV%",
                    (false, ExprType::Text) => "DIMV$",
                    (true, ExprType::Boolean) => "DIMSV?",
                    (true, ExprType::Double) => "DIMSV#",
                    (true, ExprType::Integer) => "DIMSV%",
                    (true, ExprType::Text) => "DIMSV$",
                };
                (opcode, Some(format!("{}", span.name)))
            }

            Instruction::DimArray(span) => {
                let opcode = match (span.shared, span.subtype) {
                    (false, ExprType::Boolean) => "DIMA?",
                    (false, ExprType::Double) => "DIMA#",
                    (false, ExprType::Integer) => "DIMA%",
                    (false, ExprType::Text) => "DIMA$",
                    (true, ExprType::Boolean) => "DIMSA?",
                    (true, ExprType::Double) => "DIMSA#",
                    (true, ExprType::Integer) => "DIMSA%",
                    (true, ExprType::Text) => "DIMSA$",
                };
                (opcode, Some(format!("{}, {}", span.name, span.dimensions)))
            }

            Instruction::End(has_code) => ("END", Some(format!("{}", has_code))),

            Instruction::EnterScope => ("ENTER", None),

            Instruction::DoubleToInteger => ("#TO%", None),
            Instruction::IntegerToDouble => ("%TO#", None),

            Instruction::Jump(span) => ("JMP", Some(format!("{:04x}", span.addr))),
            Instruction::JumpIfDefined(span) => {
                ("JMPVD", Some(format!("{}, {:04x}", span.var, span.addr)))
            }
            Instruction::JumpIfTrue(addr) => ("JMPT", Some(format!("{:04x}", addr))),
            Instruction::JumpIfNotTrue(addr) => ("JMPNT", Some(format!("{:04x}", addr))),

            Instruction::LeaveScope => ("LEAVE", None),

            Instruction::LoadBoolean(key, _pos) => ("LOAD?", Some(key.to_string())),
            Instruction::LoadDouble(key, _pos) => ("LOAD#", Some(key.to_string())),
            Instruction::LoadInteger(key, _pos) => ("LOAD%", Some(key.to_string())),
            Instruction::LoadString(key, _pos) => ("LOAD$", Some(key.to_string())),

            Instruction::LoadRef(key, _etype, _pos) => ("LOADR", Some(key.to_string())),

            Instruction::Nop => ("NOP", None),

            Instruction::PushBoolean(b, _pos) => ("PUSH?", Some(format!("{}", b))),
            Instruction::PushDouble(d, _pos) => ("PUSH#", Some(format!("{}", d))),
            Instruction::PushInteger(i, _pos) => ("PUSH%", Some(format!("{}", i))),
            Instruction::PushString(s, _pos) => ("PUSH$", Some(format!("\"{}\"", s))),

            Instruction::Return(_pos) => ("RET", None),

            Instruction::SetErrorHandler(span) => match span {
                ErrorHandlerISpan::Jump(addr) => ("SEHA", Some(format!("{:04x}", addr))),
                ErrorHandlerISpan::None => ("SEHN", None),
                ErrorHandlerISpan::ResumeNext => ("SEHRN", None),
            },

            Instruction::Unset(span) => ("UNSETV", Some(format!("{}", span.name))),
        }
    }

    /// Returns the position in the source code where this instruction originated.
    ///
    /// For some instructions, we cannot tell their location right now, so we return None for those.
    pub fn pos(&self) -> Option<LineCol> {
        match self {
            Instruction::BitwiseAnd(pos) => Some(*pos),
            Instruction::BitwiseOr(pos) => Some(*pos),
            Instruction::BitwiseXor(pos) => Some(*pos),
            Instruction::BitwiseNot(pos) => Some(*pos),

            Instruction::LogicalAnd(pos) => Some(*pos),
            Instruction::LogicalOr(pos) => Some(*pos),
            Instruction::LogicalXor(pos) => Some(*pos),
            Instruction::LogicalNot(pos) => Some(*pos),

            Instruction::ShiftLeft(pos) => Some(*pos),
            Instruction::ShiftRight(pos) => Some(*pos),

            Instruction::EqualBooleans(pos) => Some(*pos),
            Instruction::NotEqualBooleans(pos) => Some(*pos),

            Instruction::EqualDoubles(pos) => Some(*pos),
            Instruction::NotEqualDoubles(pos) => Some(*pos),
            Instruction::LessDoubles(pos) => Some(*pos),
            Instruction::LessEqualDoubles(pos) => Some(*pos),
            Instruction::GreaterDoubles(pos) => Some(*pos),
            Instruction::GreaterEqualDoubles(pos) => Some(*pos),

            Instruction::EqualIntegers(pos) => Some(*pos),
            Instruction::NotEqualIntegers(pos) => Some(*pos),
            Instruction::LessIntegers(pos) => Some(*pos),
            Instruction::LessEqualIntegers(pos) => Some(*pos),
            Instruction::GreaterIntegers(pos) => Some(*pos),
            Instruction::GreaterEqualIntegers(pos) => Some(*pos),

            Instruction::EqualStrings(pos) => Some(*pos),
            Instruction::NotEqualStrings(pos) => Some(*pos),
            Instruction::LessStrings(pos) => Some(*pos),
            Instruction::LessEqualStrings(pos) => Some(*pos),
            Instruction::GreaterStrings(pos) => Some(*pos),
            Instruction::GreaterEqualStrings(pos) => Some(*pos),

            Instruction::AddDoubles(pos) => Some(*pos),
            Instruction::SubtractDoubles(pos) => Some(*pos),
            Instruction::MultiplyDoubles(pos) => Some(*pos),
            Instruction::DivideDoubles(pos) => Some(*pos),
            Instruction::ModuloDoubles(pos) => Some(*pos),
            Instruction::PowerDoubles(pos) => Some(*pos),
            Instruction::NegateDouble(pos) => Some(*pos),

            Instruction::AddIntegers(pos) => Some(*pos),
            Instruction::SubtractIntegers(pos) => Some(*pos),
            Instruction::MultiplyIntegers(pos) => Some(*pos),
            Instruction::DivideIntegers(pos) => Some(*pos),
            Instruction::ModuloIntegers(pos) => Some(*pos),
            Instruction::PowerIntegers(pos) => Some(*pos),
            Instruction::NegateInteger(pos) => Some(*pos),

            Instruction::ConcatStrings(pos) => Some(*pos),

            Instruction::ArrayAssignment(_, pos, _) => Some(*pos),
            Instruction::ArrayLoad(_, pos, _) => Some(*pos),
            Instruction::Assign(_) => None,
            Instruction::BuiltinCall(span) => Some(span.name_pos),
            Instruction::Call(_) => None,
            Instruction::FunctionCall(span) => Some(span.name_pos),
            Instruction::Dim(_) => None,
            Instruction::DimArray(span) => Some(span.name_pos),
            Instruction::End(_) => None,
            Instruction::EnterScope => None,
            Instruction::DoubleToInteger => None,
            Instruction::IntegerToDouble => None,
            Instruction::Jump(_) => None,
            Instruction::JumpIfDefined(_) => None,
            Instruction::JumpIfTrue(_) => None,
            Instruction::JumpIfNotTrue(_) => None,
            Instruction::LeaveScope => None,
            Instruction::LoadBoolean(_, pos) => Some(*pos),
            Instruction::LoadDouble(_, pos) => Some(*pos),
            Instruction::LoadInteger(_, pos) => Some(*pos),
            Instruction::LoadString(_, pos) => Some(*pos),
            Instruction::LoadRef(_, _, pos) => Some(*pos),
            Instruction::Nop => None,
            Instruction::PushBoolean(_, pos) => Some(*pos),
            Instruction::PushDouble(_, pos) => Some(*pos),
            Instruction::PushInteger(_, pos) => Some(*pos),
            Instruction::PushString(_, pos) => Some(*pos),
            Instruction::Return(pos) => Some(*pos),
            Instruction::SetErrorHandler(_) => None,
            Instruction::Unset(span) => Some(span.pos),
        }
    }

    /// Returns true if this instruction represents the execution of a statement.
    ///
    /// This is a heuristic to implement `ON ERROR RESUME NEXT`.  It works for now without
    /// additional tracking, but maybe this needs to change in the future if we add some
    /// instruction that cannot be disambiguated.
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
            | Instruction::FunctionCall(_)
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
            | Instruction::PushString(_, _)
            | Instruction::EnterScope
            | Instruction::LeaveScope => false,

            Instruction::ArrayAssignment(_, _, _)
            | Instruction::Assign(_)
            | Instruction::BuiltinCall(_)
            | Instruction::Call(_)
            | Instruction::Dim(_)
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
    /// List of builtin upcalls in the order in which they were assigned indexes.
    pub upcalls: Vec<SymbolKey>,

    /// Collection of instructions in the program.
    ///
    /// The indices of this vector correspond to the program counter.
    pub instrs: Vec<Instruction>,

    /// Collection of data values in the program.
    pub data: Vec<Option<Value>>,
}
