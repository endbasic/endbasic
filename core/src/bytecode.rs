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

use crate::ast::*;
use crate::reader::LineCol;
use std::borrow::Cow;

/// Convenience type to represent a program address.
pub type Address = usize;

/// Components of an array definition.
#[derive(Debug, PartialEq)]
#[cfg_attr(test, derive(Clone))]
pub struct DimArrayISpan {
    /// Name of the array to define.  Type annotations are not allowed, hence why this is not a
    /// `VarRef`.
    pub name: String,

    /// Position of the name.
    pub name_pos: LineCol,

    /// Number of values in the stack representing the dimensions of the array.
    pub dimensions: usize,

    /// Type of the array to be defined.
    pub subtype: VarType,

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
    pub var: String,

    /// The address to jump to.
    pub addr: Address,
}

/// Components of a conditional jump that depends on a boolean expression.
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct JumpIfBoolISpan {
    /// The address to jump to.
    pub addr: Address,

    /// The message to emit if the condition is not boolean.
    pub error_msg: &'static str,
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
    pub name: String,

    /// Position of where this instruction was requested.
    pub pos: LineCol,
}

/// Representation of all possible instructions in the bytecode.
#[cfg_attr(test, derive(Debug, PartialEq))]
pub enum Instruction {
    /// Represents a binary "and" operation.
    And(LineCol),

    /// Represents a binary "or" operation.
    Or(LineCol),

    /// Represents a binary "xor" operation.
    Xor(LineCol),

    /// Represents a unary "nor" operation.
    Not(LineCol),

    /// Represents a left bitshift.
    ShiftLeft(LineCol),

    /// Represents a right bitshift.
    ShiftRight(LineCol),

    /// Represents an equality comparison.
    Equal(LineCol),

    /// Represents an inequality comparison.
    NotEqual(LineCol),

    /// Represents a less-than comparison.
    Less(LineCol),

    /// Represents a less-or-equal comparison.
    LessEqual(LineCol),

    /// Represents a greater-than comparison.
    Greater(LineCol),

    /// Represents a greater-or-equal comparison.
    GreaterEqual(LineCol),

    /// Represents an arithmetic addition operation.
    Add(LineCol),

    /// Represents an arithmetic subtraction operation.
    Subtract(LineCol),

    /// Represents an arithmetic multiplication operation.
    Multiply(LineCol),

    /// Represents an arithmetic division operation.
    Divide(LineCol),

    /// Represents an arithmetic modulo operation.
    Modulo(LineCol),

    /// Represents an arithmetic power operation.
    Power(LineCol),

    /// Represents an arithmetic sign flip operation.
    Negate(LineCol),

    /// Represents an assignment to an element of an array with the given number of subscripts.
    ArrayAssignment(VarRef, LineCol, usize),

    /// Represents an assignment of a value to a variable.
    Assign(VarRef, LineCol),

    /// Represents a call to a builtin command such as `PRINT` with the given number of arguments.
    ///
    /// The arguments in the stack are interspersed with the separators used to separate them from.
    /// each other, because those separators have meaning.
    BuiltinCall(VarRef, LineCol, usize),

    /// Represents an unconditional call to a location that will return.
    Call(JumpISpan),

    /// Represents a call to the given function with the given number of arguments.
    FunctionCall(VarRef, LineCol, usize),

    /// Represents a variable definition.
    Dim(DimSpan),

    /// Represents an array definition.
    DimArray(DimArrayISpan),

    /// Represents a request to terminate the program.  If the boolean is true, the exit ode is
    /// at the top of the stack.
    End(bool),

    /// Represents an unconditional jump.
    Jump(JumpISpan),

    /// Represents an conditional jump that jumps if the variable is defined.
    JumpIfDefined(JumpIfDefinedISpan),

    /// Represents an conditional jump that jumps if the condition is met.
    JumpIfTrue(JumpIfBoolISpan),

    /// Represents an conditional jump that jumps if the condition is not met.
    JumpIfNotTrue(JumpIfBoolISpan),

    /// Represents a load of a variable's value from main memory into the stack.
    Load(VarRef, LineCol),

    /// Represents a load of a variable's reference into the stack.
    LoadRef(VarRef, LineCol),

    /// Represents an instruction that does nothing.
    Nop,

    /// Represents a load of a literal value into the top of the stack.
    Push(Value, LineCol),

    /// Represents a return after a call.
    Return(LineCol),

    /// Represents a change in the error handler state.
    SetErrorHandler(ErrorHandlerISpan),

    /// Represents a request to unset a variable.
    Unset(UnsetISpan),
}

impl Instruction {
    /// Returns the textual representation of the instruction.
    pub fn repr(&self) -> Cow<'static, str> {
        match self {
            Instruction::And(_pos) => Cow::from("and"),
            Instruction::Or(_pos) => Cow::from("or"),
            Instruction::Xor(_pos) => Cow::from("xor"),
            Instruction::Not(_pos) => Cow::from("not"),
            Instruction::ShiftLeft(_pos) => Cow::from("shl"),
            Instruction::ShiftRight(_pos) => Cow::from("shr"),
            Instruction::Equal(_pos) => Cow::from("cmpe"),
            Instruction::NotEqual(_pos) => Cow::from("cmpne"),
            Instruction::Less(_pos) => Cow::from("cmpl"),
            Instruction::LessEqual(_pos) => Cow::from("cmple"),
            Instruction::Greater(_pos) => Cow::from("cmpg"),
            Instruction::GreaterEqual(_pos) => Cow::from("cmpge"),
            Instruction::Add(_pos) => Cow::from("add"),
            Instruction::Subtract(_pos) => Cow::from("sub"),
            Instruction::Multiply(_pos) => Cow::from("mul"),
            Instruction::Divide(_pos) => Cow::from("div"),
            Instruction::Modulo(_pos) => Cow::from("mod"),
            Instruction::Power(_pos) => Cow::from("pow"),
            Instruction::Negate(_pos) => Cow::from("neg"),
            Instruction::ArrayAssignment(vref, _pos, nargs) => {
                Cow::from(format!("seta {}, {}", vref, nargs))
            }
            Instruction::Assign(vref, _pos) => Cow::from(format!("setv {}", vref)),
            Instruction::BuiltinCall(vref, _pos, nargs) => {
                Cow::from(format!("callb {}, {}", vref, nargs))
            }
            Instruction::Call(span) => Cow::from(format!("calla {:04x}", span.addr)),
            Instruction::FunctionCall(vref, _pos, nargs) => {
                Cow::from(format!("callf {}, {}", vref, nargs))
            }
            Instruction::Dim(span) => Cow::from(format!("dimv {}, {}", span.name, span.vtype)),
            Instruction::DimArray(span) => {
                Cow::from(format!("dima {}, {}, {}", span.name, span.dimensions, span.subtype))
            }
            Instruction::End(has_code) => Cow::from(format!("end {}", has_code)),
            Instruction::Jump(span) => Cow::from(format!("jmp {:04x}", span.addr)),
            Instruction::JumpIfDefined(span) => {
                Cow::from(format!("jmpvd {}, {:04x}", span.var, span.addr))
            }
            Instruction::JumpIfTrue(span) => {
                Cow::from(format!("jmpt {:04x}, \"{}\"", span.addr, span.error_msg))
            }
            Instruction::JumpIfNotTrue(span) => {
                Cow::from(format!("jmpnt {:04x}, \"{}\"", span.addr, span.error_msg))
            }
            Instruction::Load(vref, _pos) => Cow::from(format!("loadv {}", vref)),
            Instruction::LoadRef(vref, _pos) => Cow::from(format!("loadr {}", vref)),
            Instruction::Nop => Cow::from("nop"),
            Instruction::Push(value, _pos) => Cow::from(format!("pushv {}", value)),
            Instruction::Return(_pos) => Cow::from("ret"),
            Instruction::SetErrorHandler(span) => match span {
                ErrorHandlerISpan::Jump(addr) => Cow::from(format!("seha {:04x}", addr)),
                ErrorHandlerISpan::None => Cow::from("sehn"),
                ErrorHandlerISpan::ResumeNext => Cow::from("sehrn"),
            },
            Instruction::Unset(span) => Cow::from(format!("unsetv {}", span.name)),
        }
    }

    /// Returns the position in the source code where this instruction originated.
    ///
    /// For some instructions, we cannot tell their location right now, so we return None for those.
    pub fn pos(&self) -> Option<LineCol> {
        match self {
            Instruction::And(pos) => Some(*pos),
            Instruction::Or(pos) => Some(*pos),
            Instruction::Xor(pos) => Some(*pos),
            Instruction::Not(pos) => Some(*pos),
            Instruction::ShiftLeft(pos) => Some(*pos),
            Instruction::ShiftRight(pos) => Some(*pos),
            Instruction::Equal(pos) => Some(*pos),
            Instruction::NotEqual(pos) => Some(*pos),
            Instruction::Less(pos) => Some(*pos),
            Instruction::LessEqual(pos) => Some(*pos),
            Instruction::Greater(pos) => Some(*pos),
            Instruction::GreaterEqual(pos) => Some(*pos),
            Instruction::Add(pos) => Some(*pos),
            Instruction::Subtract(pos) => Some(*pos),
            Instruction::Multiply(pos) => Some(*pos),
            Instruction::Divide(pos) => Some(*pos),
            Instruction::Modulo(pos) => Some(*pos),
            Instruction::Power(pos) => Some(*pos),
            Instruction::Negate(pos) => Some(*pos),
            Instruction::ArrayAssignment(_, pos, _) => Some(*pos),
            Instruction::Assign(_, pos) => Some(*pos),
            Instruction::BuiltinCall(_, pos, _) => Some(*pos),
            Instruction::Call(_) => None,
            Instruction::FunctionCall(_, pos, _) => Some(*pos),
            Instruction::Dim(span) => Some(span.name_pos),
            Instruction::DimArray(span) => Some(span.name_pos),
            Instruction::End(_) => None,
            Instruction::Jump(_) => None,
            Instruction::JumpIfDefined(_) => None,
            Instruction::JumpIfTrue(_) => None,
            Instruction::JumpIfNotTrue(_) => None,
            Instruction::Load(_, pos) => Some(*pos),
            Instruction::LoadRef(_, pos) => Some(*pos),
            Instruction::Nop => None,
            Instruction::Push(_, pos) => Some(*pos),
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
            Instruction::And(_)
            | Instruction::Or(_)
            | Instruction::Xor(_)
            | Instruction::Not(_)
            | Instruction::ShiftLeft(_)
            | Instruction::ShiftRight(_)
            | Instruction::Equal(_)
            | Instruction::NotEqual(_)
            | Instruction::Less(_)
            | Instruction::LessEqual(_)
            | Instruction::Greater(_)
            | Instruction::GreaterEqual(_)
            | Instruction::Add(_)
            | Instruction::Subtract(_)
            | Instruction::Multiply(_)
            | Instruction::Divide(_)
            | Instruction::Modulo(_)
            | Instruction::Power(_)
            | Instruction::Negate(_)
            | Instruction::FunctionCall(_, _, _)
            | Instruction::Load(_, _)
            | Instruction::LoadRef(_, _)
            | Instruction::Push(_, _) => false,

            Instruction::ArrayAssignment(_, _, _)
            | Instruction::Assign(_, _)
            | Instruction::BuiltinCall(_, _, _)
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
    /// Collection of instructions in the program.
    ///
    /// The indices of this vector correspond to the program counter.
    pub instrs: Vec<Instruction>,

    /// Collection of data values in the program.
    pub data: Vec<Option<Value>>,
}
