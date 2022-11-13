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

/// Convenience type to represent a program address.
pub type Address = usize;

/// Components of an unconditional jump instruction.
#[derive(Debug, Eq, PartialEq)]
pub struct JumpSpan {
    /// The address to jump to.
    pub addr: Address,
}

/// Components of a conditional jump that depends on whether a variable is defined.
#[cfg_attr(test, derive(Debug, Eq, PartialEq))]
pub struct JumpIfDefinedSpan {
    /// The variable to check for nonexistence.
    pub var: String,

    /// The address to jump to.
    pub addr: Address,
}

/// Components of a conditional jump that depends on whether an expression is not true.
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct JumpIfNotTrueSpan {
    /// The condition to check for falseness.
    pub cond: Expr,

    /// The address to jump to.
    pub addr: Address,

    /// The message to emit if the condition is not boolean.
    pub error_msg: &'static str,
}

/// Representation of all possible instructions in the bytecode.
#[cfg_attr(test, derive(Debug, PartialEq))]
pub enum Instruction {
    /// Represents an assignment to an element of an array.
    ArrayAssignment(ArrayAssignmentSpan),

    /// Represents a variable assignment.
    Assignment(AssignmentSpan),

    /// Represents a call to a builtin command such as `PRINT`.
    BuiltinCall(BuiltinCallSpan),

    /// Represents a variable definition.
    Dim(DimSpan),

    /// Represents an array definition.
    DimArray(DimArraySpan),

    /// Represents an unconditional jump.
    Jump(JumpSpan),

    /// Represents an conditional jump that jumps if the variable is defined.
    JumpIfDefined(JumpIfDefinedSpan),

    /// Represents an conditional jump that jumps if the condition is not met.
    JumpIfNotTrue(JumpIfNotTrueSpan),

    /// Represents an instruction that does nothing.
    Nop,
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
