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

//! Memory representation and related types.

use crate::ExprType;
use crate::num::{U24, unchecked_u24_as_usize};
use std::convert::TryFrom;
use std::hash::Hash;

/// A single value in the EndBASIC language.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Datum {
    /// A boolean value.
    Boolean(bool),

    /// A double-precision floating-point value.
    Double(f64),

    /// A 32-bit signed integer value.
    Integer(i32),

    /// A string value.
    Text(String),
}

impl Eq for Datum {}

impl Hash for Datum {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::Boolean(b) => b.hash(state),
            Self::Double(d) => d.to_bits().hash(state),
            Self::Integer(i) => i.hash(state),
            Self::Text(s) => s.hash(state),
        }
    }
}

impl Datum {
    /// Creates a new datum of `etype` with a default value.
    pub(crate) fn new(etype: ExprType) -> Self {
        match etype {
            ExprType::Boolean => Datum::Boolean(false),
            ExprType::Double => Datum::Double(0.0),
            ExprType::Integer => Datum::Integer(0),
            ExprType::Text => Datum::Text(String::new()),
        }
    }

    /// Returns the type of the datum.
    pub(crate) fn etype(&self) -> ExprType {
        match self {
            Self::Boolean(..) => ExprType::Boolean,
            Self::Double(..) => ExprType::Double,
            Self::Integer(..) => ExprType::Integer,
            Self::Text(..) => ExprType::Text,
        }
    }
}

/// Tagged pointers for constant and heap addresses.
///
/// A `DatumPtr` indexes into the constant pool or the heap, where `Datum` values live.
/// The encoding uses the sign of the lower 32 bits of a `u64`: positive values are
/// constant pool indices, and negative values (two's complement) are heap indices.
///
/// This is distinct from `TaggedRegisterRef`, which points to a register in the register
/// file rather than to data storage.
#[derive(Clone, Copy)]
pub(crate) enum DatumPtr {
    /// A pointer to an entry in the constants pool.
    Constant(U24),

    /// A pointer to an entry in the heap.
    Heap(U24),
}

impl From<u64> for DatumPtr {
    fn from(value: u64) -> Self {
        let signed_value = value as i32;
        if signed_value < 0 {
            DatumPtr::Heap(U24::try_from((-signed_value - 1) as u32).unwrap())
        } else {
            DatumPtr::Constant(U24::try_from(signed_value as u32).unwrap())
        }
    }
}

impl DatumPtr {
    /// Creates a new pointer for a heap `index` and returns its `u64` representation.
    pub(crate) fn for_heap(index: u32) -> u64 {
        let raw = index as i32;
        let raw = -raw - 1;
        raw as u64
    }

    /// Gets the datum pointed to by this pointer from the `constants` and `heap`.
    pub(crate) fn resolve<'b>(&self, constants: &'b [Datum], heap: &'b [Datum]) -> &'b Datum {
        match self {
            DatumPtr::Constant(index) => &constants[unchecked_u24_as_usize(*index)],
            DatumPtr::Heap(index) => &heap[unchecked_u24_as_usize(*index)],
        }
    }
}
