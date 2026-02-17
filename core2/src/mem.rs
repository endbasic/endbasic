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

//! Memory representation and related types.

use crate::ExprType;
use crate::num::{U24, unchecked_u24_as_usize};
use std::convert::TryFrom;
use std::hash::Hash;

/// Data for a multidimensional array stored on the heap.
#[derive(Clone, Debug)]
pub(crate) struct ArrayData {
    /// Size of each dimension.
    pub(crate) dimensions: Vec<usize>,

    /// Flattened row-major storage of element values as `u64` (matching register representation).
    pub(crate) values: Vec<u64>,
}

impl ArrayData {
    /// Computes the flat index into `values` for the given `subscripts`, with bounds checking.
    pub(crate) fn flat_index(&self, subscripts: &[i32]) -> Result<usize, String> {
        debug_assert_eq!(
            subscripts.len(),
            self.dimensions.len(),
            "Invalid number of subscripts; guaranteed valid by the compiler"
        );

        let mut offset = 0;
        let mut multiplier = 1;
        for (s, d) in subscripts.iter().zip(&self.dimensions) {
            let Ok(s) = usize::try_from(*s) else {
                return Err(format!("Subscript {} cannot be negative", s));
            };
            if s >= *d {
                return Err(format!("Subscript {} exceeds limit of {}", s, d));
            }
            offset += s * multiplier;
            multiplier *= d;
        }
        Ok(offset)
    }
}

/// A single value in the EndBASIC language.
#[derive(Clone, Debug)]
pub(crate) enum Datum {
    /// An array value.
    Array(ArrayData),

    /// A boolean value.
    Boolean(bool),

    /// A double-precision floating-point value.
    Double(f64),

    /// A 32-bit signed integer value.
    Integer(i32),

    /// A string value.
    Text(String),
}

impl PartialEq for Datum {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Boolean(a), Self::Boolean(b)) => a == b,
            (Self::Double(a), Self::Double(b)) => a.to_bits() == b.to_bits(),
            (Self::Integer(a), Self::Integer(b)) => a == b,
            (Self::Text(a), Self::Text(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for Datum {}

impl Hash for Datum {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Self::Array(_) => panic!("Arrays cannot be hashed"),
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
            Self::Array(..) => panic!("Arrays do not have a simple ExprType"),
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

    /// Extracts the heap index from this pointer.
    ///
    /// Panics if this is not a heap pointer.
    pub(crate) fn heap_index(&self) -> usize {
        match self {
            DatumPtr::Heap(index) => unchecked_u24_as_usize(*index),
            DatumPtr::Constant(_) => panic!("Expected a heap pointer"),
        }
    }
}
