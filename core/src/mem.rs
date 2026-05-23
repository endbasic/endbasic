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

/// A typed scalar value, used both in the compile-time constant pool and as a
/// return value when inspecting global variables after execution.
///
/// Only scalar types that can be hashed are included here.  Arrays are never
/// stored as `ConstantDatum`.
#[derive(Clone, Debug)]
pub enum ConstantDatum {
    /// A boolean value.
    Boolean(bool),

    /// A double-precision floating-point value.
    Double(f64),

    /// A 32-bit signed integer value.
    Integer(i32),

    /// A string value.
    Text(String),
}

impl PartialEq for ConstantDatum {
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

impl Eq for ConstantDatum {}

impl Hash for ConstantDatum {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Self::Boolean(b) => b.hash(state),
            Self::Double(d) => d.to_bits().hash(state),
            Self::Integer(i) => i.hash(state),
            Self::Text(s) => s.hash(state),
        }
    }
}

impl From<bool> for ConstantDatum {
    fn from(value: bool) -> Self {
        Self::Boolean(value)
    }
}

impl From<f64> for ConstantDatum {
    fn from(value: f64) -> Self {
        Self::Double(value)
    }
}

impl From<i32> for ConstantDatum {
    fn from(value: i32) -> Self {
        Self::Integer(value)
    }
}

impl From<&str> for ConstantDatum {
    fn from(value: &str) -> Self {
        Self::Text(value.to_owned())
    }
}

impl From<String> for ConstantDatum {
    fn from(value: String) -> Self {
        Self::Text(value)
    }
}

impl ConstantDatum {
    /// Returns the type of the constant datum.
    pub(crate) fn etype(&self) -> ExprType {
        match self {
            Self::Boolean(..) => ExprType::Boolean,
            Self::Double(..) => ExprType::Double,
            Self::Integer(..) => ExprType::Integer,
            Self::Text(..) => ExprType::Text,
        }
    }

    /// Formats this value as EndBASIC source code.
    pub fn as_source(&self) -> String {
        match self {
            Self::Boolean(v) => {
                if *v {
                    "TRUE".to_owned()
                } else {
                    "FALSE".to_owned()
                }
            }
            Self::Double(v) => {
                let mut s = format!("{}", v);
                if !s.contains('.') && !s.contains('e') && !s.contains('E') {
                    s.push_str(".0");
                }
                s
            }
            Self::Integer(v) => format!("{}", v),
            Self::Text(v) => format!("\"{}\"", v.replace('"', "\"\"")),
        }
    }

    /// Formats this value for display in disassembly output.
    pub(crate) fn as_disassembly(&self) -> String {
        match self {
            Self::Boolean(v) => {
                if *v {
                    "TRUE".to_owned()
                } else {
                    "FALSE".to_owned()
                }
            }
            Self::Double(v) => v.to_string(),
            Self::Integer(v) => format!("{}", v),
            Self::Text(v) => format!("\"{}\"", v.replace('"', "\"\"")),
        }
    }

    /// Decodes a raw register `value` of `etype` into a constant datum.
    pub(crate) fn from_raw(
        value: u64,
        etype: ExprType,
        constants: &[ConstantDatum],
        heap: &Heap,
    ) -> Self {
        match etype {
            ExprType::Boolean => Self::Boolean(value != 0),
            ExprType::Double => Self::Double(f64::from_bits(value)),
            ExprType::Integer => Self::Integer(value as i32),
            ExprType::Text => {
                let ptr = DatumPtr::from(value);
                Self::Text(ptr.resolve_string(constants, heap).to_owned())
            }
        }
    }
}

/// A heap-allocated value used at runtime.
///
/// Only types that require heap allocation are included here.  Scalars other than
/// `Text` live directly in registers and never appear on the heap.
#[derive(Clone, Debug)]
pub(crate) enum HeapDatum {
    /// An array value.
    Array(ArrayData),

    /// A string value.
    Text(String),
}

/// Error reported when the heap cannot grow any further.
#[derive(Debug, thiserror::Error)]
#[error("Out of heap space")]
pub(crate) struct HeapOverflowError;

/// Heap-allocated data used at runtime.
pub(crate) struct Heap {
    data: Vec<HeapDatum>,
    max_entries: U24,
}

impl Heap {
    /// Creates a new empty heap.
    pub(crate) fn new(max_entries: U24) -> Self {
        Self { data: vec![HeapDatum::Text(String::new())], max_entries }
    }

    /// Removes all entries from the heap.
    pub(crate) fn clear(&mut self) {
        *self = Self::new(self.max_entries);
    }

    /// Returns the number of entries in the heap.
    pub(crate) fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns the pointer to the shared empty string.
    pub(crate) fn empty_text_ptr(&self) -> u64 {
        debug_assert!(matches!(self.data.first(), Some(HeapDatum::Text(s)) if s.is_empty()));
        DatumPtr::for_heap(0)
    }

    /// Allocates `datum` in the heap and returns its pointer.
    pub(crate) fn push(&mut self, datum: HeapDatum) -> Result<u64, HeapOverflowError> {
        if matches!(&datum, HeapDatum::Text(s) if s.is_empty()) {
            return Ok(self.empty_text_ptr());
        }

        let index = U24::try_from(self.len()).map_err(|_| HeapOverflowError)?;
        if self.len() >= unchecked_u24_as_usize(self.max_entries) {
            return Err(HeapOverflowError);
        }
        self.data.push(datum);
        Ok(DatumPtr::for_heap(u32::from(index)))
    }

    /// Returns the heap entry at `index`.
    pub(crate) fn get(&self, index: usize) -> &HeapDatum {
        &self.data[index]
    }

    /// Returns the heap entry at `index` for mutation.
    pub(crate) fn get_mut(&mut self, index: usize) -> &mut HeapDatum {
        &mut self.data[index]
    }
}

/// Tagged pointers for constant and heap addresses.
///
/// A `DatumPtr` indexes into the constant pool or the heap, where datum values live.
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

    /// Resolves this pointer and returns the string it points to.
    ///
    /// Panics if the pointed-to datum is not a `Text` value.
    pub(crate) fn resolve_string<'b>(
        &self,
        constants: &'b [ConstantDatum],
        heap: &'b Heap,
    ) -> &'b str {
        match self {
            DatumPtr::Constant(index) => match &constants[unchecked_u24_as_usize(*index)] {
                ConstantDatum::Text(s) => s,
                _ => panic!("Constant pointer does not point to a Text value"),
            },
            DatumPtr::Heap(index) => match heap.get(unchecked_u24_as_usize(*index)) {
                HeapDatum::Text(s) => s,
                _ => panic!("Heap pointer does not point to a Text value"),
            },
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constant_datum_from_scalars() {
        assert_eq!(ConstantDatum::Boolean(true), ConstantDatum::from(true));
        assert_eq!(ConstantDatum::Double(3.25), ConstantDatum::from(3.25));
        assert_eq!(ConstantDatum::Integer(-7), ConstantDatum::from(-7));
    }

    #[test]
    fn test_constant_datum_from_str() {
        let mut text = "hello".to_owned();
        let datum = ConstantDatum::from(text.as_str());
        text.clear();

        assert_eq!(ConstantDatum::Text("hello".to_owned()), datum);
    }

    #[test]
    fn test_constant_datum_from_string() {
        assert_eq!(
            ConstantDatum::Text("hello".to_owned()),
            ConstantDatum::from("hello".to_owned())
        );
    }

    #[test]
    fn test_constant_datum_from_raw() {
        assert_eq!(
            ConstantDatum::Boolean(true),
            ConstantDatum::from_raw(1, ExprType::Boolean, &[], &Heap::new(U24::from(64)))
        );
        assert_eq!(
            ConstantDatum::Double(3.25),
            ConstantDatum::from_raw(
                3.25f64.to_bits(),
                ExprType::Double,
                &[],
                &Heap::new(U24::from(64))
            )
        );
        assert_eq!(
            ConstantDatum::Integer(-7),
            ConstantDatum::from_raw(
                (-7i32) as u64,
                ExprType::Integer,
                &[],
                &Heap::new(U24::from(64))
            )
        );

        let constants = vec![ConstantDatum::Text("hello".to_owned())];
        assert_eq!(
            ConstantDatum::Text("hello".to_owned()),
            ConstantDatum::from_raw(0, ExprType::Text, &constants, &Heap::new(U24::from(64)))
        );
    }
}
