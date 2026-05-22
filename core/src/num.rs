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

//! Efficient conversion utilities with diagnostics.

use std::convert::TryFrom;
use std::num::TryFromIntError;

/// An unsigned integer constrained to 24 bits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct U24(u32);

impl From<u16> for U24 {
    fn from(value: u16) -> Self {
        Self(u32::from(value))
    }
}

impl TryFrom<u32> for U24 {
    type Error = ();

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        if value >= (1 << 24) { Err(()) } else { Ok(Self(value)) }
    }
}

impl TryFrom<usize> for U24 {
    type Error = ();

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        if value >= (1 << 24) { Err(()) } else { Ok(Self(value as u32)) }
    }
}

impl From<U24> for u32 {
    fn from(value: U24) -> Self {
        value.0
    }
}

impl TryFrom<U24> for usize {
    type Error = TryFromIntError;

    fn try_from(value: U24) -> Result<Self, Self::Error> {
        Self::try_from(value.0)
    }
}

impl U24 {
    /// Maximum value that a `U24` can carry.
    pub(crate) const MAX: U24 = U24(1 << 24);
}

/// A trait to perform an unchecked cast from one type to another.
trait UncheckedFrom {
    /// The source type to convert from.
    type T;

    /// Converts `value` to `Self`.
    ///
    /// Must be implemented as an `as` cast in release builds but can do extra
    /// sanity-checking in debug builds.
    fn unchecked_from(value: Self::T) -> Self;
}

/// Implements an unchecked conversion function between two integer types.
///
/// In debug mode, this asserts that the input value fits in the return type.
/// In release mode, this makes the conversion with truncation.
macro_rules! impl_unchecked_cast {
    ( $name:ident, $from_ty:ty, $to_ty:ty, primitive ) => {
        pub(crate) fn $name(value: $from_ty) -> $to_ty {
            if cfg!(debug_assertions) {
                <$to_ty>::try_from(value).unwrap()
            } else {
                value as $to_ty
            }
        }
    };

    ( $name:ident, $from_ty:ty, $to_ty:ty, user_defined ) => {
        pub(crate) fn $name(value: $from_ty) -> $to_ty {
            if cfg!(debug_assertions) {
                <$to_ty>::try_from(value).unwrap()
            } else {
                <$to_ty>::unchecked_from(value)
            }
        }
    };
}

impl_unchecked_cast!(unchecked_u32_as_u8, u32, u8, primitive);
impl_unchecked_cast!(unchecked_u32_as_u16, u32, u16, primitive);
impl_unchecked_cast!(unchecked_u32_as_usize, u32, usize, primitive);
impl_unchecked_cast!(unchecked_u64_as_u8, u64, u8, primitive);
impl_unchecked_cast!(unchecked_usize_as_u8, usize, u8, primitive);

impl UncheckedFrom for usize {
    type T = U24;

    fn unchecked_from(value: Self::T) -> Self {
        value.0 as Self
    }
}

impl_unchecked_cast!(unchecked_u24_as_usize, U24, usize, user_defined);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unchecked_u32_as_u8() {
        assert_eq!(10u8, unchecked_u32_as_u8(10u32));
    }

    #[test]
    fn test_unchecked_u32_as_u16() {
        assert_eq!(10u16, unchecked_u32_as_u16(10u32));
    }

    #[test]
    fn test_unchecked_u32_as_usize() {
        assert_eq!(10usize, unchecked_u32_as_usize(10u32));
    }

    #[test]
    fn test_unchecked_u64_as_u8() {
        assert_eq!(10u8, unchecked_u64_as_u8(10u64));
    }

    #[test]
    fn test_unchecked_usize_as_u8() {
        assert_eq!(10u8, unchecked_usize_as_u8(10_usize));
    }

    #[test]
    fn test_unchecked_u24_as_usize() {
        assert_eq!(10_usize, unchecked_u24_as_usize(U24(10)));
    }
}
