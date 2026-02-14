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

//! Efficient conversion utilities with diagnostics.

use std::convert::TryFrom;
use std::num::TryFromIntError;

/// An unsigned integer constrained to 24 bits.
#[derive(Clone, Copy)]
pub(crate) struct U24(u32);

impl TryFrom<u32> for U24 {
    type Error = ();

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        if value >= (1 << 24) { Err(()) } else { Ok(Self(value)) }
    }
}

impl TryFrom<U24> for usize {
    type Error = TryFromIntError;

    fn try_from(value: U24) -> Result<Self, Self::Error> {
        Self::try_from(value.0)
    }
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
impl_unchecked_cast!(unchecked_usize_as_u32, usize, u32, primitive);

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
    fn test_unchecked_usize_as_u32() {
        assert_eq!(10u32, unchecked_usize_as_u32(10_usize));
    }

    #[test]
    fn test_unchecked_u24_as_usize() {
        assert_eq!(10_usize, unchecked_u24_as_usize(U24(10)));
    }
}
