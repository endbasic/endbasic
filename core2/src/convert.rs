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

/// Does a native cast from `Self` to `T`.
pub(crate) trait Cast<T> {
    fn cast(self) -> T;
}

/// Implements `Cast` for two types, bidirectionally.
macro_rules! impl_cast {
    ( $ty1:ty ) => {
        impl Cast<$ty1> for $ty1 {
            fn cast(self) -> $ty1 {
                self as $ty1
            }
        }
    };

    ( $ty1:ty, $ty2:ty ) => {
        impl Cast<$ty1> for $ty2 {
            fn cast(self) -> $ty1 {
                self as $ty1
            }
        }

        impl Cast<$ty2> for $ty1 {
            fn cast(self) -> $ty2 {
                self as $ty2
            }
        }
    };
}

impl_cast!(i16, u32);
impl_cast!(u16, u32);
impl_cast!(u8, u32);
impl_cast!(u8, usize);
impl_cast!(usize, u32);
impl_cast!(usize);

/// Casts `value` to `T`.
///
/// In debug mode, this performs the cast with range checks and panics if the conversion
/// is not possible.
///
/// In release mode, this performs a native integer cast without checks.
pub(crate) fn cast<T, V>(value: V) -> T
where
    T: TryFrom<V>,
    <T as TryFrom<V>>::Error: std::fmt::Debug,
    V: Cast<T>,
{
    if cfg!(debug_assertions) { T::try_from(value).unwrap() } else { Cast::<T>::cast(value) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cast() {
        assert_eq!(10u8, cast(10u32));
    }
}
