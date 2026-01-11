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

//! ID generators.

use std::collections::HashMap;
use std::hash::Hash;

/// Trait to convert an usize to a narrower integer type.
pub(super) trait IdConverter: Sized {
    fn convert(v: usize) -> Self;
}

impl IdConverter for usize {
    fn convert(v: usize) -> Self {
        v
    }
}

impl IdConverter for u16 {
    fn convert(v: usize) -> Self {
        debug_assert!(v <= (u16::MAX as usize));
        v as u16
    }
}

impl IdConverter for u8 {
    fn convert(v: usize) -> Self {
        debug_assert!(v <= (u8::MAX as usize));
        v as u8
    }
}

/// Data structure with O(1) lookup and insertion that assigns sequential identifiers to
/// elements as they are inserted and allows later retrieval of these identifiers and
/// allows retrieving the inserted values in insertion order.
pub(super) struct IdAssigner<T, I> {
    map: HashMap<T, I>,
}

impl<T, I> Default for IdAssigner<T, I> {
    fn default() -> Self {
        Self { map: HashMap::default() }
    }
}

impl<T: Clone + Eq + Hash, I: Copy + Ord + IdConverter> IdAssigner<T, I> {
    /// Gets the identifier for a `key`, assigning one if the `key` does not yet have one.
    // DO NOT SUBMIT: This should take something else to support both &T and T as input...
    // I tried Into<Cow> but couldn't get it to work.
    pub(super) fn get(&mut self, key: &T) -> I {
        if let Some(index) = self.map.get(key) {
            *index
        } else {
            let index = I::convert(self.map.len());
            self.map.insert(key.clone(), index);
            index
        }
    }

    /// Returns the number of assigned identifiers.
    pub(super) fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns the keys in insertion order.
    pub(super) fn to_vec(self) -> Vec<T> {
        let mut reverse = self.map.into_iter().collect::<Vec<(T, I)>>();
        reverse.sort_by_key(|(_value, index)| *index);
        reverse.into_iter().map(|(value, _index)| value).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_id_assigner_with_u8_ids() {
        let mut map = IdAssigner::<&'static str, u8>::new(0);

        assert_eq!(0, map.get("foo"));
        assert_eq!(1, map.get("bar"));
        assert_eq!(2, map.get("baz"));

        assert_eq!(1, map.get("bar"));

        assert_eq!(["foo", "bar", "baz"], map.to_vec().as_slice());
    }

    #[test]
    fn test_id_assigner_with_usize_ids() {
        let mut map = IdAssigner::<&'static str, usize>::new(0);

        assert_eq!(0, map.get("foo"));
        assert_eq!(1, map.get("bar"));
        assert_eq!(2, map.get("baz"));

        assert_eq!(1, map.get("bar"));

        assert_eq!(["foo", "bar", "baz"], map.to_vec().as_slice());
    }
}
