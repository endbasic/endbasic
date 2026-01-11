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
use std::convert::TryFrom;
use std::hash::Hash;

/// Hash map that assigns sequential identifiers to elements as they are inserted and
/// allows later retrieval of these identifiers and retrieving the inserted values in
/// insertion order.
pub(super) struct HashMapWithIds<K, V, I> {
    /// The underlying storage mapping keys to their values and assigned identifiers.
    map: HashMap<K, (V, I)>,
}

impl<K, V, I> Default for HashMapWithIds<K, V, I> {
    fn default() -> Self {
        Self { map: HashMap::default() }
    }
}

impl<K, V, I> HashMapWithIds<K, V, I>
where
    K: Clone + Eq + Hash,
    I: Copy + std::fmt::Debug + Ord + TryFrom<usize>,
    V: Copy + std::fmt::Debug + PartialEq,
{
    /// Gets the value and identifier for a `key`.
    ///
    /// Returns `None` if the key is not present.
    pub(super) fn get(&self, key: &K) -> Option<(&V, I)> {
        self.map.get(key).map(|(v, i)| (v, *i))
    }

    /// Gets mutable access to the value and identifier for a `key`.
    ///
    /// Returns `None` if the key is not present.
    pub(super) fn get_mut(&mut self, key: &K) -> Option<(&mut V, I)> {
        self.map.get_mut(key).map(|(v, i)| (v, *i))
    }

    /// Inserts the `key`/`value` pair into the hash map, assigning a new identifier
    /// to the `key` if it does not yet have one.
    ///
    /// If the `key` is already present, returns a pair with the previous value and the already
    /// assigned identifier.  If the `keys` is not yet present, returns a pair with None and the
    /// newly-assigned identifier.
    ///
    /// Returns `None` when the IDs run out.
    pub(super) fn insert(&mut self, key: K, value: V) -> Option<(Option<V>, I)> {
        let id = match self.map.get(&key) {
            Some((_value, id)) => *id,
            None => match I::try_from(self.map.len()) {
                Ok(id) => id,
                Err(_) => return None,
            },
        };
        self.map
            .insert(key, (value, id))
            .map(|(prev_value, prev_id)| {
                debug_assert_eq!(prev_id, id);
                (Some(prev_value), id)
            })
            .or(Some((None, id)))
    }

    /// Returns the number of assigned identifiers.
    pub(super) fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns the keys in insertion order.
    pub(super) fn keys_to_vec(self) -> Vec<K> {
        let mut reverse = self.map.into_iter().collect::<Vec<(K, (V, I))>>();
        reverse.sort_by_key(|(_key, (_value, index))| *index);
        reverse.into_iter().map(|(key, _index)| key).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hash_map_with_ids_basic_hashmap_api() {
        let mut map = HashMapWithIds::<&'static str, &'static str, u8>::default();

        assert_eq!(Some((None, 0)), map.insert("first", "v1"));
        assert_eq!(Some((None, 1)), map.insert("second", "v2"));

        assert_eq!(Some((&"v1", 0)), map.get(&"first"));
        assert_eq!(Some((&"v2", 1)), map.get(&"second"));
        assert_eq!(None, map.get(&"third"));

        {
            let mut_first = map.get_mut(&"first");
            assert_eq!(Some((&mut "v1", 0)), mut_first);
            *mut_first.unwrap().0 = "edited";
        }

        assert_eq!(Some((&"edited", 0)), map.get(&"first"));
        assert_eq!(Some((&"v2", 1)), map.get(&"second"));
        assert_eq!(None, map.get(&"third"));

        assert_eq!(2, map.len());
    }

    #[test]
    fn test_hash_map_with_ids_use_u8_ids() {
        let mut map = HashMapWithIds::<&'static str, (), u8>::default();

        assert_eq!(Some((None, 0)), map.insert("foo", ()));
        assert_eq!(Some((None, 1)), map.insert("bar", ()));
        assert_eq!(Some((None, 2)), map.insert("baz", ()));

        assert_eq!(Some((Some(()), 1)), map.insert("bar", ()));

        assert_eq!(["foo", "bar", "baz"], map.keys_to_vec().as_slice());
    }

    #[test]
    fn test_hash_map_with_ids_use_usize_ids() {
        let mut map = HashMapWithIds::<&'static str, (), usize>::default();

        assert_eq!(Some((None, 0)), map.insert("foo", ()));
        assert_eq!(Some((None, 1)), map.insert("bar", ()));
        assert_eq!(Some((None, 2)), map.insert("baz", ()));

        assert_eq!(Some((Some(()), 1)), map.insert("bar", ()));

        assert_eq!(["foo", "bar", "baz"], map.keys_to_vec().as_slice());
    }

    #[test]
    fn test_hash_map_with_ids_run_out_of_ids() {
        let mut map = HashMapWithIds::<u16, (), u8>::default();

        for i in 0..(u16::from(u8::MAX) + 1) {
            assert!(map.insert(i, ()).is_some());
        }
        assert!(map.insert(u16::from(u8::MAX) + 1, ()).is_none());
    }
}
