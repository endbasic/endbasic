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

use crate::ast::ExprType;
use crate::syms::{CallableMetadata, Symbol, SymbolKey, Symbols};
#[cfg(test)]
use std::collections::hash_map::Keys;
use std::collections::HashMap;
#[cfg(test)]
use std::collections::HashSet;
use std::hash::Hash;

/// Interface to return the discriminant of an enum for index calculation purposes.
///
/// This is not `std::mem::discriminant` because 1. we don't want to have to construct a default
/// instance just to get the discriminant, and because 2. we may want to collapse multiple types
/// into the same bucket.
trait Bucketizer {
    /// The type being bucketized.
    type V;

    /// Bucketizes a value and assigns it a "bucket" number.
    fn bucketize(&self, value: &Self::V) -> u8;
}

/// Information about a symbol in the symbols table.
#[derive(Clone)]
pub(super) enum SymbolPrototype {
    /// Information about an array.  The integer indicates the number of dimensions in the array.
    Array(ExprType, usize),

    /// Information about a callable that's a builtin and requires an upcall to execute.
    /// The integer indicates the runtime upcall index of the callable.
    BuiltinCallable(CallableMetadata),

    /// Information about a callable.
    Callable(CallableMetadata),

    /// Information about a variable.
    Variable(ExprType),
}

/// A bucketizer for `SymbolPrototype`.
#[derive(Default)]
struct SymbolPrototypeBucketizer {}

impl SymbolPrototypeBucketizer {
    const BUCKET_BUILTINS: u8 = 0;
    const BUCKET_STACK: u8 = 1;
    const BUCKET_OTHER: u8 = 255;
}

impl Bucketizer for SymbolPrototypeBucketizer {
    type V = SymbolPrototype;

    fn bucketize(&self, value: &SymbolPrototype) -> u8 {
        match value {
            SymbolPrototype::BuiltinCallable(..) => Self::BUCKET_BUILTINS,
            SymbolPrototype::Array(..) | SymbolPrototype::Variable(..) => Self::BUCKET_STACK,
            _ => Self::BUCKET_OTHER,
        }
    }
}

/// A wrapper over `HashMap` that assigns indexes to newly-inserted entries based on a `Bucketizer`
/// and then allows retrieving such indexes per key and retrieving the list of keys in insertion
/// order for a given bucket.
struct IndexedHashMap<K, V, B> {
    map: HashMap<K, (V, usize)>,
    bucketizer: B,
    counters: HashMap<u8, usize>,
}

impl<K, V, B: Bucketizer<V = V>> IndexedHashMap<K, V, B> {
    /// Constructs a new `IndexedHashMap` backed by `bucketizer` to assign indexes.
    fn new(bucketizer: B) -> Self {
        Self { map: HashMap::default(), bucketizer, counters: HashMap::default() }
    }

    /// Returns the counter of the bucket where `value` belongs.
    fn counts_of(&self, value: &V) -> usize {
        let counter_id = self.bucketizer.bucketize(value);
        self.counters.get(&counter_id).copied().unwrap_or(0)
    }

    /// Increments the counter of the bucket where `value` belongs.
    fn increment_counts_of(&mut self, value: &V) -> usize {
        let counter_id = self.bucketizer.bucketize(value);
        let next_index = *self.counters.entry(counter_id).and_modify(|v| *v += 1).or_insert(1);
        next_index - 1
    }
}

impl<K: Eq + Hash, V, B: Bucketizer<V = V>> IndexedHashMap<K, V, B> {
    /// Same as `HashMap::contains_key`.
    fn contains_key(&self, key: &K) -> bool {
        self.map.contains_key(key)
    }

    /// Same as `HashMap::get`.
    #[cfg(test)]
    fn get(&self, key: &K) -> Option<&V> {
        self.map.get(key).map(|v| &v.0)
    }

    /// Same as `HashMap::get` but also returns the index assigned to the key.
    fn get_with_index(&self, key: &K) -> Option<(&V, usize)> {
        self.map.get(key).map(|v| (&v.0, v.1))
    }

    /// Same as `HashMap::insert` but does not return the previous value because this assumes that
    /// no previous value can exist.  Instead, this returns the assigned index.
    fn insert(&mut self, key: K, value: V) -> usize {
        let index = self.increment_counts_of(&value);
        let previous = self.map.insert(key, (value, index));
        // We could support updating existing keys, but that would make things more difficult for no
        // reason because we would need to check if the replacement value matches the bucket of the
        // previous one and deal with that accordingly.
        assert!(previous.is_none(), "Updating existing keys is not supported");
        index
    }

    /// Same as `HashMap::keys`.
    #[cfg(test)]
    fn keys(&self) -> Keys<'_, K, (V, usize)> {
        self.map.keys()
    }

    /// Same as `HashMap::remove`.
    fn remove(&mut self, key: &K) -> Option<V> {
        self.map.remove(key).map(|v| v.0)
    }
}

impl<K: Clone + Eq + Hash, V, B: Bucketizer<V = V>> IndexedHashMap<K, V, B> {
    /// Returns the list of keys, in insertion order, for `bucket`.
    fn get_ordered_keys(&self, bucket: u8) -> Vec<K> {
        let mut builtins = self
            .map
            .iter()
            .filter_map(|(key, (proto, index))| {
                if self.bucketizer.bucketize(proto) == bucket {
                    Some((index, key))
                } else {
                    None
                }
            })
            .collect::<Vec<(&usize, &K)>>();
        builtins.sort_by_key(|(index, _key)| *index);
        builtins.into_iter().map(|(_index, key)| key.clone()).collect()
    }
}

type SymbolsMap = IndexedHashMap<SymbolKey, SymbolPrototype, SymbolPrototypeBucketizer>;

/// The symbols table used during compilation.
///
/// Symbols are represented as a two-layer map: the globals map contains all symbols that are
/// visible by all scopes, and the scope contains all symbols that are only visible within a
/// given scope.
///
/// The collection of symbols that is visible at any given point in time is thus the union of
/// the global symbols and the symbols in the last scope.
///
/// There is always at least one scope in the scopes stack: at the program level outside of
/// functions, variables are not global by default and thus they are kept in their own scope.
/// But because we do not support nested function definitions, the scopes "stack" should
/// always have size of one or two.
pub(super) struct SymbolsTable {
    /// Map of global symbol names to their definitions.
    globals: SymbolsMap,

    /// Map of local symbol names to their definitions.
    scopes: Vec<SymbolsMap>,
}

impl Default for SymbolsTable {
    fn default() -> Self {
        Self {
            globals: IndexedHashMap::new(SymbolPrototypeBucketizer::default()),
            scopes: vec![IndexedHashMap::new(SymbolPrototypeBucketizer::default())],
        }
    }
}

impl From<SymbolsMap> for SymbolsTable {
    fn from(globals: SymbolsMap) -> Self {
        Self { globals, scopes: vec![IndexedHashMap::new(SymbolPrototypeBucketizer::default())] }
    }
}

impl From<&Symbols> for SymbolsTable {
    fn from(syms: &Symbols) -> Self {
        let globals = {
            let mut globals = IndexedHashMap::new(SymbolPrototypeBucketizer::default());

            let callables = syms.callables();
            let mut names = callables.keys().copied().collect::<Vec<&SymbolKey>>();
            // This is only necessary for testing really... but may also remove some confusion
            // when inspecting the bytecode because it helps keep upcall indexes stable across
            // different compilations.
            names.sort();

            for name in names {
                let callable = callables.get(&name).unwrap();
                let proto = SymbolPrototype::BuiltinCallable(callable.metadata().clone());
                globals.insert(name.clone(), proto);
            }

            globals
        };

        let mut scope = IndexedHashMap::new(SymbolPrototypeBucketizer::default());
        for (name, symbol) in syms.locals() {
            let proto = match symbol {
                Symbol::Array(array) => {
                    SymbolPrototype::Array(array.subtype(), array.dimensions().len())
                }
                Symbol::Callable(_) => {
                    unreachable!("Callables must only be global");
                }
                Symbol::Variable(var) => SymbolPrototype::Variable(var.as_exprtype()),
            };
            scope.insert(name.clone(), proto);
        }

        Self { globals, scopes: vec![scope] }
    }
}

impl SymbolsTable {
    /// Enters a new scope.
    pub(super) fn enter_scope(&mut self) {
        self.scopes.push(IndexedHashMap::new(SymbolPrototypeBucketizer::default()));
    }

    /// Leaves the current scope.
    pub(super) fn leave_scope(&mut self) {
        let last = self.scopes.pop();
        assert!(last.is_some(), "Must have at least one scope to pop");
        assert!(!self.scopes.is_empty(), "Cannot pop the global scope");
    }

    /// Returns true if the symbols table contains `key`.
    pub(super) fn contains_key(&mut self, key: &SymbolKey) -> bool {
        self.scopes.last().unwrap().contains_key(key) || self.globals.contains_key(key)
    }

    /// Returns the information for the symbol `key` if it exists, otherwise `None`.
    #[cfg(test)]
    pub(super) fn get(&self, key: &SymbolKey) -> Option<&SymbolPrototype> {
        let proto = self.scopes.last().unwrap().get(key);
        if proto.is_some() {
            return proto;
        }

        self.globals.get(key)
    }

    /// Returns the information for the symbol `key` if it exists, otherwise `None`.
    pub(super) fn get_with_index(&self, key: &SymbolKey) -> Option<(&SymbolPrototype, usize)> {
        let proto = self.scopes.last().unwrap().get_with_index(key);
        if proto.is_some() {
            return proto;
        }

        self.globals.get_with_index(key)
    }

    /// Inserts the new information `proto` about symbol `key` into the symbols table.
    /// The symbol must not yet exist.
    pub(super) fn insert(&mut self, key: SymbolKey, proto: SymbolPrototype) -> usize {
        debug_assert!(!self.globals.contains_key(&key), "Cannot redefine a symbol");
        self.scopes.last_mut().unwrap().insert(key, proto)
    }

    /// Inserts the builtin callable described by `md` and assigns an upcall index.
    /// The symbol must not yet exist.
    #[cfg(test)]
    pub(super) fn insert_builtin_callable(&mut self, key: SymbolKey, md: CallableMetadata) {
        debug_assert!(!self.globals.contains_key(&key), "Cannot redefine a symbol");
        let proto = SymbolPrototype::BuiltinCallable(md);
        self.globals.insert(key, proto);
    }

    /// Inserts the new information `proto` about symbol `key` into the symbols table.
    /// The symbol must not yet exist.
    pub(super) fn insert_global(&mut self, key: SymbolKey, proto: SymbolPrototype) -> usize {
        self.globals.insert(key, proto)
    }

    /// Returns the index of the last element of type `proto` for the current scope.
    pub(super) fn last_index_of(&self, proto: &SymbolPrototype) -> usize {
        self.scopes.last().unwrap().counts_of(proto)
    }

    /// Removes information about the symbol `key`.
    pub(super) fn remove(&mut self, key: SymbolKey) {
        let previous = self.scopes.last_mut().unwrap().remove(&key);
        debug_assert!(previous.is_some(), "Cannot unset a non-existing symbol");
    }

    /// Returns a view of the keys in the symbols table.
    #[cfg(test)]
    pub(super) fn keys(&self) -> HashSet<&SymbolKey> {
        let mut keys = HashSet::default();
        keys.extend(self.globals.keys());
        keys.extend(self.scopes.last().unwrap().keys());
        keys
    }

    /// Calculates the list of upcalls in this symbols table in the order in which they were
    /// assigned indexes.
    pub(super) fn upcalls(&self) -> Vec<SymbolKey> {
        self.globals.get_ordered_keys(SymbolPrototypeBucketizer::BUCKET_BUILTINS)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A bucketizer for integers that classifies them as even or odd.
    struct I32Bucketizer {}

    impl I32Bucketizer {
        const BUCKET_ODD: u8 = 10;
        const BUCKET_EVEN: u8 = 20;
    }

    impl Bucketizer for I32Bucketizer {
        type V = i32;

        fn bucketize(&self, value: &Self::V) -> u8 {
            if value % 2 == 0 {
                Self::BUCKET_EVEN
            } else {
                Self::BUCKET_ODD
            }
        }
    }

    #[test]
    fn test_indexed_hash_map_assigns_indexes_by_bucket() {
        let mut map = IndexedHashMap::new(I32Bucketizer {});
        map.insert("a", 1);
        map.insert("b", 2);
        map.insert("c", 2);
        map.insert("d", 3);
        map.insert("e", 3);
        map.insert("f", 1);
        map.insert("g", 4);

        assert_eq!((&1, 0), map.get_with_index(&"a").unwrap());
        assert_eq!((&2, 0), map.get_with_index(&"b").unwrap());
        assert_eq!((&2, 1), map.get_with_index(&"c").unwrap());
        assert_eq!((&3, 1), map.get_with_index(&"d").unwrap());
        assert_eq!((&3, 2), map.get_with_index(&"e").unwrap());
        assert_eq!((&1, 3), map.get_with_index(&"f").unwrap());
        assert_eq!((&4, 2), map.get_with_index(&"g").unwrap());
    }

    #[test]
    fn test_indexed_hash_map_get_ordered_keys() {
        let mut map = IndexedHashMap::new(I32Bucketizer {});
        map.insert("a", 1);
        map.insert("h", 2);
        map.insert("d", 2);
        map.insert("i", 3);
        map.insert("e", 3);
        map.insert("z", 1);
        map.insert("o", 4);

        assert_eq!(["h", "d", "o"], map.get_ordered_keys(I32Bucketizer::BUCKET_EVEN).as_slice());
        assert_eq!(
            ["a", "i", "e", "z"],
            map.get_ordered_keys(I32Bucketizer::BUCKET_ODD).as_slice()
        );
    }
}
