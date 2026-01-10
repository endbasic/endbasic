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
use std::collections::HashMap;
#[cfg(test)]
use std::collections::HashSet;

/// Information about a symbol in the symbols table.
#[derive(Clone)]
pub(super) enum SymbolPrototype {
    /// Information about an array.  The integer indicates the number of dimensions in the array.
    Array(ExprType, usize),

    /// Information about a callable that's a builtin and requires an upcall to execute.
    /// The integer indicates the runtime upcall index of the callable.
    BuiltinCallable(CallableMetadata, usize),

    /// Information about a callable.
    Callable(CallableMetadata),

    /// Information about a variable.
    Variable(ExprType),
}

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
    globals: HashMap<SymbolKey, SymbolPrototype>,

    /// Map of local symbol names to their definitions.
    scopes: Vec<HashMap<SymbolKey, SymbolPrototype>>,
}

impl Default for SymbolsTable {
    fn default() -> Self {
        Self { globals: HashMap::default(), scopes: vec![HashMap::default()] }
    }
}

impl From<HashMap<SymbolKey, SymbolPrototype>> for SymbolsTable {
    fn from(globals: HashMap<SymbolKey, SymbolPrototype>) -> Self {
        Self { globals, scopes: vec![HashMap::default()] }
    }
}

impl From<&Symbols> for SymbolsTable {
    fn from(syms: &Symbols) -> Self {
        let globals = {
            let mut globals = HashMap::default();

            let callables = syms.callables();
            let mut names = callables.keys().copied().collect::<Vec<&SymbolKey>>();
            // This is only necessary for testing really... but may also remove some confusion
            // when inspecting the bytecode because it helps keep upcall indexes stable across
            // different compilations.
            names.sort();

            for (i, name) in names.into_iter().enumerate() {
                let callable = callables.get(&name).unwrap();
                let proto = SymbolPrototype::BuiltinCallable(callable.metadata().clone(), i);
                globals.insert(name.clone(), proto);
            }

            globals
        };

        let mut scope = HashMap::default();
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
        self.scopes.push(HashMap::default());
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
    pub(super) fn get(&self, key: &SymbolKey) -> Option<&SymbolPrototype> {
        let proto = self.scopes.last().unwrap().get(key);
        if proto.is_some() {
            return proto;
        }

        self.globals.get(key)
    }

    /// Inserts the new information `proto` about symbol `key` into the symbols table.
    /// The symbol must not yet exist.
    pub(super) fn insert(&mut self, key: SymbolKey, proto: SymbolPrototype) {
        debug_assert!(!self.globals.contains_key(&key), "Cannot redefine a symbol");
        let previous = self.scopes.last_mut().unwrap().insert(key, proto);
        debug_assert!(previous.is_none(), "Cannot redefine a symbol");
    }

    /// Inserts the builtin callable described by `md` and assigns an upcall index.
    /// The symbol must not yet exist.
    #[cfg(test)]
    pub(super) fn insert_builtin_callable(&mut self, key: SymbolKey, md: CallableMetadata) {
        let next_upcall_index = self
            .globals
            .values()
            .filter(|proto| matches!(proto, SymbolPrototype::BuiltinCallable(..)))
            .count();

        debug_assert!(!self.globals.contains_key(&key), "Cannot redefine a symbol");
        let proto = SymbolPrototype::BuiltinCallable(md, next_upcall_index);
        let previous = self.globals.insert(key, proto);
        debug_assert!(previous.is_none(), "Cannot redefine a symbol");
    }

    /// Inserts the new information `proto` about symbol `key` into the symbols table.
    /// The symbol must not yet exist.
    pub(super) fn insert_global(&mut self, key: SymbolKey, proto: SymbolPrototype) {
        let previous = self.globals.insert(key, proto);
        debug_assert!(previous.is_none(), "Cannot redefine a symbol");
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
        let mut builtins = self
            .globals
            .iter()
            .filter_map(|(key, proto)| {
                if let SymbolPrototype::BuiltinCallable(_md, upcall_index) = proto {
                    Some((upcall_index, key))
                } else {
                    None
                }
            })
            .collect::<Vec<(&usize, &SymbolKey)>>();
        builtins.sort_by_key(|(upcall_index, _key)| *upcall_index);
        builtins.into_iter().map(|(_upcall_index, key)| key.clone()).collect()
    }
}
