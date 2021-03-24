// EndBASIC
// Copyright 2021 Julio Merino
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

//! Storage-related abstractions and commands.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::io;
use std::rc::Rc;
use std::str;

mod cmds;
pub use cmds::*;
mod fs;
pub use fs::DirectoryDrive;
mod mem;
pub use mem::InMemoryDrive;

/// Metadata of an entry in a storage medium.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Metadata {
    /// Last modification time of the entry.
    pub date: time::OffsetDateTime,

    /// Total size of the entry.
    pub length: u64,
}

/// Abstract operations to load and store programs on some storage medium.
pub trait Drive {
    /// Deletes the program given by `name`.
    fn delete(&mut self, name: &str) -> io::Result<()>;

    /// Returns a sorted list of the entries in the store and their metadata.
    fn enumerate(&self) -> io::Result<BTreeMap<String, Metadata>>;

    /// Loads the contents of the program given by `name`.
    fn get(&self, name: &str) -> io::Result<String>;

    /// Saves the in-memory program given by `content` into `name`.
    fn put(&mut self, name: &str, content: &str) -> io::Result<()>;
}

/// Storage subsystem representation.
///
/// At the moment, the storage subsystem is backed by a single drive, so this type is a wrapper
/// for the `Drive` type.
pub struct Storage {
    drive: Rc<RefCell<dyn Drive>>,
}

impl Storage {
    /// Creates a new storage subsytem backed by `drive`.
    pub fn new(drive: Rc<RefCell<dyn Drive>>) -> Self {
        Self { drive }
    }

    /// Deletes the program given by `name`.
    pub fn delete(&mut self, name: &str) -> io::Result<()> {
        self.drive.borrow_mut().delete(name)
    }

    /// Returns a sorted list of the entries in the store and their metadata.
    pub fn enumerate(&self) -> io::Result<BTreeMap<String, Metadata>> {
        self.drive.borrow().enumerate()
    }

    /// Loads the contents of the program given by `name`.
    pub fn get(&self, name: &str) -> io::Result<String> {
        self.drive.borrow().get(name)
    }

    /// Saves the in-memory program given by `content` into `name`.
    pub fn put(&mut self, name: &str, content: &str) -> io::Result<()> {
        self.drive.borrow_mut().put(name, content)
    }
}
