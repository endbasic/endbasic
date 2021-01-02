// EndBASIC
// Copyright 2020 Julio Merino
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

//! Implementation of a `Store` that uses the browser's local storage.

use endbasic_core::store::{Metadata, Store};
use std::collections::BTreeMap;
use std::io;

/// Mechanism to obtain the current time to facilitate testing.
trait Clock {
    /// Obtains the current time.
    fn now(&self) -> time::OffsetDateTime;
}

/// Clock that obtains the current time from the Javascript runtime.
#[derive(Default)]
struct JsClock {}

impl Clock for JsClock {
    fn now(&self) -> time::OffsetDateTime {
        time::OffsetDateTime::from_unix_timestamp((js_sys::Date::now() / 1000.0) as i64)
    }
}

/// Key for a program stored in the browser's local storage.
#[derive(Debug, Eq, PartialEq)]
struct Key(String);

impl Key {
    /// Prefix for all keys that belong to us.
    const PREFIX: &'static str = "endbasic-program:";

    /// Creates a new key for a program name.
    fn for_name(name: &str) -> Self {
        debug_assert!(name.to_ascii_uppercase().ends_with(".BAS"));
        Self(format!("{}{}", Key::PREFIX, name))
    }

    /// Constructs a key from a serialized representation of a key, or none if the `raw` string does
    /// not correspond to one of our keys.
    fn parse(raw: &str) -> Option<Key> {
        if raw.starts_with(Key::PREFIX) && raw.to_ascii_uppercase().ends_with(".BAS") {
            Some(Key(raw.to_owned()))
        } else {
            None
        }
    }

    /// Returns the program name for this key.
    fn name(&self) -> &str {
        &self.0[Key::PREFIX.len()..]
    }

    /// Returns the serialized version of this key for use with the local storage API.
    fn serialized(&self) -> &str {
        &self.0
    }
}

/// Represents the contents and the metadata of a stored program.
#[derive(serde::Serialize, serde::Deserialize)]
struct Entry {
    /// Version of the schema used to write out this entry.
    version: u16,

    /// The textual content of the program.
    content: String,

    /// The last modification time of the program, in UTC.
    mtime: time::OffsetDateTime,
}

impl Entry {
    /// Version of the schema used in the serialized entries.
    const VERSION: u16 = 1;

    /// Constructs a new entry with the given `content` and with a last modification of now.
    fn new<S: Into<String>>(content: S, mtime: time::OffsetDateTime) -> Self {
        Self { version: Entry::VERSION, content: content.into(), mtime }
    }

    /// Returns the generic `Metadata` object for this entry.
    fn metadata(&self) -> Metadata {
        // I'm sure there is something wrong with this timezone adjustment.
        let tz_offset =
            time::UtcOffset::minutes(-js_sys::Date::new_0().get_timezone_offset() as i16);
        Metadata { date: self.mtime.to_offset(tz_offset), length: self.content.len() as u64 }
    }
}

/// Browser-based store implementation that uses the local storage.
pub struct WebStore {
    /// Instance of the window's local storage.
    storage: web_sys::Storage,

    /// Clock used by this store to generate mtime values.
    clock: Box<dyn Clock>,
}

impl WebStore {
    /// Creates a new store for the current window.
    pub fn from_window() -> Self {
        // TODO(jmmv): Should probably do something fancier here instead of these unwraps...
        let window = web_sys::window().unwrap();
        let storage = window.local_storage().unwrap().unwrap();
        Self { clock: Box::from(JsClock::default()), storage }
    }

    /// Obtains and parses the entry given by `key`.
    fn get_entry(&self, key: &Key) -> io::Result<Entry> {
        let key = key.serialized();
        let raw = match self.storage.get(key) {
            Ok(Some(content)) => content,
            Ok(None) => return Err(io::Error::new(io::ErrorKind::NotFound, "File not found")),
            Err(e) => {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    format!("Failed to get local storage entry with key {}: {:?}", key, e),
                ))
            }
        };

        match serde_json::from_str(&raw) {
            Ok(entry) => Ok(entry),
            Err(e) => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Failed to parse local storage entry with key {}: {:?}", key, e),
            )),
        }
    }
}

impl Store for WebStore {
    fn delete(&mut self, name: &str) -> io::Result<()> {
        let key = Key::for_name(name);
        let key = key.serialized();

        match self.storage.get(key) {
            Ok(Some(_)) => (), // File exists.
            Ok(None) => return Err(io::Error::new(io::ErrorKind::NotFound, "File not found")),
            Err(_) => (), // Fall through to try deletion anyway.
        }

        match self.storage.delete(key) {
            Ok(()) => Ok(()),
            Err(e) => Err(io::Error::new(
                io::ErrorKind::Other,
                format!("Failed to put remove storage entry with key {}: {:?}", key, e),
            )),
        }
    }

    fn enumerate(&self) -> io::Result<BTreeMap<String, Metadata>> {
        let mut entries = BTreeMap::new();

        let n = match self.storage.length() {
            Ok(n) => n,
            Err(e) => return Err(io::Error::new(io::ErrorKind::Other, format!("{:?}", e))),
        };
        for i in 0..n {
            let key = match self.storage.key(i) {
                Ok(Some(key)) => key,
                Ok(None) => return Err(io::Error::new(io::ErrorKind::Other, "Entry vanished")),
                Err(e) => {
                    return Err(io::Error::new(
                        io::ErrorKind::Other,
                        format!("Failed to fetch local storage entry with index {}: {:?}", i, e),
                    ))
                }
            };

            if let Some(key) = Key::parse(&key) {
                let entry = self.get_entry(&key)?;
                entries.insert(key.name().to_owned(), entry.metadata());
            }
        }

        Ok(entries)
    }

    fn get(&self, name: &str) -> io::Result<String> {
        let entry = self.get_entry(&Key::for_name(name))?;
        Ok(entry.content)
    }

    fn put(&mut self, name: &str, content: &str) -> io::Result<()> {
        let key = Key::for_name(name);

        // There is no information we care about the old entry so we can replace it all in one go
        // with a new one.
        let entry = Entry::new(content, self.clock.now());

        let key = key.serialized();
        match self.storage.set(key, &serde_json::to_string(&entry)?) {
            Ok(()) => Ok(()),
            Err(e) => Err(io::Error::new(
                io::ErrorKind::Other,
                format!("Failed to put local storage entry with key {}: {:?}", key, e),
            )),
        }
    }
}

#[cfg(test)]
mod testutils {
    use super::*;

    /// Fake clock that always returns the same time instant.
    pub(crate) struct FakeClock {
        pub(crate) now: i64,
    }

    impl Clock for FakeClock {
        fn now(&self) -> time::OffsetDateTime {
            time::OffsetDateTime::from_unix_timestamp(self.now)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::testutils::*;
    use super::*;
    use wasm_bindgen_test::*;

    #[wasm_bindgen_test]
    fn test_key_for_name() {
        assert_eq!(Key("endbasic-program:hello.bas".to_owned()), Key::for_name("hello.bas"));
        assert_eq!(Key("endbasic-program:OTHER.BAS".to_owned()), Key::for_name("OTHER.BAS"));
    }

    #[wasm_bindgen_test]
    fn test_key_parse() {
        assert_eq!(
            Some(Key("endbasic-program:X.BAS".to_owned())),
            Key::parse("endbasic-program:X.BAS")
        );
        assert_eq!(
            Some(Key("endbasic-program:hello.bas".to_owned())),
            Key::parse("endbasic-program:hello.bas")
        );

        assert_eq!(None, Key::parse("endbasic-program:unknown.bat"));
        assert_eq!(None, Key::parse("endbasic-program:"));
        assert_eq!(None, Key::parse("foo-program:hello.bas"));
    }

    #[wasm_bindgen_test]
    fn test_key_name() {
        assert_eq!("hello.bas", Key::for_name("hello.bas").name());
    }

    #[wasm_bindgen_test]
    fn test_key_serialized() {
        assert_eq!("endbasic-program:hello.bas", Key::for_name("hello.bas").serialized());
    }

    #[wasm_bindgen_test]
    fn test_webstore_delete_ok() {
        let mut webstore = WebStore::from_window();
        webstore.storage.clear().unwrap();
        webstore.storage.set("endbasic-program:first.bas", "").unwrap();
        webstore.storage.set("endbasic-program:first.bat", "").unwrap();

        webstore.delete("first.bas").unwrap();
        assert!(webstore.storage.get("endbasic-program:first.bas").unwrap().is_none());
        webstore.storage.get("endbasic-program:first.bat").unwrap();
    }

    #[wasm_bindgen_test]
    fn test_webstore_delete_missing_file() {
        let mut webstore = WebStore::from_window();
        webstore.storage.clear().unwrap();

        assert_eq!("File not found", format!("{}", webstore.delete("first.bas").unwrap_err()));
    }

    #[wasm_bindgen_test]
    fn test_webstore_enumerate() {
        let entry1 = Entry {
            version: Entry::VERSION,
            content: "first".to_owned(),
            mtime: time::OffsetDateTime::from_unix_timestamp(1234),
        };
        let entry2 = Entry {
            version: Entry::VERSION,
            content: "second".to_owned(),
            mtime: time::OffsetDateTime::from_unix_timestamp(987_654_321),
        };

        let webstore = WebStore::from_window();
        webstore.storage.clear().unwrap();
        webstore
            .storage
            .set("endbasic-program:first.bas", &serde_json::to_string(&entry1).unwrap())
            .unwrap();
        webstore
            .storage
            .set("endbasic-program:SECOND SPACES.BAS", &serde_json::to_string(&entry2).unwrap())
            .unwrap();
        webstore.storage.set("first.bas", "ignore me").unwrap();
        webstore.storage.set("endbasic-program:", "ignore me").unwrap();

        let entries = webstore.enumerate().unwrap();
        assert_eq!(2, entries.len());
        assert_eq!(&entry1.metadata(), entries.get("first.bas").unwrap());
        assert_eq!(&entry2.metadata(), entries.get("SECOND SPACES.BAS").unwrap());
    }

    #[wasm_bindgen_test]
    fn test_webstore_get() {
        let entry = Entry {
            version: Entry::VERSION,
            content: "second".to_owned(),
            mtime: time::OffsetDateTime::from_unix_timestamp(1234),
        };

        let webstore = WebStore::from_window();
        webstore.storage.clear().unwrap();
        webstore.storage.set("endbasic-program:a.bas", "first").unwrap();
        webstore
            .storage
            .set("endbasic-program:b.bas", &serde_json::to_string(&entry).unwrap())
            .unwrap();
        webstore.storage.set("endbasic-program:b.bat", "third").unwrap();
        webstore.storage.set("b.bas", "fourth").unwrap();

        assert_eq!(entry.content, webstore.get("b.bas").unwrap());
    }

    #[wasm_bindgen_test]
    fn test_webstore_put() {
        let entry = Entry {
            version: Entry::VERSION,
            content: "this is some content".to_owned(),
            mtime: time::OffsetDateTime::from_unix_timestamp(1_234_567),
        };

        let mut webstore = WebStore::from_window();
        webstore.clock = Box::from(FakeClock { now: 1_234_567 });
        webstore.storage.clear().unwrap();
        webstore.put("code.bas", &entry.content).unwrap();

        assert_eq!(
            serde_json::to_string(&entry).unwrap(),
            webstore.storage.get("endbasic-program:code.bas").unwrap().unwrap()
        );
    }
}
