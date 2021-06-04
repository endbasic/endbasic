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

use async_trait::async_trait;
use serde::Deserialize;
#[cfg(test)]
use serde::Serialize;
use std::collections::{BTreeMap, HashMap};
use std::fmt::{self};
use std::io;
use std::path::PathBuf;
use std::str;

mod cmds;
pub use cmds::*;
mod fs;
pub use fs::*;
mod mem;
pub use mem::*;

/// Metadata of an entry in a storage medium.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Metadata {
    /// Last modification time of the entry.
    pub date: time::OffsetDateTime,

    /// Total size of the entry.
    pub length: u64,
}

/// Describes the ACLs of a file.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct FileAcls {
    /// List of principals that are allowed to read the file.
    pub readers: Vec<String>,
}

impl FileAcls {
    /// Extends this set of ACLs with the given `readers`.
    pub fn with_readers<T: Into<Vec<String>>>(mut self, readers: T) -> Self {
        self.readers.extend(readers.into());
        self
    }

    /// Gets the list of principals that are allowed to read the file.
    pub fn readers(&self) -> &[String] {
        &self.readers
    }

    /// Modifies the readers list by appending `reader` to it.
    pub(crate) fn add_reader<R: Into<String>>(&mut self, reader: R) {
        self.readers.push(reader.into());
    }
}

/// Representation of some amount of disk space.  Can be used to express both quotas and usage.
#[derive(Clone, Copy, Debug, Deserialize, PartialEq)]
#[cfg_attr(test, derive(Serialize))]
pub struct DiskSpace {
    bytes: u64,
    files: u64,
}

impl DiskSpace {
    /// Creates a new representation of disk space.
    pub fn new(bytes: u64, files: u64) -> Self {
        Self { bytes, files }
    }

    /// Returns the amount of bytes in this disk space.
    pub fn bytes(&self) -> u64 {
        self.bytes
    }

    /// Returns the number of files in this disk space.
    pub fn files(&self) -> u64 {
        self.files
    }
}

/// Collection of entries in the store and their metadata.  Used to represent the result of the
/// `Drive::enumerate` call.
#[derive(Debug)]
pub struct DriveFiles {
    dirents: BTreeMap<String, Metadata>,
    disk_quota: Option<DiskSpace>,
    disk_free: Option<DiskSpace>,
}

impl DriveFiles {
    /// Creates a new collection of files with the given `dirents`.
    pub fn new(
        dirents: BTreeMap<String, Metadata>,
        disk_quota: Option<DiskSpace>,
        disk_free: Option<DiskSpace>,
    ) -> Self {
        Self { dirents, disk_quota, disk_free }
    }

    /// Returns the collection of files in this result.
    pub fn dirents(&self) -> &BTreeMap<String, Metadata> {
        &self.dirents
    }

    /// Returns the user's disk quota, if known.
    pub fn disk_quota(&self) -> &Option<DiskSpace> {
        &self.disk_quota
    }

    /// Returns the disk free space, if known.
    pub fn disk_free(&self) -> &Option<DiskSpace> {
        &self.disk_free
    }
}

/// Abstract operations to load and store programs on some storage medium.
#[async_trait(?Send)]
pub trait Drive {
    /// Deletes the program given by `name`.
    async fn delete(&mut self, name: &str) -> io::Result<()>;

    /// Returns the entries in the store and their metadata.
    async fn enumerate(&self) -> io::Result<DriveFiles>;

    /// Loads the contents of the program given by `name`.
    async fn get(&self, name: &str) -> io::Result<String>;

    /// Gets the ACLs of the file `_name`.
    async fn get_acls(&self, _name: &str) -> io::Result<FileAcls> {
        Err(io::Error::new(io::ErrorKind::Other, "Operation not supported by drive"))
    }

    /// Saves the in-memory program given by `content` into `name`.
    async fn put(&mut self, name: &str, content: &str) -> io::Result<()>;

    /// Updates the ACLs of the file `_name` by extending them with the contents of `_add` and
    /// removing the existing entries listed in `_remove`.
    async fn update_acls(
        &mut self,
        _name: &str,
        _add: &FileAcls,
        _remove: &FileAcls,
    ) -> io::Result<()> {
        Err(io::Error::new(io::ErrorKind::Other, "Operation not supported by drive"))
    }

    /// Gets the system-addressable path of the file `_name`, if any.
    fn system_path(&self, _name: &str) -> Option<PathBuf> {
        None
    }
}

/// Unique identifier for a drive.
///
/// The name contained in the key is stored in its canonical form.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct DriveKey(String);

impl DriveKey {
    /// Constructs a drive from a raw string, validating that the name is valid.
    fn new<T: Into<String>>(drive: T) -> io::Result<DriveKey> {
        let drive = drive.into();
        if !DriveKey::is_valid(&drive) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("Invalid drive name '{}'", drive),
            ));
        }
        Ok(DriveKey(drive.to_uppercase()))
    }

    /// Returns true if the given drive name is valid.
    fn is_valid(s: &str) -> bool {
        !s.is_empty() && !s.chars().any(|c| c == ':' || c == '\\' || c == '/' || c == '.')
    }
}

impl fmt::Display for DriveKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// Representation of an EndBASIC path.
///
/// This implementation is not as efficient as it could be, given that many times we don't have to
/// clone the input string to break it into pieces.  However, owning the components here makes the
/// implementation much simpler and, for now, should not be a noticeable performance problem.
#[derive(Debug)]
struct Location {
    drive: Option<DriveKey>,
    path: String,
}

impl Location {
    /// Constructs a new path from the contents of `s` after validating it.
    fn new(s: &str) -> io::Result<Self> {
        let fields = s.split(':').collect::<Vec<&str>>();
        let (drive, mut path) = match fields.as_slice() {
            [drive, path] => (Some(DriveKey::new(*drive)?), *path),
            [path] => (None, *path),
            _ => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("Too many : separators in path '{}'", s),
                ))
            }
        };

        if path.is_empty() {
            path = "/";
        } else {
            if !Location::is_path_valid(path)
                || path == "."
                || path == ".."
                || path == "/."
                || path == "/.."
            {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("Invalid path '{}'", s),
                ));
            }
            let slashes = path.chars().fold(0, |a, c| if c == '/' { a + 1 } else { a });
            if (slashes == 1 && !path.starts_with('/')) || slashes > 1 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("Too many / separators in path '{}'", s),
                ));
            }
        }

        Ok(Self { drive, path: path.to_owned() })
    }

    /// Convenience function to create a path to the root of a `drive`.
    fn with_drive_root(drive: DriveKey) -> Self {
        Self { drive: Some(drive), path: "/".to_owned() }
    }

    /// Returns true if the given path is valid.
    fn is_path_valid(s: &str) -> bool {
        !s.is_empty() && !s.chars().any(|c| c == ':' || c == '\\')
    }

    /// Returns the last component of this path, or none if there is no referenced file.
    fn leaf_name(&self) -> Option<&str> {
        if self.path == "/" {
            None
        } else if self.path.starts_with('/') {
            Some(&self.path[1..])
        } else {
            Some(&self.path)
        }
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.drive {
            Some(drive) => write!(f, "{}:{}", drive.0, self.path),
            None => self.path.fmt(f),
        }
    }
}

/// Trait to instantiate drives of a given type.
pub trait DriveFactory {
    /// Creates a new drive for `target`.
    fn create(&self, target: &str) -> io::Result<Box<dyn Drive>>;
}

/// Given a mount URI, validates it and returns the `(scheme, path)` pair.
fn split_uri(uri: &str) -> io::Result<(&str, &str)> {
    match uri.find("://") {
        Some(pos) if pos > 0 => Ok((&uri[0..pos], &uri[pos + 3..])),
        _ => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "Mount URI must be of the form scheme://path",
        )),
    }
}

/// Metadata for a mounted drive.
struct MountedDrive {
    uri: String,
    drive: Box<dyn Drive>,
}

/// Storage subsystem representation.
///
/// At the moment, the storage subsystem is backed by a single drive, so this type is a wrapper
/// for the `Drive` type.
pub struct Storage {
    /// Mapping of target scheme names to drive factories.
    factories: HashMap<String, Box<dyn DriveFactory>>,

    /// Mapping of drive names to drives.
    drives: HashMap<DriveKey, MountedDrive>,

    /// Name of the active drive, which must be present in `drives`.
    current: DriveKey,
}

impl Default for Storage {
    /// Creates a new storage subsytem backed by an in-memory drive.
    fn default() -> Self {
        let mut factories: HashMap<String, Box<dyn DriveFactory>> = HashMap::default();
        factories.insert("memory".to_owned(), Box::from(InMemoryDriveFactory::default()));

        let drive: Box<dyn Drive> = Box::from(InMemoryDrive::default());

        let mut drives = HashMap::new();
        let key = DriveKey::new("MEMORY").expect("Hardcoded drive name must be valid");
        let mounted_drive = MountedDrive { uri: "memory://".to_owned(), drive };
        drives.insert(key.clone(), mounted_drive);
        Self { factories, drives, current: key }
    }
}

impl Storage {
    /// Registers a new drive `factory` to handle the `scheme`.  Must not have previously been
    /// registered and the `scheme` must be in lowercase.
    pub fn register_scheme(&mut self, scheme: &str, factory: Box<dyn DriveFactory>) {
        assert_eq!(scheme.to_lowercase(), scheme);
        let previous = self.factories.insert(scheme.to_owned(), factory);
        assert!(previous.is_none(), "Tried to register {} twice", scheme);
    }

    /// Returns true if the `scheme` is already registered.
    pub(crate) fn has_scheme(&self, scheme: &str) -> bool {
        self.factories.contains_key(scheme)
    }

    /// Converts a location, which needn't exist, to its canonical form.
    pub fn make_canonical(&self, raw_location: &str) -> io::Result<String> {
        let mut location = Location::new(raw_location)?;
        if location.drive.is_none() {
            location.drive = Some(self.current.clone());
        }
        Ok(location.to_string())
    }

    /// Attaches a new `drive` with `name`, which was instantiated with `uri`.
    ///
    /// The `name` must be valid and must not yet have been registered.
    fn attach(&mut self, name: &str, uri: &str, drive: Box<dyn Drive>) -> io::Result<()> {
        let key = DriveKey::new(name)?;
        if self.drives.contains_key(&key) {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                format!("Drive '{}' is already mounted", name),
            ));
        }
        let mounted_drive = MountedDrive { uri: uri.to_owned(), drive };
        self.drives.insert(DriveKey::new(name)?, mounted_drive);
        Ok(())
    }

    /// Instantiates and attaches a new `drive` with `name` that points to `uri`.
    ///
    /// The `name` must be valid and must not yet have been registered.
    pub fn mount(&mut self, name: &str, uri: &str) -> io::Result<()> {
        let (scheme, path) = split_uri(uri)?;
        let drive = match self.factories.get(&scheme.to_lowercase()) {
            Some(factory) => factory.create(path)?,
            None => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("Unknown mount scheme '{}'", scheme),
                ))
            }
        };
        self.attach(name, uri, drive)
    }

    /// Detaches an existing drive named `name`.
    ///
    /// The drive `name` must exist, cannot be the current drive, and cannot be the last mounted
    /// drive.
    pub fn unmount(&mut self, name: &str) -> io::Result<()> {
        let key = DriveKey::new(name)?;
        if !self.drives.contains_key(&key) {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!("Drive '{}' is not mounted", name),
            ));
        }
        if self.current == key {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                format!("Cannot unmount the current drive '{}'", name),
            ));
        }
        assert!(
            self.drives.len() > 1,
            "There must be more than one drive if the current drive is not the given name"
        );
        self.drives.remove(&key).expect("Drive presence in map checked above");
        Ok(())
    }

    /// Returns information about the mounted drives as a mapping of drive names to the URIs that
    /// were used to mount them.
    pub fn mounted(&self) -> BTreeMap<&str, &str> {
        let mut info = BTreeMap::new();
        for (name, mounted_drive) in &self.drives {
            info.insert(name.0.as_str(), mounted_drive.uri.as_str());
        }
        info
    }

    /// Changes the current location.
    ///
    /// Given that we currently do not support directories, the location can only be of the forms
    /// `DRIVE:` or `DRIVE:/`.
    pub fn cd(&mut self, location: &str) -> io::Result<()> {
        let location = Location::new(location)?;
        if location.leaf_name().is_some() {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "Cannot cd to a file"));
        }

        match location.drive {
            Some(drive) => {
                if !self.drives.contains_key(&drive) {
                    return Err(io::Error::new(
                        io::ErrorKind::AlreadyExists,
                        format!("Drive '{}' is not mounted", drive),
                    ));
                }
                self.current = drive;
                Ok(())
            }
            None => Ok(()),
        }
    }

    /// Returns the current location, used to resolve relative paths.
    pub fn cwd(&self) -> String {
        Location::with_drive_root(self.current.clone()).to_string()
    }

    /// Returns the drive referenced by `location`, or an error if it doesn't exist.
    fn get_drive(&self, location: &Location) -> io::Result<&dyn Drive> {
        match &location.drive {
            Some(key) => match self.drives.get(&key) {
                Some(mounted_drive) => Ok(mounted_drive.drive.as_ref()),
                None => Err(io::Error::new(
                    io::ErrorKind::NotFound,
                    format!("Drive '{}' is not mounted", key),
                )),
            },
            None => Ok(self
                .drives
                .get(&self.current)
                .expect("Current drive out of sync")
                .drive
                .as_ref()),
        }
    }

    /// Returns the drive referenced by `location`, or an error if it doesn't exist.
    fn get_drive_mut(&mut self, location: &Location) -> io::Result<&mut dyn Drive> {
        match &location.drive {
            Some(key) => match self.drives.get_mut(&key) {
                Some(mounted_drive) => Ok(mounted_drive.drive.as_mut()),
                None => Err(io::Error::new(
                    io::ErrorKind::NotFound,
                    format!("Drive '{}' is not mounted", key),
                )),
            },
            None => Ok(self
                .drives
                .get_mut(&self.current)
                .expect("Current drive out of sync")
                .drive
                .as_mut()),
        }
    }

    /// Deletes the program given by `raw_location`.
    pub async fn delete(&mut self, raw_location: &str) -> io::Result<()> {
        let location = Location::new(raw_location)?;
        match location.leaf_name() {
            Some(name) => self.get_drive_mut(&location)?.delete(name).await,
            None => Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!("Missing file name in path '{}'", raw_location),
            )),
        }
    }

    /// Returns a sorted list of the entries in `raw_location` and their metadata.
    pub async fn enumerate(&self, raw_location: &str) -> io::Result<DriveFiles> {
        let location = Location::new(raw_location)?;
        match location.leaf_name() {
            Some(_) => Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!("Location '{}' is not a directory", raw_location),
            )),
            None => self.get_drive(&location)?.enumerate().await,
        }
    }

    /// Loads the contents of the program given by `raw_location`.
    pub async fn get(&self, raw_location: &str) -> io::Result<String> {
        let location = Location::new(raw_location)?;
        match location.leaf_name() {
            Some(name) => self.get_drive(&location)?.get(name).await,
            None => Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!("Missing file name in path '{}'", raw_location),
            )),
        }
    }

    /// Gets the ACLs of the file `raw_location`.
    pub async fn get_acls(&self, raw_location: &str) -> io::Result<FileAcls> {
        let location = Location::new(raw_location)?;
        match location.leaf_name() {
            Some(name) => self.get_drive(&location)?.get_acls(name).await,
            None => Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!("Missing file name in path '{}'", raw_location),
            )),
        }
    }

    /// Saves the in-memory program given by `content` into `raw_location`.
    pub async fn put(&mut self, raw_location: &str, content: &str) -> io::Result<()> {
        let location = Location::new(raw_location)?;
        match location.leaf_name() {
            Some(name) => self.get_drive_mut(&location)?.put(name, content).await,
            None => Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!("Missing file name in path '{}'", raw_location),
            )),
        }
    }

    /// Updates the ACLs of the file `raw_location` by extending them with the contents of `add` and
    /// removing the existing entries listed in `remove`.
    pub async fn update_acls(
        &mut self,
        raw_location: &str,
        add: &FileAcls,
        remove: &FileAcls,
    ) -> io::Result<()> {
        let location = Location::new(raw_location)?;
        match location.leaf_name() {
            Some(name) => self.get_drive_mut(&location)?.update_acls(name, add, remove).await,
            None => Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!("Missing file name in path '{}'", raw_location),
            )),
        }
    }

    /// Gets the system-addressable path of `raw_location`, if any.
    pub fn system_path(&self, raw_location: &str) -> io::Result<Option<PathBuf>> {
        let location = Location::new(raw_location)?;
        match location.leaf_name() {
            Some(name) => Ok(self.get_drive(&location)?.system_path(name)),
            None => Ok(self.get_drive(&location)?.system_path("")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures_lite::future::block_on;

    #[test]
    fn test_split_uri_ok() {
        assert_eq!(("the-scheme", ""), split_uri("the-scheme://").unwrap());
        assert_eq!(("foo", "/some:/target"), split_uri("foo:///some:/target").unwrap());
        assert_eq!(("foo", "bar://baz"), split_uri("foo://bar://baz").unwrap());
    }

    #[test]
    fn test_split_uri_errors() {
        for uri in &["", "://abc", "foo:/", "bar//", "/baz/"] {
            assert_eq!(
                "Mount URI must be of the form scheme://path",
                format!("{}", split_uri(uri).unwrap_err())
            );
        }
    }

    #[test]
    fn test_drivekey_new() {
        assert_eq!(DriveKey("FOO".to_owned()), DriveKey::new("foo").unwrap());
        assert_eq!(DriveKey("A".to_owned()), DriveKey::new("A".to_owned()).unwrap());
    }

    #[test]
    fn test_drivekey_errors() {
        assert_eq!("Invalid drive name ''", format!("{}", DriveKey::new("").unwrap_err()));
        assert_eq!("Invalid drive name 'a:b'", format!("{}", DriveKey::new("a:b").unwrap_err()));
        assert_eq!("Invalid drive name 'a\\b'", format!("{}", DriveKey::new("a\\b").unwrap_err()));
        assert_eq!("Invalid drive name 'a/b'", format!("{}", DriveKey::new("a/b").unwrap_err()));
        assert_eq!("Invalid drive name 'a.b'", format!("{}", DriveKey::new("a.b").unwrap_err()));
    }

    #[test]
    fn test_location_new_ok() {
        fn check(exp_drive: Option<&str>, exp_path: &str, input: &str) {
            let rp = Location::new(input).unwrap();
            assert_eq!(exp_drive.map(|s| DriveKey::new(s).unwrap()), rp.drive);
            assert_eq!(exp_path, rp.path);
        }

        check(None, "/", "/");
        check(None, "/foo.bas", "/foo.bas");

        check(Some("A"), "/", "a:");
        check(Some("ABC"), "/foo.bas", "abc:/foo.bas");
        check(Some("ABC"), "Foo.Bas", "abc:Foo.Bas");
    }

    #[test]
    fn test_location_new_errors() {
        fn check(exp_error: &str, input: &str) {
            let e = Location::new(input).unwrap_err();
            assert_eq!(io::ErrorKind::InvalidInput, e.kind());
            assert_eq!(exp_error, format!("{}", e));
        }

        check("Too many : separators in path 'a:b:c'", "a:b:c");

        check("Invalid drive name ''", ":");
        check("Invalid drive name 'a\\b'", "a\\b:");
        check("Invalid drive name 'a/b'", "a/b:");
        check("Invalid drive name 'a.b'", "a.b:");

        check("Invalid path 'a:\\'", "a:\\");
        check("Invalid path 'a:.'", "a:.");
        check("Invalid path 'a:..'", "a:..");
        check("Invalid path 'a:/.'", "a:/.");
        check("Invalid path 'a:/..'", "a:/..");
        check("Invalid path '.'", ".");
        check("Invalid path '..'", "..");
        check("Invalid path '/.'", "/.");
        check("Invalid path '/..'", "/..");

        check("Too many / separators in path 'a://.'", "a://.");
        check("Too many / separators in path 'a:../'", "a:../");
        check("Too many / separators in path 'a:b/c'", "a:b/c");
        check("Too many / separators in path 'a:/b/c'", "a:/b/c");
    }

    #[test]
    fn test_location_leaf_name() {
        assert_eq!(None, Location::new("drv:/").unwrap().leaf_name());
        assert_eq!(None, Location::new("drv:").unwrap().leaf_name());

        assert_eq!(Some("abc.txt"), Location::new("a:/abc.txt").unwrap().leaf_name());
        assert_eq!(Some("abc.txt"), Location::new("a:abc.txt").unwrap().leaf_name());
        assert_eq!(Some("abc.txt"), Location::new("abc.txt").unwrap().leaf_name());
    }

    /// Convenience helper to obtain the sorted list of mounted drive names in canonical form.
    fn drive_names(storage: &Storage) -> Vec<String> {
        let mut names = storage.drives.keys().map(DriveKey::to_string).collect::<Vec<String>>();
        names.sort();
        names
    }

    #[test]
    fn test_storage_default() {
        let storage = Storage::default();
        assert_eq!("MEMORY:/", storage.cwd());
    }

    #[test]
    fn test_storage_make_canonical_ok() {
        let mut storage = Storage::default();
        storage.mount("some", "memory://").unwrap();

        assert_eq!("MEMORY:foo.bar", storage.make_canonical("foo.bar").unwrap());
        assert_eq!("MEMORY:/foo.bar", storage.make_canonical("/foo.bar").unwrap());
        storage.cd("some:/").unwrap();
        assert_eq!("SOME:foo.bar", storage.make_canonical("foo.bar").unwrap());
        assert_eq!("SOME:/foo.bar", storage.make_canonical("/foo.bar").unwrap());

        assert_eq!("MEMORY:a", storage.make_canonical("memory:a").unwrap());
        assert_eq!("MEMORY:/Abc", storage.make_canonical("memory:/Abc").unwrap());
        assert_eq!("OTHER:a", storage.make_canonical("Other:a").unwrap());
        assert_eq!("OTHER:/Abc", storage.make_canonical("Other:/Abc").unwrap());
    }

    #[test]
    fn test_storage_make_canonical_errors() {
        let storage = Storage::default();
        assert_eq!(
            "Invalid drive name 'a\\b'",
            format!("{}", storage.make_canonical("a\\b:c").unwrap_err())
        );
    }

    #[test]
    fn test_storage_attach_ok() {
        let mut storage = Storage::default();
        storage.attach("zzz1", "z://", Box::from(InMemoryDrive::default())).unwrap();
        storage.attach("A4", "z://", Box::from(InMemoryDrive::default())).unwrap();

        assert_eq!("MEMORY:/", storage.cwd());
        assert_eq!(["A4", "MEMORY", "ZZZ1"], drive_names(&storage).as_slice());
    }

    #[test]
    fn test_storage_attach_invalid_name() {
        let mut storage = Storage::default();
        assert_eq!(
            "Invalid drive name 'a:b'",
            format!(
                "{}",
                storage.attach("a:b", "z://", Box::from(InMemoryDrive::default())).unwrap_err()
            )
        );
    }

    #[test]
    fn test_storage_attach_already_attached() {
        let mut storage = Storage::default();
        assert_eq!(
            "Drive 'memory' is already mounted",
            format!(
                "{}",
                storage.attach("memory", "z://", Box::from(InMemoryDrive::default())).unwrap_err()
            )
        );

        storage.attach("new", "z://", Box::from(InMemoryDrive::default())).unwrap();
        assert_eq!(
            "Drive 'New' is already mounted",
            format!(
                "{}",
                storage.attach("New", "z://", Box::from(InMemoryDrive::default())).unwrap_err()
            )
        );
    }

    #[test]
    fn test_storage_has_scheme() {
        let mut storage = Storage::default();
        storage.register_scheme("fake", Box::from(InMemoryDriveFactory::default()));
        assert!(storage.has_scheme("fake"));
        assert!(!storage.has_scheme("fakes"));
    }

    #[test]
    fn test_storage_mount_ok() {
        let mut storage = Storage::default();
        storage.register_scheme("fake", Box::from(InMemoryDriveFactory::default()));
        storage.mount("a", "memory://").unwrap();
        storage.mount("z", "fAkE://").unwrap();

        assert_eq!(["A", "MEMORY", "Z"], drive_names(&storage).as_slice());
    }

    #[test]
    fn test_storage_mount_path_redirection() {
        let root = tempfile::tempdir().unwrap();
        let dir1 = root.path().join("first");
        let dir2 = root.path().join("second");

        let mut storage = Storage::default();
        storage.register_scheme("file", Box::from(DirectoryDriveFactory::default()));
        storage.mount("c", &format!("file://{}", dir1.display())).unwrap();
        storage.mount("d", &format!("file://{}", dir2.display())).unwrap();

        block_on(storage.put("c:file1.txt", "hi")).unwrap();
        block_on(storage.put("d:file2.txt", "bye")).unwrap();

        assert!(dir1.join("file1.txt").exists());
        assert!(!dir1.join("file2.txt").exists());
        assert!(!dir2.join("file1.txt").exists());
        assert!(dir2.join("file2.txt").exists());
    }

    #[test]
    fn test_storage_mount_unknown_scheme() {
        let mut storage = Storage::default();
        assert_eq!(
            "Unknown mount scheme 'fake'",
            format!("{}", storage.mount("a", "fake://abc").unwrap_err())
        );
    }

    #[test]
    fn test_storage_mount_invalid_path_for_scheme() {
        let mut storage = Storage::default();
        assert_eq!(
            "Cannot specify a path to mount an in-memory drive",
            format!("{}", storage.mount("a", "memory://abc").unwrap_err())
        );
    }

    #[test]
    fn test_storage_unmount_ok() {
        let mut storage = Storage::default();
        storage.mount("other", "memory://").unwrap();
        assert_eq!("MEMORY:/", storage.cwd());
        assert_eq!(["MEMORY", "OTHER"], drive_names(&storage).as_slice());

        storage.unmount("other").unwrap();
        assert_eq!("MEMORY:/", storage.cwd());
        assert_eq!(["MEMORY"], drive_names(&storage).as_slice());
    }

    #[test]
    fn test_storage_unmount_not_mounted_error() {
        let mut storage = Storage::default();
        assert_eq!(
            "Drive 'foo' is not mounted",
            format!("{}", storage.unmount("foo").unwrap_err())
        );
    }

    #[test]
    fn test_storage_unmount_current_drive_error() {
        let mut storage = Storage::default();
        storage.mount("other", "memory://").unwrap();
        assert_eq!(
            "Cannot unmount the current drive 'memory'",
            format!("{}", storage.unmount("memory").unwrap_err())
        );
        storage.cd("other:").unwrap();
        storage.unmount("memory").unwrap();
        assert_eq!("OTHER:/", storage.cwd());
        assert_eq!(["OTHER"], drive_names(&storage).as_slice());
    }

    #[test]
    fn test_storage_mounted() {
        let mut storage = Storage::default();
        storage.register_scheme("fake", Box::from(InMemoryDriveFactory::default()));
        storage.mount("z", "fAkE://").unwrap();

        let mut exp_info = BTreeMap::default();
        exp_info.insert("MEMORY", "memory://");
        exp_info.insert("Z", "fAkE://");
        assert_eq!(exp_info, storage.mounted());
    }

    #[test]
    fn test_storage_cd_and_cwd_ok() {
        let mut storage = Storage::default();
        storage.mount("other", "memory://").unwrap();
        assert_eq!("MEMORY:/", storage.cwd());
        storage.cd("other:/").unwrap();
        assert_eq!("OTHER:/", storage.cwd());
        storage.cd("memory:").unwrap();
        assert_eq!("MEMORY:/", storage.cwd());
    }

    #[test]
    fn test_storage_cd_errors() {
        let mut storage = Storage::default();
        assert_eq!("Invalid drive name ''", format!("{}", storage.cd(":foo").unwrap_err()));
        assert_eq!("Invalid path 'a:b\\c'", format!("{}", storage.cd("a:b\\c").unwrap_err()));
        assert_eq!("Cannot cd to a file", format!("{}", storage.cd("foo:bar.bas").unwrap_err()));
        assert_eq!("Drive 'A' is not mounted", format!("{}", storage.cd("a:").unwrap_err()));
    }

    #[test]
    fn test_storage_file_ops_with_absolute_paths() {
        let mut storage = Storage::default();
        storage.mount("other", "memory://").unwrap();

        block_on(storage.put("other:/f1", "some text")).unwrap();
        block_on(storage.put("other:f2", "other text")).unwrap();
        {
            // Ensure that the put operations were routed to the correct objects.
            let memory_drive = storage.drives.get(&DriveKey::new("memory").unwrap()).unwrap();
            assert_eq!(0, block_on(memory_drive.drive.enumerate()).unwrap().dirents().len());
            let other_drive = storage.drives.get(&DriveKey::new("other").unwrap()).unwrap();
            assert_eq!(2, block_on(other_drive.drive.enumerate()).unwrap().dirents().len());
        }

        assert_eq!(0, block_on(storage.enumerate("memory:")).unwrap().dirents().len());
        assert_eq!(0, block_on(storage.enumerate("memory:")).unwrap().dirents().len());
        assert_eq!(2, block_on(storage.enumerate("other:/")).unwrap().dirents().len());
        assert_eq!(2, block_on(storage.enumerate("other:/")).unwrap().dirents().len());

        assert_eq!("some text", block_on(storage.get("OTHER:f1")).unwrap());
        assert_eq!("other text", block_on(storage.get("OTHER:/f2")).unwrap());

        block_on(storage.delete("other:/f2")).unwrap();
        assert_eq!(0, block_on(storage.enumerate("memory:")).unwrap().dirents().len());
        assert_eq!(1, block_on(storage.enumerate("other:")).unwrap().dirents().len());
        block_on(storage.delete("other:f1")).unwrap();
        assert_eq!(0, block_on(storage.enumerate("memory:")).unwrap().dirents().len());
        assert_eq!(0, block_on(storage.enumerate("other:")).unwrap().dirents().len());
    }

    #[test]
    fn test_storage_file_ops_with_relative_paths() {
        let mut storage = Storage::default();
        storage.mount("other", "memory://").unwrap();

        block_on(storage.put("/f1", "some text")).unwrap();
        block_on(storage.put("f2", "other text")).unwrap();
        {
            // Ensure that the put operations were routed to the correct objects.
            let memory_drive = storage.drives.get(&DriveKey::new("memory").unwrap()).unwrap();
            assert_eq!(2, block_on(memory_drive.drive.enumerate()).unwrap().dirents().len());
            let other_drive = storage.drives.get(&DriveKey::new("other").unwrap()).unwrap();
            assert_eq!(0, block_on(other_drive.drive.enumerate()).unwrap().dirents().len());
        }

        assert_eq!(2, block_on(storage.enumerate("")).unwrap().dirents().len());
        assert_eq!(2, block_on(storage.enumerate("/")).unwrap().dirents().len());
        assert_eq!(0, block_on(storage.enumerate("other:")).unwrap().dirents().len());
        assert_eq!(0, block_on(storage.enumerate("other:/")).unwrap().dirents().len());

        assert_eq!("some text", block_on(storage.get("f1")).unwrap());
        assert_eq!("other text", block_on(storage.get("/f2")).unwrap());

        block_on(storage.delete("/f2")).unwrap();
        assert_eq!(1, block_on(storage.enumerate("")).unwrap().dirents().len());
        assert_eq!(0, block_on(storage.enumerate("other:")).unwrap().dirents().len());
        block_on(storage.delete("f1")).unwrap();
        assert_eq!(0, block_on(storage.enumerate("")).unwrap().dirents().len());
        assert_eq!(0, block_on(storage.enumerate("other:")).unwrap().dirents().len());
    }

    #[test]
    fn test_storage_delete_errors() {
        let mut storage = Storage::default();
        assert_eq!(
            "Invalid drive name ''",
            format!("{}", block_on(storage.delete(":foo")).unwrap_err())
        );
        assert_eq!(
            "Invalid path 'a:b\\c'",
            format!("{}", block_on(storage.delete("a:b\\c")).unwrap_err())
        );
        assert_eq!(
            "Missing file name in path 'a:'",
            format!("{}", block_on(storage.delete("a:")).unwrap_err())
        );
    }

    #[test]
    fn test_storage_enumerate_errors() {
        let storage = Storage::default();
        assert_eq!(
            "Invalid drive name ''",
            format!("{}", block_on(storage.enumerate(":foo")).unwrap_err())
        );
        assert_eq!(
            "Invalid path 'a:b\\c'",
            format!("{}", block_on(storage.enumerate("a:b\\c")).unwrap_err())
        );
        assert_eq!(
            "Location 'a:/foo' is not a directory",
            format!("{}", block_on(storage.enumerate("a:/foo")).unwrap_err())
        );
    }

    #[test]
    fn test_storage_get_errors() {
        let storage = Storage::default();
        assert_eq!(
            "Invalid drive name ''",
            format!("{}", block_on(storage.get(":foo")).unwrap_err())
        );
        assert_eq!(
            "Invalid path 'a:b\\c'",
            format!("{}", block_on(storage.get("a:b\\c")).unwrap_err())
        );
        assert_eq!(
            "Missing file name in path 'a:'",
            format!("{}", block_on(storage.get("a:")).unwrap_err())
        );
    }

    #[test]
    fn test_storage_put_errors() {
        let mut storage = Storage::default();
        assert_eq!(
            "Invalid drive name ''",
            format!("{}", block_on(storage.put(":foo", "")).unwrap_err())
        );
        assert_eq!(
            "Invalid path 'a:b\\c'",
            format!("{}", block_on(storage.put("a:b\\c", "")).unwrap_err())
        );
        assert_eq!(
            "Missing file name in path 'a:'",
            format!("{}", block_on(storage.put("a:", "")).unwrap_err())
        );
    }

    #[test]
    fn test_storage_system_path_ok() {
        let dir = tempfile::tempdir().unwrap();
        let dir = dir.path().canonicalize().unwrap();

        let mut storage = Storage::default();
        storage
            .attach(
                "c",
                &format!("file://{}", dir.display()),
                Box::from(DirectoryDrive::new(dir.clone()).unwrap()),
            )
            .unwrap();

        assert!(storage.system_path("memory:/foo").unwrap().is_none());
        assert_eq!(dir.join("some name"), storage.system_path("c:/some name").unwrap().unwrap());
        assert_eq!(dir.join("xyz"), storage.system_path("c:xyz").unwrap().unwrap());
    }

    #[test]
    fn test_storage_system_path_of_cwd() {
        let dir = tempfile::tempdir().unwrap();
        let dir = dir.path().canonicalize().unwrap();

        let mut storage = Storage::default();
        storage
            .attach(
                "c",
                &format!("file://{}", dir.display()),
                Box::from(DirectoryDrive::new(dir.clone()).unwrap()),
            )
            .unwrap();

        assert!(storage.system_path(&storage.cwd()).unwrap().is_none());

        storage.cd("c:/").unwrap();
        assert_eq!(dir, storage.system_path(&storage.cwd()).unwrap().unwrap());
    }

    #[test]
    fn test_storage_system_path_errors() {
        let dir = tempfile::tempdir().unwrap();
        let dir = dir.path();

        let mut storage = Storage::default();
        storage
            .attach(
                "c",
                &format!("file://{}", dir.display()),
                Box::from(DirectoryDrive::new(dir).unwrap()),
            )
            .unwrap();

        assert_eq!(
            "Too many / separators in path 'c:a/b'",
            format!("{}", storage.system_path("c:a/b").unwrap_err())
        );
        assert_eq!("Invalid path 'c:..'", format!("{}", storage.system_path("c:..").unwrap_err()));
    }
}
