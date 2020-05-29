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

//! Implementation of a `FileStore` backed by an on-disk directory.

use endbasic_core::program::{Metadata, Store};
use std::collections::BTreeMap;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::PathBuf;

/// An implementation of `Store` backed by an on-disk directory.
pub struct FileStore {
    /// Path to the directory containing all entries backed by this `Store`.  The directory may
    /// contain files that are not EndBASIC programs, and that's OK, but those files will not be
    /// accessible through this interface.
    dir: PathBuf,
}

impl FileStore {
    /// Creates a new store backed by the `dir` directory.
    pub fn new<P: Into<PathBuf>>(dir: P) -> Self {
        Self { dir: dir.into() }
    }
}

impl Store for FileStore {
    fn delete(&mut self, name: &str) -> io::Result<()> {
        let path = self.dir.join(name);
        fs::remove_file(path)
    }

    fn enumerate(&self) -> io::Result<BTreeMap<String, Metadata>> {
        let mut entries = BTreeMap::default();
        match fs::read_dir(&self.dir) {
            Ok(dirents) => {
                for de in dirents {
                    let de = de?;

                    let file_type = de.file_type()?;
                    if !file_type.is_file() && !file_type.is_symlink() {
                        // Silently ignore entries we cannot handle.
                        continue;
                    }

                    // This follows symlinks for cross-platform simplicity, but it is ugly.  I don't
                    // expect symlinks in the programs directory anyway.  If we want to handle this
                    // better, we'll have to add a way to report file types.
                    let metadata = fs::metadata(de.path())?;
                    let date = time::OffsetDateTime::from(metadata.modified()?)
                        .to_offset(time::UtcOffset::current_local_offset());
                    let length = metadata.len();

                    entries.insert(
                        de.file_name().to_string_lossy().to_string(),
                        Metadata { date, length },
                    );
                }
            }
            Err(e) => {
                if e.kind() != io::ErrorKind::NotFound {
                    return Err(e);
                }
            }
        }
        Ok(entries)
    }

    fn get(&self, name: &str) -> io::Result<String> {
        let path = self.dir.join(name);
        let input = File::open(&path)?;
        let mut content = String::new();
        io::BufReader::new(input).read_to_string(&mut content)?;
        Ok(content)
    }

    fn put(&mut self, name: &str, content: &str) -> io::Result<()> {
        let path = self.dir.join(name);
        let dir = path.parent().expect("Must be a filename with a directory");
        fs::create_dir_all(&dir)?;

        // TODO(jmmv): Should back up existing files.
        let output = OpenOptions::new().create(true).write(true).truncate(true).open(path)?;
        let mut writer = io::BufWriter::new(output);
        writer.write_all(content.as_bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use endbasic_core::program::Metadata;
    use std::io::BufRead;
    use std::path::Path;

    /// Reads `path` and checks that its contents match `exp_lines`.
    fn check_file(path: &Path, exp_lines: &[&str]) {
        let file = File::open(path).unwrap();
        let reader = io::BufReader::new(file);
        let mut lines = vec![];
        for line in reader.lines() {
            lines.push(line.unwrap());
        }
        assert_eq!(exp_lines, lines.as_slice());
    }

    /// Creates `path` with the contents in `lines` and with a deterministic modification time.
    fn write_file(path: &Path, lines: &[&str]) {
        let mut file = fs::OpenOptions::new()
            .create(true)
            .truncate(false) // Should not be creating the same file more than once.
            .write(true)
            .open(path)
            .unwrap();
        for line in lines {
            file.write_fmt(format_args!("{}\n", line)).unwrap();
        }
        drop(file);

        filetime::set_file_mtime(path, filetime::FileTime::from_unix_time(1_588_757_875, 0))
            .unwrap();
    }

    #[test]
    fn test_delete_ok() {
        let dir = tempfile::tempdir().unwrap();
        write_file(&dir.path().join("a.bas"), &[]);
        write_file(&dir.path().join("a.bat"), &[]);

        let mut store = FileStore::new(&dir.path());
        store.delete("a.bas").unwrap();
        assert!(!dir.path().join("a.bas").exists());
        assert!(dir.path().join("a.bat").exists());
    }

    #[test]
    fn test_delete_missing_file() {
        let dir = tempfile::tempdir().unwrap();

        // TODO(jmmv): This is very ugly... need better error reporting in general, not just for
        // this one case.
        let enoent_message = if cfg!(target_os = "windows") {
            "The system cannot find the file specified. (os error 2)"
        } else {
            "No such file or directory (os error 2)"
        };

        let mut store = FileStore::new(&dir.path());
        assert_eq!(enoent_message, format!("{}", store.delete("a.bas").unwrap_err()));
    }

    #[test]
    fn test_enumerate_nothing() {
        let dir = tempfile::tempdir().unwrap();

        let store = FileStore::new(&dir.path());
        assert!(store.enumerate().unwrap().is_empty());
    }

    #[test]
    fn test_enumerate_some_files() {
        let dir = tempfile::tempdir().unwrap();
        write_file(&dir.path().join("empty.bas"), &[]);
        write_file(&dir.path().join("some file.bas"), &["this is not empty"]);

        let store = FileStore::new(&dir.path());
        let entries = store.enumerate().unwrap();
        assert_eq!(2, entries.len());
        let date = time::OffsetDateTime::from_unix_timestamp(1_588_757_875);
        assert_eq!(&Metadata { date: date, length: 0 }, entries.get("empty.bas").unwrap());
        assert_eq!(&Metadata { date: date, length: 18 }, entries.get("some file.bas").unwrap());
    }

    #[test]
    fn test_enumerate_treats_missing_dir_as_empty() {
        let dir = tempfile::tempdir().unwrap();
        let store = FileStore::new(dir.path().join("does-not-exist"));
        assert!(store.enumerate().unwrap().is_empty());
    }

    #[test]
    fn test_enumerate_ignores_non_files() {
        let dir = tempfile::tempdir().unwrap();
        fs::create_dir(dir.path().join("will-be-ignored")).unwrap();
        let store = FileStore::new(&dir.path());
        assert!(store.enumerate().unwrap().is_empty());
    }

    #[cfg(not(target_os = "windows"))]
    #[test]
    fn test_enumerate_follows_symlinks() {
        use std::os::unix::fs as unix_fs;

        let dir = tempfile::tempdir().unwrap();
        write_file(&dir.path().join("some file.bas"), &["this is not empty"]);
        unix_fs::symlink(&Path::new("some file.bas"), &dir.path().join("a link.bas")).unwrap();

        let store = FileStore::new(&dir.path());
        let entries = store.enumerate().unwrap();
        assert_eq!(2, entries.len());
        let metadata =
            Metadata { date: time::OffsetDateTime::from_unix_timestamp(1_588_757_875), length: 18 };
        assert_eq!(&metadata, entries.get("some file.bas").unwrap());
        assert_eq!(&metadata, entries.get("a link.bas").unwrap());
    }

    #[test]
    fn test_enumerate_fails_on_non_directory() {
        let dir = tempfile::tempdir().unwrap();

        // TODO(jmmv): This is very ugly... need better error reporting in general, not just for
        // this one case.
        let enotdir_message = if cfg!(target_os = "windows") {
            "The directory name is invalid. (os error 267)"
        } else {
            "Not a directory (os error 20)"
        };

        let file = dir.path().join("not-a-dir");
        write_file(&file, &[]);
        let store = FileStore::new(&file);
        assert_eq!(enotdir_message, format!("{}", store.enumerate().unwrap_err()));
    }

    #[test]
    fn test_get() {
        let dir = tempfile::tempdir().unwrap();
        write_file(&dir.path().join("some file.bas"), &["one line", "two lines"]);

        let store = FileStore::new(&dir.path());
        assert_eq!("one line\ntwo lines\n", store.get("some file.bas").unwrap());
    }

    #[test]
    fn test_put() {
        let dir = tempfile::tempdir().unwrap();

        let mut store = FileStore::new(&dir.path());
        store.put("some file.bas", "a b c\nd e\n").unwrap();
        check_file(&dir.path().join("some file.bas"), &["a b c", "d e"]);
    }
}
