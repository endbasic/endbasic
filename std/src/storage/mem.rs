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

//! In-memory implementation of the storage system.

use crate::storage::{DiskSpace, Drive, DriveFactory, DriveFiles, FileAcls, Metadata};
use async_trait::async_trait;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::io;
use std::str;

/// A drive that records all data in memory only.
#[derive(Default)]
pub struct InMemoryDrive {
    programs: HashMap<String, (String, HashSet<String>)>,

    // TODO(jmmv): These fields are currently exposed only to allow testing for the consumers of
    // these details and are not enforced in the drive.  It might be nice to actually implement
    // proper support for this.
    pub(crate) fake_disk_quota: Option<DiskSpace>,
    pub(crate) fake_disk_free: Option<DiskSpace>,
}

#[async_trait(?Send)]
impl Drive for InMemoryDrive {
    async fn delete(&mut self, name: &str) -> io::Result<()> {
        match self.programs.remove(name) {
            Some(_) => Ok(()),
            None => Err(io::Error::new(io::ErrorKind::NotFound, "Entry not found")),
        }
    }

    async fn enumerate(&self) -> io::Result<DriveFiles> {
        let date = time::OffsetDateTime::from_unix_timestamp(1_588_757_875);

        let mut entries = BTreeMap::new();
        for (name, (contents, _readers)) in &self.programs {
            entries.insert(name.clone(), Metadata { date, length: contents.len() as u64 });
        }
        Ok(DriveFiles::new(entries, self.fake_disk_quota, self.fake_disk_free))
    }

    async fn get(&self, name: &str) -> io::Result<String> {
        match self.programs.get(name) {
            Some((content, _readers)) => Ok(content.to_owned()),
            None => Err(io::Error::new(io::ErrorKind::NotFound, "Entry not found")),
        }
    }

    async fn get_acls(&self, name: &str) -> io::Result<FileAcls> {
        match self.programs.get(name) {
            Some((_content, readers)) => {
                let mut readers = readers.iter().map(String::to_owned).collect::<Vec<String>>();
                // There is no need to sort the returned ACLs, but doing so simplifies testing...
                // and this in-memory drive exists mostly for testing only.
                readers.sort();
                Ok(FileAcls::default().with_readers(readers))
            }
            None => Err(io::Error::new(io::ErrorKind::NotFound, "Entry not found")),
        }
    }

    async fn put(&mut self, name: &str, content: &str) -> io::Result<()> {
        if let Some((prev_content, _readers)) = self.programs.get_mut(name) {
            *prev_content = content.to_owned();
            return Ok(());
        };
        self.programs.insert(name.to_owned(), (content.to_owned(), HashSet::new()));
        Ok(())
    }

    async fn update_acls(
        &mut self,
        name: &str,
        add: &FileAcls,
        remove: &FileAcls,
    ) -> io::Result<()> {
        let readers = match self.programs.get_mut(name) {
            Some((_content, readers)) => readers,
            None => return Err(io::Error::new(io::ErrorKind::NotFound, "Entry not found")),
        };
        for reader in remove.readers() {
            readers.remove(reader);
        }
        for reader in add.readers() {
            readers.insert(reader.to_owned());
        }
        Ok(())
    }
}

/// Factory for in-memory drives.
#[derive(Default)]
pub struct InMemoryDriveFactory {}

impl DriveFactory for InMemoryDriveFactory {
    fn create(&self, target: &str) -> io::Result<Box<dyn Drive>> {
        if target.is_empty() {
            Ok(Box::from(InMemoryDrive::default()))
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Cannot specify a path to mount an in-memory drive",
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Convenience function to instantiate a `FileAcls` with the `r` readers.
    fn readers(r: &[&str]) -> FileAcls {
        FileAcls::default().with_readers(r.iter().map(|x| x.to_string()).collect::<Vec<String>>())
    }

    #[tokio::test]
    async fn test_inmemorydrive_put_respects_acls() {
        let mut drive = InMemoryDrive::default();
        drive.put("untouched", "some content").await.unwrap();

        drive.put("file", "before").await.unwrap();
        drive.update_acls("file", &readers(&["r1"]), &FileAcls::default()).await.unwrap();

        assert_eq!("before", drive.get("file").await.unwrap());
        assert_eq!(readers(&["r1"]), drive.get_acls("file").await.unwrap());

        drive.put("file", "after").await.unwrap();

        assert_eq!("after", drive.get("file").await.unwrap());
        assert_eq!(readers(&["r1"]), drive.get_acls("file").await.unwrap());
    }

    #[tokio::test]
    async fn test_inmemorydrive_get_update_acls() {
        let mut drive = InMemoryDrive::default();
        drive.put("untouched", "some content").await.unwrap();

        let err =
            drive.update_acls("file", &readers(&["r0"]), &FileAcls::default()).await.unwrap_err();
        assert_eq!(io::ErrorKind::NotFound, err.kind());

        drive.put("file", "some content").await.unwrap();
        assert_eq!(FileAcls::default(), drive.get_acls("file").await.unwrap());

        // Add some new readers and try to remove a non-existing one.
        drive.update_acls("file", &readers(&["r1", "r2"]), &readers(&["r3"])).await.unwrap();
        assert_eq!(readers(&["r1", "r2"]), drive.get_acls("file").await.unwrap());

        // Add a new reader and a duplicate and remove an existing one.
        drive.update_acls("file", &readers(&["r2", "r2", "r3"]), &readers(&["r1"])).await.unwrap();
        assert_eq!(readers(&["r2", "r3"]), drive.get_acls("file").await.unwrap());

        // Make sure other files were not affected.
        assert_eq!(FileAcls::default(), drive.get_acls("untouched").await.unwrap());
    }

    #[test]
    fn test_inmemorydrive_system_path() {
        let drive = InMemoryDrive::default();
        assert!(drive.system_path("foo").is_none());
    }
}
