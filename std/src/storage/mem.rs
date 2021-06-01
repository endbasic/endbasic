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

use crate::storage::{DiskSpace, Drive, DriveFactory, DriveFiles, Metadata};
use async_trait::async_trait;
use std::collections::{BTreeMap, HashMap};
use std::io;
use std::str;

/// A drive that records all data in memory only.
#[derive(Default)]
pub struct InMemoryDrive {
    programs: HashMap<String, String>,

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
        for (name, contents) in &self.programs {
            entries.insert(name.clone(), Metadata { date, length: contents.len() as u64 });
        }
        Ok(DriveFiles::new(entries, self.fake_disk_quota, self.fake_disk_free))
    }

    async fn get(&self, name: &str) -> io::Result<String> {
        match self.programs.get(name) {
            Some(content) => Ok(content.to_owned()),
            None => Err(io::Error::new(io::ErrorKind::NotFound, "Entry not found")),
        }
    }

    async fn put(&mut self, name: &str, content: &str) -> io::Result<()> {
        self.programs.insert(name.to_owned(), content.to_owned());
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

    #[test]
    fn test_inmemorydrive_system_path() {
        let drive = InMemoryDrive::default();
        assert!(drive.system_path("foo").is_none());
    }
}
