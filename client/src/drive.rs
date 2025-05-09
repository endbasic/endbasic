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

//! Cloud-based implementation of an EndBASIC storage drive.

use crate::*;
use async_trait::async_trait;
use endbasic_std::storage::{Drive, DriveFactory, DriveFiles, FileAcls, Metadata};
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::io;
use std::rc::Rc;
use std::str;

/// A drive backed by a remote EndBASIC service.
struct CloudDrive {
    service: Rc<RefCell<dyn Service>>,
    username: String,
}

impl CloudDrive {
    /// Creates a new cloud drive against `service` to access the files owned by `username`.
    fn new<S: Into<String>>(service: Rc<RefCell<dyn Service>>, username: S) -> Self {
        let username = username.into();
        Self { service, username }
    }
}

#[async_trait(?Send)]
impl Drive for CloudDrive {
    async fn delete(&mut self, filename: &str) -> io::Result<()> {
        self.service.borrow_mut().delete_file(&self.username, filename).await
    }

    async fn enumerate(&self) -> io::Result<DriveFiles> {
        let response = self.service.borrow_mut().get_files(&self.username).await?;
        let mut entries = BTreeMap::default();
        for e in response.files {
            let date = match time::OffsetDateTime::from_unix_timestamp(e.mtime as i64) {
                Ok(date) => date,
                Err(e) => return Err(io::Error::new(io::ErrorKind::InvalidData, format!("{}", e))),
            };
            entries.insert(e.filename, Metadata { date, length: e.length });
        }
        Ok(DriveFiles::new(
            entries,
            response.disk_quota.map(|x| x.into()),
            response.disk_free.map(|x| x.into()),
        ))
    }

    async fn get(&self, filename: &str) -> io::Result<Vec<u8>> {
        self.service.borrow_mut().get_file(&self.username, filename).await
    }

    async fn get_acls(&self, filename: &str) -> io::Result<FileAcls> {
        self.service.borrow_mut().get_file_acls(&self.username, filename).await
    }

    async fn put(&mut self, filename: &str, content: &[u8]) -> io::Result<()> {
        self.service
            .borrow_mut()
            .patch_file_content(&self.username, filename, content.to_vec())
            .await
    }

    async fn update_acls(
        &mut self,
        filename: &str,
        add: &FileAcls,
        remove: &FileAcls,
    ) -> io::Result<()> {
        self.service.borrow_mut().patch_file_acls(&self.username, filename, add, remove).await
    }
}

/// Factory for cloud drives.
pub struct CloudDriveFactory {
    service: Rc<RefCell<dyn Service>>,
}

impl CloudDriveFactory {
    /// Creates a new cloud drive factory that uses `service` to connect to the remote service.
    pub(crate) fn new(service: Rc<RefCell<dyn Service>>) -> Self {
        Self { service }
    }
}

impl DriveFactory for CloudDriveFactory {
    fn create(&self, target: &str) -> io::Result<Box<dyn Drive>> {
        if !target.is_empty() {
            Ok(Box::from(CloudDrive::new(self.service.clone(), target)))
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Must specify a username to mount a cloud-backed drive",
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;

    #[tokio::test]
    async fn test_clouddrive_delete() {
        let service = Rc::from(RefCell::from(MockService::default()));
        service.borrow_mut().do_login().await;
        let mut drive = CloudDrive::new(service.clone(), "the-user");

        service.borrow_mut().add_mock_delete_file("the-user", "the-filename", Ok(()));
        drive.delete("the-filename").await.unwrap();

        service.take().verify_all_used();
    }

    #[tokio::test]
    async fn test_clouddrive_enumerate() {
        let service = Rc::from(RefCell::from(MockService::default()));
        service.borrow_mut().do_login().await;
        let drive = CloudDrive::new(service.clone(), "the-user");

        service.borrow_mut().add_mock_get_files(
            "the-user",
            Ok(GetFilesResponse {
                files: vec![
                    DirectoryEntry { filename: "one".to_owned(), mtime: 9000, length: 15 },
                    DirectoryEntry { filename: "two".to_owned(), mtime: 8000, length: 17 },
                ],
                disk_quota: Some(DiskSpace::new(10000, 100).into()),
                disk_free: Some(DiskSpace::new(123, 45).into()),
            }),
        );
        let result = drive.enumerate().await.unwrap();
        assert_eq!(2, result.dirents().len());
        assert_eq!(
            &Metadata {
                date: time::OffsetDateTime::from_unix_timestamp(9000).unwrap(),
                length: 15
            },
            result.dirents().get("one").unwrap()
        );
        assert_eq!(
            &Metadata {
                date: time::OffsetDateTime::from_unix_timestamp(8000).unwrap(),
                length: 17
            },
            result.dirents().get("two").unwrap()
        );
        assert_eq!(&DiskSpace::new(10000, 100), result.disk_quota().as_ref().unwrap());
        assert_eq!(&DiskSpace::new(123, 45), result.disk_free().as_ref().unwrap());

        service.take().verify_all_used();
    }

    #[tokio::test]
    async fn test_clouddrive_get() {
        let service = Rc::from(RefCell::from(MockService::default()));
        service.borrow_mut().do_login().await;
        let drive = CloudDrive::new(service.clone(), "the-user");

        service.borrow_mut().add_mock_get_file(
            "the-user",
            "the-filename",
            Ok(b"some content".to_owned()),
        );
        let result = drive.get("the-filename").await.unwrap();
        assert_eq!("some content".as_bytes(), result);

        service.take().verify_all_used();
    }

    #[tokio::test]
    async fn test_clouddrive_get_no_content() {
        let service = Rc::from(RefCell::from(MockService::default()));
        service.borrow_mut().do_login().await;
        let drive = CloudDrive::new(service.clone(), "the-user");

        service.borrow_mut().add_mock_get_file("the-user", "the-filename", Ok(""));
        let result = drive.get("the-filename").await.unwrap();
        assert_eq!("".as_bytes(), result);

        service.take().verify_all_used();
    }

    #[allow(invalid_from_utf8)]
    #[tokio::test]
    async fn test_clouddrive_get_invalid_utf8() {
        const BAD_UTF8: &[u8] = &[0x00, 0xc3, 0x28];
        assert!(str::from_utf8(BAD_UTF8).is_err());

        let service = Rc::from(RefCell::from(MockService::default()));
        service.borrow_mut().do_login().await;
        let drive = CloudDrive::new(service.clone(), "the-user");

        service.borrow_mut().add_mock_get_file("the-user", "the-filename", Ok(BAD_UTF8));
        let result = drive.get("the-filename").await.unwrap();
        assert_eq!(BAD_UTF8, result);

        service.take().verify_all_used();
    }

    #[tokio::test]
    async fn test_clouddrive_get_acls() {
        let service = Rc::from(RefCell::from(MockService::default()));
        service.borrow_mut().do_login().await;
        let drive = CloudDrive::new(service.clone(), "the-user");

        let response = FileAcls { readers: vec!["r1".to_owned(), "r2".to_owned()] };
        service.borrow_mut().add_mock_get_file_acls("the-user", "the-filename", Ok(response));
        let result = drive.get_acls("the-filename").await.unwrap();
        assert_eq!(FileAcls::default().with_readers(["r1".to_owned(), "r2".to_owned()]), result);

        service.take().verify_all_used();
    }

    #[tokio::test]
    async fn test_clouddrive_get_acls_no_readers() {
        let service = Rc::from(RefCell::from(MockService::default()));
        service.borrow_mut().do_login().await;
        let drive = CloudDrive::new(service.clone(), "the-user");

        service.borrow_mut().add_mock_get_file_acls(
            "the-user",
            "the-filename",
            Ok(FileAcls::default()),
        );
        let result = drive.get_acls("the-filename").await.unwrap();
        assert_eq!(FileAcls::default(), result);

        service.take().verify_all_used();
    }

    #[tokio::test]
    async fn test_clouddrive_put_new() {
        let service = Rc::from(RefCell::from(MockService::default()));
        service.borrow_mut().do_login().await;
        let mut drive = CloudDrive::new(service.clone(), "the-user");

        service.borrow_mut().add_mock_patch_file_content(
            "the-user",
            "the-filename",
            "some content",
            Ok(()),
        );
        drive.put("the-filename", b"some content").await.unwrap();

        service.take().verify_all_used();
    }

    #[tokio::test]
    async fn test_clouddrive_put_existing() {
        let service = Rc::from(RefCell::from(MockService::default()));
        service.borrow_mut().do_login().await;
        let mut drive = CloudDrive::new(service.clone(), "the-user");

        service.borrow_mut().add_mock_patch_file_content(
            "the-user",
            "the-filename",
            "some content",
            Ok(()),
        );
        drive.put("the-filename", b"some content").await.unwrap();

        service.borrow_mut().add_mock_patch_file_content(
            "the-user",
            "the-filename",
            "some other content",
            Ok(()),
        );
        drive.put("the-filename", b"some other content").await.unwrap();

        service.take().verify_all_used();
    }

    #[tokio::test]
    async fn test_clouddrive_put_acls() {
        let service = Rc::from(RefCell::from(MockService::default()));
        service.borrow_mut().do_login().await;
        let mut drive = CloudDrive::new(service.clone(), "the-user");

        service.borrow_mut().add_mock_patch_file_acls(
            "the-user",
            "the-filename",
            ["r1".to_owned(), "r2".to_owned()],
            ["r2".to_owned(), "r3".to_owned()],
            Ok(()),
        );
        drive
            .update_acls(
                "the-filename",
                &FileAcls::default().with_readers(["r1".to_owned(), "r2".to_owned()]),
                &FileAcls::default().with_readers(["r2".to_owned(), "r3".to_owned()]),
            )
            .await
            .unwrap();

        service.take().verify_all_used();
    }

    #[test]
    fn test_clouddrive_system_path() {
        let service = Rc::from(RefCell::from(MockService::default()));
        let drive = CloudDrive::new(service, "");
        assert!(drive.system_path("foo").is_none());
    }

    #[test]
    fn test_login_and_mount_other_user() {
        let mut t = ClientTester::default();
        t.get_service().borrow_mut().add_mock_login(
            "mock-username",
            "mock-password",
            Ok(LoginResponse { access_token: AccessToken::new("random token"), motd: vec![] }),
        );
        t.get_service().borrow_mut().add_mock_get_files(
            "mock-username",
            Ok(GetFilesResponse {
                files: vec![DirectoryEntry {
                    filename: "one".to_owned(),
                    mtime: 1622556024,
                    length: 15,
                }],
                disk_quota: Some(DiskSpace::new(10000, 100).into()),
                disk_free: Some(DiskSpace::new(123, 45).into()),
            }),
        );
        t.get_service().borrow_mut().add_mock_get_files(
            "user2",
            Ok(GetFilesResponse {
                files: vec![DirectoryEntry {
                    filename: "two".to_owned(),
                    mtime: 1622556024,
                    length: 17,
                }],
                disk_quota: None,
                disk_free: None,
            }),
        );
        t.run(format!(
            r#"LOGIN "{}", "{}": MOUNT "cloud://user2" AS "x": DIR "cloud:/": DIR "x:/""#,
            "mock-username", "mock-password",
        ))
        .expect_access_token("random token")
        .expect_prints([
            "",
            "    Directory of CLOUD:/",
            "",
            "    Modified              Size    Name",
            "    2021-06-01 14:00        15    one",
            "",
            "    1 file(s), 15 bytes",
            "    123 of 10000 bytes free",
            "",
            "",
            "    Directory of X:/",
            "",
            "    Modified              Size    Name",
            "    2021-06-01 14:00        17    two",
            "",
            "    1 file(s), 17 bytes",
            "",
        ])
        .check();
    }
}
