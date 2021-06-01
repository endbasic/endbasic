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

use crate::service::*;
use crate::storage::{Drive, DriveFactory, DriveFiles, Metadata};
use async_trait::async_trait;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::io;
use std::rc::Rc;
use std::str;

/// A drive backed by a remote EndBASIC service.
pub struct CloudDrive {
    service: Rc<RefCell<dyn Service>>,
    access_token: AccessToken,
    username: String,
}

impl CloudDrive {
    /// Creates a new cloud drive against `service` to access the files owned by `username` and
    /// using the `access_token` for authorization.
    pub fn new<S: Into<String>>(
        service: Rc<RefCell<dyn Service>>,
        access_token: AccessToken,
        username: S,
    ) -> Self {
        let username = username.into();
        Self { service, access_token, username }
    }
}

#[async_trait(?Send)]
impl Drive for CloudDrive {
    async fn delete(&mut self, filename: &str) -> io::Result<()> {
        self.service.borrow_mut().delete_file(&self.access_token, &self.username, filename).await
    }

    async fn enumerate(&self) -> io::Result<DriveFiles> {
        let response =
            self.service.borrow_mut().get_files(&self.access_token, &self.username).await?;
        let mut entries = BTreeMap::default();
        for e in response.files {
            let date = time::OffsetDateTime::from_unix_timestamp(e.mtime as i64);
            entries.insert(e.filename, Metadata { date, length: e.length });
        }
        Ok(DriveFiles::new(entries, response.disk_quota, response.disk_free))
    }

    async fn get(&self, filename: &str) -> io::Result<String> {
        let request = GetFileRequest::default().with_get_content();
        let response = self
            .service
            .borrow_mut()
            .get_file(&self.access_token, &self.username, filename, &request)
            .await?;
        match response.decoded_content()? {
            Some(content) => match String::from_utf8(content) {
                Ok(s) => Ok(s),
                Err(e) => Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("Requested file is not valid UTF-8: {}", e),
                )),
            },
            None => Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Server response is missing the file content".to_string(),
            )),
        }
    }

    async fn put(&mut self, filename: &str, content: &str) -> io::Result<()> {
        let request = PatchFileRequest::default().with_content(content.as_bytes());
        self.service
            .borrow_mut()
            .patch_file(&self.access_token, &self.username, filename, &request)
            .await
    }
}

/// Factory for cloud drives.
#[derive(Default)]
pub struct CloudDriveFactory {}

impl DriveFactory for CloudDriveFactory {
    fn create(&self, _target: &str) -> io::Result<Box<dyn Drive>> {
        Err(io::Error::new(
            io::ErrorKind::Other,
            "Mounting other people's drives is not yet supported",
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;

    #[tokio::test]
    async fn test_clouddrive_delete() {
        let service = Rc::from(RefCell::from(MockService::default()));
        let access_token = service.borrow_mut().do_authenticate().await;
        let mut drive = CloudDrive::new(service.clone(), access_token, "the-user");

        service.borrow_mut().add_mock_delete_file("the-user", "the-filename", Ok(()));
        drive.delete("the-filename").await.unwrap();

        service.take().verify_all_used();
    }

    #[tokio::test]
    async fn test_clouddrive_enumerate() {
        let service = Rc::from(RefCell::from(MockService::default()));
        let access_token = service.borrow_mut().do_authenticate().await;
        let drive = CloudDrive::new(service.clone(), access_token, "the-user");

        service.borrow_mut().add_mock_get_files(
            "the-user",
            Ok(GetFilesResponse {
                files: vec![
                    DirectoryEntry { filename: "one".to_owned(), mtime: 9000, length: 15 },
                    DirectoryEntry { filename: "two".to_owned(), mtime: 8000, length: 17 },
                ],
                disk_quota: Some(DiskSpace::new(10000, 100)),
                disk_free: Some(DiskSpace::new(123, 45)),
            }),
        );
        let result = drive.enumerate().await.unwrap();
        assert_eq!(2, result.dirents().len());
        assert_eq!(
            &Metadata { date: time::OffsetDateTime::from_unix_timestamp(9000), length: 15 },
            result.dirents().get("one").unwrap()
        );
        assert_eq!(
            &Metadata { date: time::OffsetDateTime::from_unix_timestamp(8000), length: 17 },
            result.dirents().get("two").unwrap()
        );
        assert_eq!(&DiskSpace::new(10000, 100), result.disk_quota().as_ref().unwrap());
        assert_eq!(&DiskSpace::new(123, 45), result.disk_free().as_ref().unwrap());

        service.take().verify_all_used();
    }

    #[tokio::test]
    async fn test_clouddrive_get() {
        let service = Rc::from(RefCell::from(MockService::default()));
        let access_token = service.borrow_mut().do_authenticate().await;
        let drive = CloudDrive::new(service.clone(), access_token, "the-user");

        let request = GetFileRequest::default().with_get_content();
        let response =
            GetFileResponse { content: Some(base64::encode("some content")), ..Default::default() };
        service.borrow_mut().add_mock_get_file("the-user", "the-filename", request, Ok(response));
        let result = drive.get("the-filename").await.unwrap();
        assert_eq!("some content", result);

        service.take().verify_all_used();
    }

    #[tokio::test]
    async fn test_clouddrive_get_no_content() {
        let service = Rc::from(RefCell::from(MockService::default()));
        let access_token = service.borrow_mut().do_authenticate().await;
        let drive = CloudDrive::new(service.clone(), access_token, "the-user");

        let request = GetFileRequest::default().with_get_content();
        let response = GetFileResponse::default();
        service.borrow_mut().add_mock_get_file("the-user", "the-filename", request, Ok(response));
        let err = drive.get("the-filename").await.unwrap_err();
        assert_eq!(io::ErrorKind::InvalidData, err.kind());
        assert!(format!("{}", err).contains("missing the file content"));

        service.take().verify_all_used();
    }

    #[tokio::test]
    async fn test_clouddrive_get_invalid_utf8() {
        let service = Rc::from(RefCell::from(MockService::default()));
        let access_token = service.borrow_mut().do_authenticate().await;
        let drive = CloudDrive::new(service.clone(), access_token, "the-user");

        let request = GetFileRequest::default().with_get_content();
        let response = GetFileResponse {
            content: Some(base64::encode([0x00, 0xc3, 0x28])),
            ..Default::default()
        };
        service.borrow_mut().add_mock_get_file("the-user", "the-filename", request, Ok(response));
        let err = drive.get("the-filename").await.unwrap_err();
        assert_eq!(io::ErrorKind::InvalidData, err.kind());
        assert!(format!("{}", err).contains("not valid UTF-8"));

        service.take().verify_all_used();
    }

    #[tokio::test]
    async fn test_clouddrive_put_new() {
        let service = Rc::from(RefCell::from(MockService::default()));
        let access_token = service.borrow_mut().do_authenticate().await;
        let mut drive = CloudDrive::new(service.clone(), access_token, "the-user");

        let request = PatchFileRequest::default().with_content("some content");
        service.borrow_mut().add_mock_patch_file("the-user", "the-filename", request, Ok(()));
        drive.put("the-filename", "some content").await.unwrap();

        service.take().verify_all_used();
    }

    #[tokio::test]
    async fn test_clouddrive_put_existing() {
        let service = Rc::from(RefCell::from(MockService::default()));
        let access_token = service.borrow_mut().do_authenticate().await;
        let mut drive = CloudDrive::new(service.clone(), access_token, "the-user");

        let request = PatchFileRequest::default().with_content("some content");
        service.borrow_mut().add_mock_patch_file("the-user", "the-filename", request, Ok(()));
        drive.put("the-filename", "some content").await.unwrap();

        let request = PatchFileRequest::default().with_content("some other content");
        service.borrow_mut().add_mock_patch_file("the-user", "the-filename", request, Ok(()));
        drive.put("the-filename", "some other content").await.unwrap();

        service.take().verify_all_used();
    }

    #[test]
    fn test_clouddrive_system_path() {
        let service = Rc::from(RefCell::from(MockService::default()));
        let drive = CloudDrive::new(service, AccessToken::new(""), "");
        assert!(drive.system_path("foo").is_none());
    }
}
