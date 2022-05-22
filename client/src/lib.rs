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

//! EndBASIC service client.

// Keep these in sync with other top-level files.
#![allow(clippy::await_holding_refcell_ref)]
#![allow(clippy::collapsible_else_if)]
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(unused, unused_extern_crates, unused_import_braces, unused_qualifications)]
#![warn(unsafe_code)]

use async_trait::async_trait;
use endbasic_std::storage::DiskSpace;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::io;

mod cloud;
pub use cloud::CloudService;
mod cmds;
pub use cmds::add_all;
mod drive;
pub(crate) use drive::CloudDriveFactory;
#[cfg(test)]
pub(crate) mod testutils;

/// Base address of the production REST API.
pub const PROD_API_ADDRESS: &str = "https://service.endbasic.dev/";

/// Wrapper over `DiskSpace` to implement (de)serialization.
#[derive(Debug, Deserialize)]
#[cfg_attr(test, derive(PartialEq, Serialize))]
struct SerdeDiskSpace {
    bytes: u64,
    files: u64,
}

impl From<DiskSpace> for SerdeDiskSpace {
    fn from(ds: DiskSpace) -> Self {
        SerdeDiskSpace { bytes: ds.bytes, files: ds.files }
    }
}

impl From<SerdeDiskSpace> for DiskSpace {
    fn from(sds: SerdeDiskSpace) -> Self {
        DiskSpace { bytes: sds.bytes, files: sds.files }
    }
}

/// An opaque access token obtained during authentication and used for all subsequent requests
/// against the server.
#[derive(Clone, Debug, PartialEq)]
pub struct AccessToken(String);

impl AccessToken {
    /// Creates a new access token based on the raw `token` string.
    pub(crate) fn new<S: Into<String>>(token: S) -> Self {
        Self(token.into())
    }

    /// Obtains the textual representation of the token so that it can be sent back to the server.
    pub(crate) fn as_str(&self) -> &str {
        &self.0
    }
}

/// Representation of the details of an error response.
#[derive(Deserialize)]
#[cfg_attr(test, derive(Debug, Serialize))]
pub struct ErrorResponse {
    pub(crate) message: String,

    #[serde(default)]
    pub(crate) missing_data: Vec<String>,
}

/// Representation of a login request.
#[derive(Debug, Serialize, PartialEq)]
#[cfg_attr(test, derive(Deserialize))]
pub struct LoginRequest {
    #[serde(default = "HashMap::default")]
    data: HashMap<String, String>,
}

/// Representation of a login response.
#[derive(Deserialize)]
#[cfg_attr(test, derive(Debug, Serialize))]
pub struct LoginResponse {
    username: String,
    motd: Vec<String>,
}

/// Representation of a single directory entry as returned by the server.
#[derive(Deserialize)]
#[cfg_attr(test, derive(Debug, Serialize))]
pub struct DirectoryEntry {
    filename: String,
    mtime: u64,
    length: u64,
}

/// Representation of a directory enumeration response.
#[derive(Deserialize)]
#[cfg_attr(test, derive(Debug, Serialize))]
pub struct GetFilesResponse {
    files: Vec<DirectoryEntry>,
    disk_quota: Option<SerdeDiskSpace>,
    disk_free: Option<SerdeDiskSpace>,
}

/// Representation of a file query.
#[derive(Debug, Default, PartialEq, Serialize)]
#[cfg_attr(test, derive(Deserialize))]
pub struct GetFileRequest {
    get_content: bool,
    get_readers: bool,
}

impl GetFileRequest {
    /// Requests the file's content from the server.
    fn with_get_content(mut self) -> Self {
        self.get_content = true;
        self
    }

    /// Requests the file's readers from the server.
    fn with_get_readers(mut self) -> Self {
        self.get_readers = true;
        self
    }
}

/// Representation of the response to a file query.
#[derive(Default, Deserialize)]
#[cfg_attr(test, derive(Debug, PartialEq, Serialize))]
pub struct GetFileResponse {
    /// Base64-encoded file content.
    content: Option<String>,

    readers: Option<Vec<String>>,
}

impl GetFileResponse {
    /// Processes the content of the response, ensuring it is valid base64.
    fn decoded_content(&self) -> io::Result<Option<Vec<u8>>> {
        match self.content.as_ref() {
            Some(content) => match base64::decode(content) {
                Ok(content) => Ok(Some(content)),
                Err(e) => Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("File content is not properly base64-encoded: {}", e),
                )),
            },
            None => Ok(None),
        }
    }
}

/// Representation of an atomic file update.
#[derive(Debug, Default, PartialEq, Serialize)]
#[cfg_attr(test, derive(Deserialize))]
pub struct PatchFileRequest {
    /// Base64-encoded file content.
    content: Option<String>,

    add_readers: Option<Vec<String>>,
    remove_readers: Option<Vec<String>>,
}

impl PatchFileRequest {
    /// Updates the file's content with `content`.  The content is automatically base64-encoded.
    fn with_content<C: AsRef<[u8]>>(mut self, content: C) -> Self {
        self.content = Some(base64::encode(content));
        self
    }

    /// Adds `readers` to the file's reader ACLs.
    #[cfg(test)]
    fn with_add_readers<R: Into<Vec<String>>>(mut self, readers: R) -> Self {
        self.add_readers = Some(readers.into());
        self
    }

    /// Removes `readers` from the file's reader ACLs.
    #[cfg(test)]
    fn with_remove_readers<R: Into<Vec<String>>>(mut self, readers: R) -> Self {
        self.remove_readers = Some(readers.into());
        self
    }
}

/// Response to a login request, which varies in type depending on whether the login completed
/// successfully or failed due to insufficient information.
pub type LoginResult = Result<LoginResponse, ErrorResponse>;

/// Abstract interface to interact with an EndBASIC service server.
#[async_trait(?Send)]
pub trait Service {
    /// Sends an authentication request to the service with `username` and `password` to obtain an
    /// access token for the session.
    async fn authenticate(&mut self, username: &str, password: &str) -> io::Result<AccessToken>;

    /// Sends a login `request` to the server with a previously-acquired `access_token`.
    async fn login(
        &mut self,
        access_token: &AccessToken,
        request: &LoginRequest,
    ) -> io::Result<LoginResult>;

    /// Sends a request to the server to obtain the list of files owned by `username` with a
    /// previously-acquired `access_token`.
    async fn get_files(
        &mut self,
        access_token: &AccessToken,
        username: &str,
    ) -> io::Result<GetFilesResponse>;

    /// Sends a request to the server to obtain the metadata and/or the contents of `filename` owned
    /// by `username` as specified in `request` with a previously-acquired `access_token`.
    async fn get_file(
        &mut self,
        access_token: &AccessToken,
        username: &str,
        filename: &str,
        request: &GetFileRequest,
    ) -> io::Result<GetFileResponse>;

    /// Sends a request to the server to update the metadata and/or the contents of `filename` owned
    /// by `username` as specified in `request` with a previously-acquired `access_token`.
    async fn patch_file(
        &mut self,
        access_token: &AccessToken,
        username: &str,
        filename: &str,
        request: &PatchFileRequest,
    ) -> io::Result<()>;

    /// Sends a request to the server to delete `filename` owned by `username` with a
    /// previously-acquired `access_token`.
    async fn delete_file(
        &mut self,
        access_token: &AccessToken,
        username: &str,
        filename: &str,
    ) -> io::Result<()>;
}
