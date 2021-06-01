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

use crate::storage::DiskSpace;
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::io;

mod cloud;
pub(crate) use cloud::CloudService;
mod drive;
pub(crate) use drive::CloudDriveFactory;
mod cmds;
pub(crate) use cmds::add_all;

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
    disk_quota: Option<DiskSpace>,
    disk_free: Option<DiskSpace>,
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
}

/// Representation of the response to a file query.
#[derive(Default, Deserialize)]
#[cfg_attr(test, derive(Debug, PartialEq, Serialize))]
pub struct GetFileResponse {
    /// Base64-encoded file content.
    content: Option<String>,

    #[serde(rename = "readers")]
    _readers: Option<Vec<String>>,
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

    #[serde(rename = "remove_readers")]
    _remove_readers: Option<Vec<String>>,

    #[serde(rename = "add_readers")]
    _add_readers: Option<Vec<String>>,
}

impl PatchFileRequest {
    /// Updates the file's content with `content`.  The content is automatically base64-encoded.
    fn with_content<C: AsRef<[u8]>>(mut self, content: C) -> Self {
        self.content = Some(base64::encode(content));
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
