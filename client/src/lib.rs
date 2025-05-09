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
use endbasic_std::storage::{DiskSpace, FileAcls};
use serde::{Deserialize, Serialize};
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
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[cfg_attr(test, derive(Serialize))]
pub struct AccessToken(String);

impl AccessToken {
    /// Creates a new access token based on the raw `token` string.
    #[cfg(test)]
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
}

/// Representation of a login response.
#[derive(Deserialize)]
#[cfg_attr(test, derive(Debug, Serialize))]
pub struct LoginResponse {
    pub(crate) access_token: AccessToken,
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

/// Representation of a signup request.
#[derive(Debug, Default, Eq, PartialEq, Serialize)]
#[cfg_attr(test, derive(Deserialize))]
pub struct SignupRequest {
    username: String,
    password: String,
    email: String,
    promotional_email: bool,
}

/// Abstract interface to interact with an EndBASIC service server.
#[async_trait(?Send)]
pub trait Service {
    /// Interactively creates an account based on the details provided in `request`.
    async fn signup(&mut self, request: &SignupRequest) -> io::Result<()>;

    /// Sends an authentication request to the service with `username` and `password` to obtain an
    /// access token for the session.
    ///
    /// If logging is successful, the access token is cached for future retrieval.
    async fn login(&mut self, username: &str, password: &str) -> io::Result<LoginResponse>;

    /// Logs out from the service and clears the access token from this object.
    async fn logout(&mut self) -> io::Result<()>;

    /// Checks if there is an active session against the service.
    fn is_logged_in(&self) -> bool;

    /// Returns the logged in username if there is an active session.
    fn logged_in_username(&self) -> Option<String>;

    /// Sends a request to the server to obtain the list of files owned by `username` with a
    /// previously-acquired `access_token`.
    async fn get_files(&mut self, username: &str) -> io::Result<GetFilesResponse>;

    /// Sends a request to the server to obtain the contents of `filename` owned by `username` with a
    /// previously-acquired `access_token`.
    async fn get_file(&mut self, username: &str, filename: &str) -> io::Result<Vec<u8>>;

    /// Sends a request to the server to obtain the ACLs of `filename` owned by `username` with a
    /// previously-acquired `access_token`.
    async fn get_file_acls(&mut self, username: &str, filename: &str) -> io::Result<FileAcls>;

    /// Sends a request to the server to update the contents of `filename` owned by `username` as
    /// specified in `content` with a previously-acquired `access_token`.
    async fn patch_file_content(
        &mut self,
        username: &str,
        filename: &str,
        content: Vec<u8>,
    ) -> io::Result<()>;

    /// Sends a request to the server to update the ACLs of `filename` owned by `username` as
    /// specified in `add` and `remove` with a previously-acquired `access_token`.
    async fn patch_file_acls(
        &mut self,
        username: &str,
        filename: &str,
        add: &FileAcls,
        remove: &FileAcls,
    ) -> io::Result<()>;

    /// Sends a request to the server to delete `filename` owned by `username` with a
    /// previously-acquired `access_token`.
    async fn delete_file(&mut self, username: &str, filename: &str) -> io::Result<()>;
}
