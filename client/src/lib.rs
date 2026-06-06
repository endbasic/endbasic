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

use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::io;

mod cloud;
pub use cloud::CloudService;
#[cfg(any(test, feature = "testutils"))]
pub mod testutils;

/// Base address of the production REST API.
pub const PROD_API_ADDRESS: &str = "https://service.endbasic.dev/";

/// Representation of some amount of disk space.  Can be used to express both quotas and usage.
#[derive(Debug, Deserialize)]
#[cfg_attr(test, derive(PartialEq, Serialize))]
pub struct DiskSpace {
    /// Number of bytes used or allowed.
    pub bytes: u64,

    /// Number of files used or allowed.
    pub files: u64,
}

/// An opaque access token obtained during authentication and used for all subsequent requests
/// against the server.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[cfg_attr(test, derive(Serialize))]
pub struct AccessToken(String);

impl AccessToken {
    /// Creates a new access token based on the raw `token` string.
    #[cfg(any(test, feature = "testutils"))]
    pub fn new<S: Into<String>>(token: S) -> Self {
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
    /// Access token returned by the server, required for subsequent operations.
    pub access_token: AccessToken,

    /// Message of the day returned by the server.
    pub motd: Vec<String>,
}

/// Representation of a single directory entry as returned by the server.
#[derive(Deserialize)]
#[cfg_attr(test, derive(Debug, Serialize))]
pub struct DirectoryEntry {
    /// Name of the file in the directory.
    pub filename: String,

    /// Last modification timestamp of the file, as UTC seconds since the Epoch.
    pub mtime: u64,

    /// Length of the file, in bytes.
    pub length: u64,
}

/// Representation of a directory enumeration response.
#[derive(Deserialize)]
#[cfg_attr(test, derive(Debug, Serialize))]
pub struct GetFilesResponse {
    /// List of entries in the directory.
    pub files: Vec<DirectoryEntry>,

    /// Total disk quota, if known/applicable.
    pub disk_quota: Option<DiskSpace>,

    /// Available disk quota, if known/applicable.
    pub disk_free: Option<DiskSpace>,
}

/// Representation of a signup request.
#[derive(Debug, Default, Eq, PartialEq, Serialize)]
#[cfg_attr(test, derive(Deserialize))]
pub struct SignupRequest {
    /// Name of the user to create an account for.
    pub username: String,

    /// Password for the new account.
    pub password: String,

    /// Email address for the new account.
    pub email: String,

    /// Whether the new user desires to receive future promotional email or not.
    pub promotional_email: bool,
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
    /// previously-acquired `access_token`.  Returns the list of allowed readers.
    async fn get_file_acls(&mut self, username: &str, filename: &str) -> io::Result<Vec<String>>;

    /// Sends a request to the server to update the contents of `filename` owned by `username` as
    /// specified in `content` with a previously-acquired `access_token`.
    async fn patch_file_content(
        &mut self,
        username: &str,
        filename: &str,
        content: Vec<u8>,
    ) -> io::Result<()>;

    /// Sends a request to the server to update the ACLs of `filename` owned by `username` as
    /// specified in `add_readers` and `remove_readers` with a previously-acquired `access_token`.
    async fn patch_file_acls(
        &mut self,
        username: &str,
        filename: &str,
        add_readers: &Vec<String>,
        remove_readers: &Vec<String>,
    ) -> io::Result<()>;

    /// Sends a request to the server to delete `filename` owned by `username` with a
    /// previously-acquired `access_token`.
    async fn delete_file(&mut self, username: &str, filename: &str) -> io::Result<()>;
}
