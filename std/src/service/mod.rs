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
use std::collections::HashMap;
use std::io;

mod cloud;
pub(crate) use cloud::CloudService;
mod cmds;
pub(crate) use cmds::add_all;

/// An opaque access token obtained during authentication and used for all subsequent requests
/// against the server.
#[derive(Debug, PartialEq)]
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
}
