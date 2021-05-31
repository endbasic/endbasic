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

//! Cloud-based implementation of the EndBASIC service client.

use crate::service::*;
use async_trait::async_trait;
use bytes::Buf;
use reqwest::Response;
use reqwest::StatusCode;
use std::collections::HashMap;
use std::io;
use std::str;

/// Base address of the REST API.
const API_ADDRESS: &str = "https://service.endbasic.dev";

/// ID of the client used to authenticate against the Azure AAD B2C endpoint.
const CLIENT_ID: &str = "ca6a2161-3197-4b5b-8857-30d66fd798b3";

/// Address of the ROPC token flow in Azure AAD B2C.
const ROPC_TOKEN_ADDRESS: &str =
    "https://endbasic.b2clogin.com/endbasic.onmicrosoft.com/b2c_1_ROPC/oauth2/v2.0/token";

/// Converts a `reqwest::Response` to an `io::Error`.  The response should have a non-OK status.
async fn http_response_to_io_error(response: Response) -> io::Error {
    let status = response.status();

    let kind = match status {
        StatusCode::OK => panic!("Should not have been called on a successful request"),

        // Match against the codes we know the server explicitly hands us.
        StatusCode::BAD_REQUEST => io::ErrorKind::InvalidInput,
        StatusCode::INSUFFICIENT_STORAGE => io::ErrorKind::Other,
        StatusCode::INTERNAL_SERVER_ERROR => io::ErrorKind::Other,
        StatusCode::NOT_FOUND => io::ErrorKind::NotFound,
        StatusCode::PAYLOAD_TOO_LARGE => io::ErrorKind::InvalidInput,
        StatusCode::SERVICE_UNAVAILABLE => io::ErrorKind::AddrNotAvailable,
        StatusCode::UNAUTHORIZED => io::ErrorKind::PermissionDenied,

        _ => io::ErrorKind::Other,
    };

    match response.text().await {
        Ok(text) => io::Error::new(
            kind,
            format!("HTTP request returned status {} with text '{}'", status, text),
        ),
        Err(e) => io::Error::new(
            kind,
            format!("HTTP request returned status {} and failed to get text due to {}", status, e),
        ),
    }
}

/// Converts a `reqwest::Error` to an `io::Error`.
fn reqwest_error_to_io_error(e: reqwest::Error) -> io::Error {
    io::Error::new(io::ErrorKind::Other, format!("{}", e))
}

#[derive(Default)]
pub(crate) struct CloudService {
    client: reqwest::Client,
}

#[async_trait(?Send)]
impl Service for CloudService {
    async fn authenticate(&mut self, username: &str, password: &str) -> io::Result<AccessToken> {
        let scope = format!("openid {}", CLIENT_ID);
        let params = [
            ("username", username),
            ("password", password),
            ("grant_type", "password"),
            ("scope", &scope),
            ("client_id", CLIENT_ID),
            ("response_type", "token"),
        ];

        let response = self
            .client
            .post(ROPC_TOKEN_ADDRESS)
            .form(&params)
            .send()
            .await
            .map_err(reqwest_error_to_io_error)?;
        let json = response.text().await.map_err(reqwest_error_to_io_error)?;

        let fields: HashMap<String, String> = serde_json::from_str(&json)?;
        match fields.get("access_token") {
            Some(token) => Ok(AccessToken::new(token)),
            None => Err(io::Error::new(io::ErrorKind::PermissionDenied, "Authentication failed")),
        }
    }

    async fn login(
        &mut self,
        access_token: &AccessToken,
        request: &LoginRequest,
    ) -> io::Result<LoginResult> {
        let response = self
            .client
            .post(&format!("{}/api/login", API_ADDRESS))
            .body(serde_json::to_vec(&request)?)
            .bearer_auth(access_token.as_str())
            .send()
            .await
            .map_err(reqwest_error_to_io_error)?;
        match response.status() {
            reqwest::StatusCode::OK => {
                let bytes = response.bytes().await.map_err(reqwest_error_to_io_error)?;
                let response: LoginResponse = serde_json::from_reader(bytes.reader())?;
                Ok(Ok(response))
            }
            reqwest::StatusCode::NOT_FOUND => {
                let bytes = response.bytes().await.map_err(reqwest_error_to_io_error)?;
                let response: ErrorResponse = serde_json::from_reader(bytes.reader())?;
                Ok(Err(response))
            }
            _ => Err(http_response_to_io_error(response).await),
        }
    }
}

#[cfg(test)]
mod tests {
    //! Tests against the real EndBASIC service.
    //!
    //! These tests are configured with the username/password of a test account that we know exists,
    //! but that limits the kind of testing we can do (especially around authentication/login).
    //! We could instead mock out the HTTP client to inject arbitrary responses in our tests, which
    //! would allow us to validate JSON deserialization and the like... but then the tests would be
    //! so unrealistic as to not be useful.

    use super::*;
    use std::env;

    /// Sets up a new client and authenticates against the server using the username and password
    /// passed in via environment variables.
    async fn setup_with_auth() -> (CloudService, AccessToken) {
        let username = env::var("TEST_ACCOUNT_USERNAME").expect("Expected env config not found");
        let password = env::var("TEST_ACCOUNT_PASSWORD").expect("Expected env config not found");

        let mut service = CloudService::default();
        let access_token = service.authenticate(&username, &password).await.unwrap();

        (service, access_token)
    }

    #[tokio::test]
    #[ignore = "Requires environment configuration and is expensive"]
    async fn test_authenticate_bad_password() {
        let username = env::var("TEST_ACCOUNT_USERNAME").expect("Expected env config not found");
        let password = "this is an invalid password for the test account";

        let mut service = CloudService::default();
        let err = service.authenticate(&username, &password).await.unwrap_err();
        assert_eq!(io::ErrorKind::PermissionDenied, err.kind());
    }

    #[tokio::test]
    #[ignore = "Requires environment configuration and is expensive"]
    async fn test_login() {
        let (mut service, access_token) = setup_with_auth().await;

        let request = LoginRequest { data: HashMap::default() };
        match service.login(&access_token, &request).await.unwrap() {
            Ok(response) => {
                assert!(!response.motd.is_empty());
            }
            Err(response) => {
                assert!(response.missing_data.is_empty());
            }
        }
    }
}
