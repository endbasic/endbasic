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
use reqwest::header::HeaderMap;
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
#[cfg_attr(test, derive(Clone))]
pub(crate) struct CloudService {
    client: reqwest::Client,
}

impl CloudService {
    /// Returns the default headers to add to every request.
    fn default_headers(&self) -> HeaderMap {
        let mut headers = HeaderMap::new();
        headers.insert(
            "x-endbasic-client-version",
            env!("CARGO_PKG_VERSION")
                .parse()
                .expect("Package version should have been serializable"),
        );
        headers
    }
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
            .headers(self.default_headers())
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

    async fn get_files(
        &mut self,
        access_token: &AccessToken,
        username: &str,
    ) -> io::Result<GetFilesResponse> {
        let response = self
            .client
            .get(&format!("{}/api/users/{}/files", API_ADDRESS, username))
            .headers(self.default_headers())
            .bearer_auth(access_token.as_str())
            .send()
            .await
            .map_err(reqwest_error_to_io_error)?;
        match response.status() {
            reqwest::StatusCode::OK => {
                let bytes = response.bytes().await.map_err(reqwest_error_to_io_error)?;
                let response: GetFilesResponse = serde_json::from_reader(bytes.reader())?;
                Ok(response)
            }
            _ => Err(http_response_to_io_error(response).await),
        }
    }

    async fn get_file(
        &mut self,
        access_token: &AccessToken,
        username: &str,
        filename: &str,
        request: &GetFileRequest,
    ) -> io::Result<GetFileResponse> {
        let response = self
            .client
            .get(&format!("{}/api/users/{}/files/{}", API_ADDRESS, username, filename))
            .headers(self.default_headers())
            .query(&request)
            .bearer_auth(access_token.as_str())
            .send()
            .await
            .map_err(reqwest_error_to_io_error)?;
        match response.status() {
            reqwest::StatusCode::OK => {
                let bytes = response.bytes().await.map_err(reqwest_error_to_io_error)?;
                let response: GetFileResponse = serde_json::from_reader(bytes.reader())?;
                Ok(response)
            }
            _ => Err(http_response_to_io_error(response).await),
        }
    }

    async fn patch_file(
        &mut self,
        access_token: &AccessToken,
        username: &str,
        filename: &str,
        request: &PatchFileRequest,
    ) -> io::Result<()> {
        let response = self
            .client
            .patch(&format!("{}/api/users/{}/files/{}", API_ADDRESS, username, filename))
            .headers(self.default_headers())
            .body(serde_json::to_vec(&request)?)
            .bearer_auth(access_token.as_str())
            .send()
            .await
            .map_err(reqwest_error_to_io_error)?;
        match response.status() {
            reqwest::StatusCode::OK | reqwest::StatusCode::CREATED => Ok(()),
            _ => Err(http_response_to_io_error(response).await),
        }
    }

    async fn delete_file(
        &mut self,
        access_token: &AccessToken,
        username: &str,
        filename: &str,
    ) -> io::Result<()> {
        let response = self
            .client
            .delete(&format!("{}/api/users/{}/files/{}", API_ADDRESS, username, filename))
            .headers(self.default_headers())
            .header("Content-Length", 0)
            .bearer_auth(access_token.as_str())
            .send()
            .await
            .map_err(reqwest_error_to_io_error)?;
        match response.status() {
            reqwest::StatusCode::OK => Ok(()),
            _ => Err(http_response_to_io_error(response).await),
        }
    }
}

#[cfg(test)]
mod testutils {
    use super::*;
    use std::env;

    /// Holds state for a test and allows for automatic cleanup of shared resources.
    #[derive(Default)]
    pub(crate) struct TestContext {
        service: CloudService,

        // State required to automatically clean up files on `drop`.
        access_token: Option<AccessToken>,
        username: Option<String>,
        files_to_delete: Vec<String>,
    }

    impl TestContext {
        /// Returns the service client in this context.
        pub(crate) fn service(&self) -> CloudService {
            self.service.clone()
        }

        /// Authenticates against the server using the username and password passed in via
        /// environment variables.  We need to support multiple test accounts at the same time, so
        /// this performs authentication for the test account `i`.
        pub(crate) async fn do_authenticate(&mut self, i: u8) -> AccessToken {
            let username = env::var(format!("TEST_ACCOUNT_{}_USERNAME", i))
                .expect("Expected env config not found");
            let password = env::var(format!("TEST_ACCOUNT_{}_PASSWORD", i))
                .expect("Expected env config not found");
            let access_token = self.service.authenticate(&username, &password).await.unwrap();
            self.access_token = Some(access_token.clone());
            access_token
        }

        /// Logs into the server and returns the username returned by it.
        pub(crate) async fn do_login(&mut self, access_token: &AccessToken) -> String {
            let request = LoginRequest { data: HashMap::default() };
            let response = self.service.login(access_token, &request).await.unwrap().unwrap();
            self.username = Some(response.username.clone());
            response.username
        }

        /// Generates a random filename and its content for testing, and makes sure the file gets
        /// deleted during cleanup in case the test didn't do it on its own.
        pub(crate) fn random_file(&mut self) -> (String, String) {
            let filename = format!("file-{}", rand::random::<u64>());
            let content = format!("Test content for {}", filename);
            self.files_to_delete.push(filename.clone());
            (filename, content)
        }
    }

    impl Drop for TestContext {
        fn drop(&mut self) {
            #[tokio::main]
            #[allow(clippy::single_match)]
            async fn cleanup(context: &mut TestContext) {
                match (context.access_token.as_ref(), context.username.as_ref()) {
                    (Some(access_token), Some(username)) => {
                        for filename in context.files_to_delete.iter() {
                            if let Err(e) =
                                context.service.delete_file(access_token, username, filename).await
                            {
                                eprintln!(
                                    "Failed to delete file {} during cleanup: {}",
                                    filename, e
                                );
                            }
                        }
                    }
                    _ => {
                        // Nothing to do: if we have a file in context.files_to_delete, it might be
                        // because we generated its name before authenticating or logging in, but
                        // in that case, we can't have created the file.
                    }
                }
            }
            cleanup(self);
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

    use super::testutils::*;
    use super::*;
    use std::env;

    #[tokio::test]
    #[ignore = "Requires environment configuration and is expensive"]
    async fn test_authenticate_bad_password() {
        let username = env::var("TEST_ACCOUNT_1_USERNAME").expect("Expected env config not found");
        let password = "this is an invalid password for the test account";

        let mut service = CloudService::default();
        let err = service.authenticate(&username, &password).await.unwrap_err();
        assert_eq!(io::ErrorKind::PermissionDenied, err.kind());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_login() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let access_token = context.do_authenticate(1).await;
            let mut service = context.service();

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
        run(&mut TestContext::default());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_get_files() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let access_token = context.do_authenticate(1).await;
            let username = context.do_login(&access_token).await;
            let mut service = context.service();

            let mut needed_bytes = 0;
            let mut needed_files = 0;
            let mut filenames_and_contents = vec![];
            for _ in 0..5 {
                let (filename, content) = context.random_file();

                needed_bytes += content.as_bytes().len() as u64;
                needed_files += 1;
                filenames_and_contents.push((filename, content));
            }

            let response = service.get_files(&access_token, &username).await.unwrap();
            for (filename, _content) in &filenames_and_contents {
                assert!(!response.files.iter().any(|x| &x.filename == filename));
            }
            let disk_quota = response.disk_quota.unwrap();
            let disk_free = response.disk_free.unwrap();
            assert!(disk_quota.bytes() > 0);
            assert!(disk_quota.files() > 0);
            assert!(disk_free.bytes() >= needed_bytes, "Not enough space for test run");
            assert!(disk_free.files() >= needed_files, "Not enough space for test run");

            for (filename, _content) in &filenames_and_contents {
                let request = GetFileRequest::default().with_get_content();
                let err = service
                    .get_file(&access_token, &username, filename, &request)
                    .await
                    .unwrap_err();
                assert_eq!(io::ErrorKind::NotFound, err.kind(), "{}", err);
            }

            for (filename, content) in &filenames_and_contents {
                let request = PatchFileRequest::default().with_content(content.as_bytes());
                service.patch_file(&access_token, &username, filename, &request).await.unwrap();
            }

            let response = service.get_files(&access_token, &username).await.unwrap();
            for (filename, _content) in &filenames_and_contents {
                assert!(response.files.iter().any(|x| &x.filename == filename));
            }
        }
        run(&mut TestContext::default());
    }

    async fn do_get_and_patch_file_test(context: &mut TestContext, filename: &str, content: &[u8]) {
        let access_token = context.do_authenticate(1).await;
        let username = context.do_login(&access_token).await;
        let mut service = context.service();

        let request = PatchFileRequest::default().with_content(content);
        service.patch_file(&access_token, &username, &filename, &request).await.unwrap();

        let request = GetFileRequest::default().with_get_content();
        let response =
            service.get_file(&access_token, &username, &filename, &request).await.unwrap();
        assert_eq!(content, response.decoded_content().unwrap().unwrap());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_get_and_patch_file_ok() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let (filename, content) = context.random_file();
            do_get_and_patch_file_test(context, &filename, content.as_bytes()).await;
        }
        run(&mut TestContext::default());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_get_and_patch_file_empty_ok() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let (filename, _content) = context.random_file();
            do_get_and_patch_file_test(context, &filename, &[]).await;
        }
        run(&mut TestContext::default());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_get_file_not_found() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let access_token = context.do_authenticate(1).await;
            let username = context.do_login(&access_token).await;
            let mut service = context.service();
            let (filename, _content) = context.random_file();

            let request = GetFileRequest::default().with_get_content();
            let err =
                service.get_file(&access_token, &username, &filename, &request).await.unwrap_err();
            assert_eq!(io::ErrorKind::NotFound, err.kind(), "{}", err);
        }
        run(&mut TestContext::default());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_acls() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let mut service = context.service();

            let access_token1 = context.do_authenticate(1).await;
            let username1 = context.do_login(&access_token1).await;
            let (filename, content) = context.random_file();

            let request = PatchFileRequest::default().with_content(content.clone());
            service.patch_file(&access_token1, &username1, &filename, &request).await.unwrap();

            let access_token2 = context.do_authenticate(2).await;
            let username2 = context.do_login(&access_token2).await;

            // Read username1's file as username2 before it is shared.
            let request = GetFileRequest::default().with_get_content();
            let err = service
                .get_file(&access_token2, &username1, &filename, &request)
                .await
                .unwrap_err();
            assert_eq!(io::ErrorKind::NotFound, err.kind(), "{}", err);

            // Share username1's file with username2.
            let request = PatchFileRequest::default().with_add_readers([username2]);
            service.patch_file(&access_token1, &username1, &filename, &request).await.unwrap();

            // Read username1's file as username2 again, now that it is shared.
            let request = GetFileRequest::default().with_get_content();
            let response =
                service.get_file(&access_token2, &username1, &filename, &request).await.unwrap();
            assert_eq!(content.as_bytes(), response.decoded_content().unwrap().unwrap());
        }
        run(&mut TestContext::default());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_delete_file_ok() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let access_token = context.do_authenticate(1).await;
            let username = context.do_login(&access_token).await;
            let mut service = context.service();
            let (filename, content) = context.random_file();

            let request = PatchFileRequest::default().with_content(content);
            service.patch_file(&access_token, &username, &filename, &request).await.unwrap();

            service.delete_file(&access_token, &username, &filename).await.unwrap();

            let request = GetFileRequest::default().with_get_content();
            let err =
                service.get_file(&access_token, &username, &filename, &request).await.unwrap_err();
            assert_eq!(io::ErrorKind::NotFound, err.kind(), "{}", err);
        }
        run(&mut TestContext::default());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_delete_file_not_found() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let access_token = context.do_authenticate(1).await;
            let username = context.do_login(&access_token).await;
            let mut service = context.service();
            let (filename, _content) = context.random_file();

            let err = service.delete_file(&access_token, &username, &filename).await.unwrap_err();
            assert_eq!(io::ErrorKind::NotFound, err.kind(), "{}", err);
        }
        run(&mut TestContext::default());
    }
}
