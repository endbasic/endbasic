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

use crate::*;
use async_trait::async_trait;
use base64::prelude::*;
use bytes::Buf;
use endbasic_std::console::remove_control_chars;
use endbasic_std::storage::FileAcls;
use reqwest::header::HeaderMap;
use reqwest::Response;
use reqwest::StatusCode;
use std::cell::RefCell;
use std::io;
use std::rc::Rc;
use std::str;
use url::Url;

/// Converts a `reqwest::Response` to an `io::Error`.  The response should have a non-OK status.
async fn http_response_to_io_error(response: Response) -> io::Error {
    let status = response.status();

    let kind = match status {
        StatusCode::OK => panic!("Should not have been called on a successful request"),

        // Match against the codes we know the server explicitly hands us.
        StatusCode::BAD_REQUEST => io::ErrorKind::InvalidInput,
        StatusCode::FORBIDDEN => io::ErrorKind::PermissionDenied,
        StatusCode::INSUFFICIENT_STORAGE => io::ErrorKind::Other,
        StatusCode::INTERNAL_SERVER_ERROR => io::ErrorKind::Other,
        StatusCode::NOT_FOUND => io::ErrorKind::NotFound,
        StatusCode::PAYLOAD_TOO_LARGE => io::ErrorKind::InvalidInput,
        StatusCode::SERVICE_UNAVAILABLE => io::ErrorKind::AddrNotAvailable,
        StatusCode::UNAUTHORIZED => io::ErrorKind::PermissionDenied,

        _ => io::ErrorKind::Other,
    };

    match response.text().await {
        Ok(text) => match serde_json::from_str::<ErrorResponse>(&text) {
            Ok(response) => io::Error::new(
                kind,
                format!("{} (server code: {})", remove_control_chars(response.message), status),
            ),
            _ => io::Error::new(
                kind,
                format!(
                    "HTTP request returned status {} with text '{}'",
                    status,
                    remove_control_chars(text)
                ),
            ),
        },
        Err(e) => io::Error::new(
            kind,
            format!(
                "HTTP request returned status {} and failed to get text due to {}",
                status,
                remove_control_chars(e.to_string())
            ),
        ),
    }
}

/// Converts a `reqwest::Error` to an `io::Error`.
fn reqwest_error_to_io_error(e: reqwest::Error) -> io::Error {
    io::Error::other(format!("{}", e))
}

/// Container for authentication data to track after login.
struct AuthData {
    username: String,
    access_token: AccessToken,
}

/// An implementation of the EndBASIC service client that talks to a remote server.
pub struct CloudService {
    api_address: Url,
    client: reqwest::Client,
    auth_data: Rc<RefCell<Option<AuthData>>>,
}

impl CloudService {
    /// Creates a new client for the cloud service that talks to `api_address`.
    pub fn new(api_address: &str) -> io::Result<Self> {
        let url = match Url::parse(api_address) {
            Ok(url) => url,
            Err(e) => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("Invalid base API address: {}", e),
                ))
            }
        };

        if !(url.path().is_empty() || url.path() == "/") {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "Invalid base API address: cannot contain a path".to_owned(),
            ));
        }

        let auth_data = Rc::from(RefCell::from(None));

        Ok(Self { api_address: url, client: reqwest::Client::default(), auth_data })
    }

    /// Generates a service URL with the given `path`.
    fn make_url(&self, path: &str) -> Url {
        assert!(path.starts_with("api/"));
        let mut url = self.api_address.clone();
        assert!(url.path().is_empty() || url.path() == "/");
        url.set_path(path);
        url
    }

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

    /// Checks if the given auth data object is present and returns it, or else returns a permission
    /// denied error.
    fn require_auth_data(data: Option<&AuthData>) -> io::Result<&AuthData> {
        match data.as_ref() {
            Some(data) => Ok(data),
            None => {
                Err(io::Error::new(io::ErrorKind::PermissionDenied, "Not logged in yet".to_owned()))
            }
        }
    }
}

#[async_trait(?Send)]
impl Service for CloudService {
    async fn signup(&mut self, request: &SignupRequest) -> io::Result<()> {
        let response = self
            .client
            .post(self.make_url("api/signup"))
            .headers(self.default_headers())
            .header("Content-Type", "application/json")
            .body(serde_json::to_vec(&request)?)
            .send()
            .await
            .map_err(reqwest_error_to_io_error)?;
        match response.status() {
            StatusCode::OK => Ok(()),
            _ => Err(http_response_to_io_error(response).await),
        }
    }

    async fn login(&mut self, username: &str, password: &str) -> io::Result<LoginResponse> {
        // TODO(https://github.com/seanmonstar/reqwest/pull/1096): Replace with a basic_auth()
        // call on the RequestBuilder once it is supported in WASM.
        let basic_auth =
            format!("Basic {}", BASE64_STANDARD.encode(format!("{}:{}", username, password)));

        let response = self
            .client
            .post(self.make_url("api/login"))
            .headers(self.default_headers())
            .header("Authorization", basic_auth)
            .header("Content-Length", 0)
            .send()
            .await
            .map_err(reqwest_error_to_io_error)?;
        match response.status() {
            StatusCode::OK => {
                let bytes = response.bytes().await.map_err(reqwest_error_to_io_error)?;
                let response: LoginResponse = serde_json::from_reader(bytes.reader())?;
                let auth_data = AuthData {
                    username: username.to_owned(),
                    access_token: response.access_token.clone(),
                };
                *(self.auth_data.borrow_mut()) = Some(auth_data);
                Ok(response)
            }
            _ => Err(http_response_to_io_error(response).await),
        }
    }

    async fn logout(&mut self) -> io::Result<()> {
        let mut auth_data = self.auth_data.borrow_mut();
        let response = {
            let auth_data = Self::require_auth_data(auth_data.as_ref())?;
            self.client
                .post(self.make_url(&format!("api/users/{}/logout", auth_data.username)))
                .headers(self.default_headers())
                .header("Content-Length", 0)
                .bearer_auth(auth_data.access_token.as_str())
                .send()
                .await
                .map_err(reqwest_error_to_io_error)?
        };
        match response.status() {
            StatusCode::OK => {
                *auth_data = None;
                Ok(())
            }
            _ => Err(http_response_to_io_error(response).await),
        }
    }

    fn is_logged_in(&self) -> bool {
        self.auth_data.borrow().is_some()
    }

    fn logged_in_username(&self) -> Option<String> {
        self.auth_data.borrow().as_ref().map(|x| x.username.to_owned())
    }

    async fn get_files(&mut self, username: &str) -> io::Result<GetFilesResponse> {
        let mut builder = self
            .client
            .get(self.make_url(&format!("api/users/{}/files", username)))
            .headers(self.default_headers());
        if let Some(auth_data) = self.auth_data.borrow().as_ref() {
            builder = builder.bearer_auth(auth_data.access_token.as_str());
        }
        let response = builder.send().await.map_err(reqwest_error_to_io_error)?;
        match response.status() {
            StatusCode::OK => {
                let bytes = response.bytes().await.map_err(reqwest_error_to_io_error)?;
                let response: GetFilesResponse = serde_json::from_reader(bytes.reader())?;
                Ok(response)
            }
            _ => Err(http_response_to_io_error(response).await),
        }
    }

    async fn get_file(&mut self, username: &str, filename: &str) -> io::Result<Vec<u8>> {
        let mut builder = self
            .client
            .get(self.make_url(&format!("api/users/{}/files/{}", username, filename)))
            .headers(self.default_headers());
        if let Some(auth_data) = self.auth_data.borrow().as_ref() {
            builder = builder.bearer_auth(auth_data.access_token.as_str());
        }
        let response = builder.send().await.map_err(reqwest_error_to_io_error)?;
        match response.status() {
            StatusCode::OK => {
                Ok(response.bytes().await.map_err(reqwest_error_to_io_error)?.to_vec())
            }
            _ => Err(http_response_to_io_error(response).await),
        }
    }

    async fn get_file_acls(&mut self, username: &str, filename: &str) -> io::Result<FileAcls> {
        let mut headers = self.default_headers();
        headers.insert("X-EndBASIC-GetContent", "false".parse().unwrap());
        headers.insert("X-EndBASIC-GetReaders", "true".parse().unwrap());
        let mut builder = self
            .client
            .get(self.make_url(&format!("api/users/{}/files/{}", username, filename)))
            .headers(headers);
        if let Some(auth_data) = self.auth_data.borrow().as_ref() {
            builder = builder.bearer_auth(auth_data.access_token.as_str());
        }
        let response = builder.send().await.map_err(reqwest_error_to_io_error)?;
        match response.status() {
            StatusCode::OK => {
                let mut readers = vec![];
                for h in response.headers().get_all("X-EndBASIC-Reader") {
                    match h.to_str() {
                        Ok(value) => readers.push(value.to_owned()),
                        Err(e) => {
                            return Err(io::Error::new(
                                io::ErrorKind::InvalidData,
                                format!("Server returned invalid reader ACL: {}", e),
                            ))
                        }
                    }
                }

                let bytes = response.bytes().await.map_err(reqwest_error_to_io_error)?;
                debug_assert!(bytes.is_empty(), "Did not expect server to return content");

                Ok(FileAcls::default().with_readers(readers))
            }
            _ => Err(http_response_to_io_error(response).await),
        }
    }

    async fn patch_file_content(
        &mut self,
        username: &str,
        filename: &str,
        content: Vec<u8>,
    ) -> io::Result<()> {
        let auth_data = self.auth_data.borrow();

        let response = self
            .client
            .patch(self.make_url(&format!("api/users/{}/files/{}", username, filename)))
            .headers(self.default_headers())
            .header("Content-Type", "application/octet-stream")
            .header("X-EndBASIC-PatchContent", "true")
            .body(content)
            .bearer_auth(Self::require_auth_data(auth_data.as_ref())?.access_token.as_str())
            .send()
            .await
            .map_err(reqwest_error_to_io_error)?;
        match response.status() {
            StatusCode::OK | StatusCode::CREATED => Ok(()),
            _ => Err(http_response_to_io_error(response).await),
        }
    }

    async fn patch_file_acls(
        &mut self,
        username: &str,
        filename: &str,
        add: &FileAcls,
        remove: &FileAcls,
    ) -> io::Result<()> {
        let auth_data = self.auth_data.borrow();

        let mut builder = self
            .client
            .patch(self.make_url(&format!("api/users/{}/files/{}", username, filename)))
            .headers(self.default_headers())
            .header("Content-Type", "application/octet-stream")
            // Ensure we have at least one header to go through the header-based request handler.
            .header("X-EndBASIC-PatchContent", "false");

        for reader in add.readers() {
            builder = builder.header("X-EndBASIC-AddReader", reader);
        }
        for reader in remove.readers() {
            builder = builder.header("X-EndBASIC-RemoveReader", reader);
        }

        let response = builder
            .bearer_auth(Self::require_auth_data(auth_data.as_ref())?.access_token.as_str())
            .send()
            .await
            .map_err(reqwest_error_to_io_error)?;
        match response.status() {
            StatusCode::OK | StatusCode::CREATED => Ok(()),
            _ => Err(http_response_to_io_error(response).await),
        }
    }

    async fn delete_file(&mut self, username: &str, filename: &str) -> io::Result<()> {
        let auth_data = self.auth_data.borrow();

        let response = self
            .client
            .delete(self.make_url(&format!("api/users/{}/files/{}", username, filename)))
            .headers(self.default_headers())
            .header("Content-Length", 0)
            .bearer_auth(Self::require_auth_data(auth_data.as_ref())?.access_token.as_str())
            .send()
            .await
            .map_err(reqwest_error_to_io_error)?;
        match response.status() {
            StatusCode::OK => Ok(()),
            _ => Err(http_response_to_io_error(response).await),
        }
    }
}

#[cfg(test)]
mod testutils {
    use super::*;
    use std::env;

    /// Creates a new service that talks to the configured API service for testing.
    pub(crate) fn new_service_from_env() -> CloudService {
        let service_api = env::var("SERVICE_URL").expect("Expected env config not found");
        CloudService::new(&service_api).unwrap()
    }

    /// Holds state for a test and allows for automatic cleanup of shared resources.
    pub(crate) struct TestContext {
        pub(super) service: CloudService,

        // State required to automatically clean up files on `drop`.
        username: Option<String>,
        files_to_delete: Vec<String>,
    }

    impl TestContext {
        /// Creates a new test context that talks to the configured API service.
        pub(crate) fn new_from_env() -> Self {
            TestContext { service: new_service_from_env(), username: None, files_to_delete: vec![] }
        }

        /// Returns the username of the selected test account.
        pub(crate) fn get_username(&self, i: u8) -> String {
            env::var(format!("TEST_ACCOUNT_{}_USERNAME", i)).expect("Expected env config not found")
        }

        /// Authenticates against the server using the username and password passed in via
        /// environment variables.  We need to support multiple test accounts at the same time, so
        /// this performs authentication for the test account `i`.
        ///
        /// Returns the username of the selected test account for convenience.
        pub(crate) async fn do_login(&mut self, i: u8) -> String {
            let username = self.get_username(i);
            let password = env::var(format!("TEST_ACCOUNT_{}_PASSWORD", i))
                .expect("Expected env config not found");
            let _response = self.service.login(&username, &password).await.unwrap();
            self.username = Some(username.clone());
            username
        }

        /// Clears the authentication token to represent a log out.
        pub(crate) async fn do_logout(&mut self) {
            self.service.logout().await.unwrap();
            self.username = None;
        }

        /// Generates a random filename and its content for testing, and makes sure the file gets
        /// deleted during cleanup in case the test didn't do it on its own.
        pub(crate) fn random_file(&mut self) -> (String, Vec<u8>) {
            let filename = format!("file-{}", rand::random::<u64>());
            let content = format!("Test content for {}", filename);
            self.files_to_delete.push(filename.clone());
            (filename, content.into_bytes())
        }
    }

    impl Drop for TestContext {
        fn drop(&mut self) {
            #[tokio::main]
            #[allow(clippy::single_match)]
            async fn cleanup(context: &mut TestContext) {
                match context.username.as_ref() {
                    Some(username) => {
                        for filename in context.files_to_delete.iter() {
                            if let Err(e) = context.service.delete_file(username, filename).await {
                                eprintln!(
                                    "Failed to delete file {} during cleanup: {}",
                                    filename, e
                                );
                            }
                        }

                        if let Err(e) = context.service.logout().await {
                            eprintln!("Failed to log out for {} during cleanup: {}", username, e);
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

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_login_ok() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let _username = context.do_login(1).await;
        }
        run(&mut TestContext::new_from_env());
    }

    #[tokio::test]
    #[ignore = "Requires environment configuration and is expensive"]
    async fn test_login_bad_password() {
        let username = env::var("TEST_ACCOUNT_1_USERNAME").expect("Expected env config not found");
        let password = "this is an invalid password for the test account";

        let mut service = new_service_from_env();
        let err = service.login(&username, &password).await.unwrap_err();
        assert_eq!(io::ErrorKind::PermissionDenied, err.kind());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_get_files() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let username = context.do_login(1).await;

            let mut needed_bytes = 0;
            let mut needed_files = 0;
            let mut filenames_and_contents = vec![];
            for _ in 0..5 {
                let (filename, content) = context.random_file();

                needed_bytes += content.len() as u64;
                needed_files += 1;
                filenames_and_contents.push((filename, content));
            }

            let response = context.service.get_files(&username).await.unwrap();
            for (filename, _content) in &filenames_and_contents {
                assert!(!response.files.iter().any(|x| &x.filename == filename));
            }
            let disk_quota: DiskSpace = response.disk_quota.unwrap().into();
            let disk_free: DiskSpace = response.disk_free.unwrap().into();
            assert!(disk_quota.bytes() > 0);
            assert!(disk_quota.files() > 0);
            assert!(disk_free.bytes() >= needed_bytes, "Not enough space for test run");
            assert!(disk_free.files() >= needed_files, "Not enough space for test run");

            for (filename, _content) in &filenames_and_contents {
                let err = context.service.get_file(&username, filename).await.unwrap_err();
                assert_eq!(io::ErrorKind::NotFound, err.kind(), "{}", err);
            }

            for (filename, content) in &filenames_and_contents {
                context
                    .service
                    .patch_file_content(&username, filename, content.clone())
                    .await
                    .unwrap();
            }

            let response = context.service.get_files(&username).await.unwrap();
            for (filename, _content) in &filenames_and_contents {
                assert!(response.files.iter().any(|x| &x.filename == filename));
            }
        }
        run(&mut TestContext::new_from_env());
    }

    async fn do_get_and_patch_file_test<B: Into<Vec<u8>>>(
        context: &mut TestContext,
        filename: &str,
        content: B,
    ) {
        let username = context.do_login(1).await;

        let content = content.into();
        context.service.patch_file_content(&username, filename, content.clone()).await.unwrap();
        assert_eq!(content, context.service.get_file(&username, filename).await.unwrap());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_get_and_patch_file_ok() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let (filename, content) = context.random_file();
            do_get_and_patch_file_test(context, &filename, content).await;
        }
        run(&mut TestContext::new_from_env());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_get_and_patch_file_empty_ok() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let (filename, _content) = context.random_file();
            do_get_and_patch_file_test(context, &filename, &[]).await;
        }
        run(&mut TestContext::new_from_env());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_get_and_patch_file_utf8() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let (filename, _content) = context.random_file();
            let content = "안녕하세요";
            do_get_and_patch_file_test(context, &filename, content).await;
        }
        run(&mut TestContext::new_from_env());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_get_file_not_found() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let username = context.do_login(1).await;
            let (filename, _content) = context.random_file();

            let err = context.service.get_file(&username, &filename).await.unwrap_err();
            assert_eq!(io::ErrorKind::NotFound, err.kind(), "{}", err);
        }
        run(&mut TestContext::new_from_env());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_patch_file_without_login() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let username = context.get_username(1);

            context.do_login(1).await;
            let (filename, _content) = context.random_file();

            context.do_logout().await;
            let err = context
                .service
                .patch_file_content(&username, &filename, b"foo".to_vec())
                .await
                .unwrap_err();
            assert_eq!(io::ErrorKind::PermissionDenied, err.kind(), "{}", err);
            assert!(format!("{}", err).contains("Not logged in"));
        }
        run(&mut TestContext::new_from_env());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_acls_private() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let (filename, content) = context.random_file();

            let username1 = context.get_username(1);
            let username2 = context.get_username(2);

            // Share username1's file with username2.
            context.do_login(1).await;
            context
                .service
                .patch_file_content(&username1, &filename, content.clone())
                .await
                .unwrap();

            // Read username1's file as username2 before it is shared.
            context.do_login(2).await;
            let err = context.service.get_file(&username1, &filename).await.unwrap_err();
            assert_eq!(io::ErrorKind::NotFound, err.kind(), "{}", err);

            // Share username1's file with username2.
            context.do_login(1).await;
            context
                .service
                .patch_file_acls(
                    &username1,
                    &filename,
                    &FileAcls::default().with_readers([username2]),
                    &FileAcls::default(),
                )
                .await
                .unwrap();

            // Read username1's file as username2 again, now that it is shared.
            context.do_login(2).await;
            let response = context.service.get_file(&username1, &filename).await.unwrap();
            assert_eq!(content, response);
        }
        run(&mut TestContext::new_from_env());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_acls_public() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let (filename, content) = context.random_file();

            let username1 = context.get_username(1);

            // Share username1's file with the public.
            context.do_login(1).await;
            context
                .service
                .patch_file_content(&username1, &filename, content.clone())
                .await
                .unwrap();

            // Read username1's file as a guest before it is shared.
            context.do_logout().await;
            let err = context.service.get_file(&username1, &filename).await.unwrap_err();
            assert_eq!(io::ErrorKind::NotFound, err.kind(), "{}", err);

            // Share username1's file with the public.
            context.do_login(1).await;
            context
                .service
                .patch_file_acls(
                    &username1,
                    &filename,
                    &FileAcls::default().with_readers(["public".to_owned()]),
                    &FileAcls::default(),
                )
                .await
                .unwrap();

            // Read username1's file as a guest again, now that it is shared.
            context.do_logout().await;
            let response = context.service.get_file(&username1, &filename).await.unwrap();
            assert_eq!(content, response);
        }
        run(&mut TestContext::new_from_env());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_delete_file_ok() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let username = context.do_login(1).await;
            let (filename, content) = context.random_file();

            context.service.patch_file_content(&username, &filename, content).await.unwrap();

            context.service.delete_file(&username, &filename).await.unwrap();

            let err = context.service.get_file(&username, &filename).await.unwrap_err();
            assert_eq!(io::ErrorKind::NotFound, err.kind(), "{}", err);
            assert!(format!("{}", err).contains("(server code: 404"));
        }
        run(&mut TestContext::new_from_env());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_delete_file_not_found() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let username = context.do_login(1).await;
            let (filename, _content) = context.random_file();

            let err = context.service.delete_file(&username, &filename).await.unwrap_err();
            assert_eq!(io::ErrorKind::NotFound, err.kind(), "{}", err);
            assert!(format!("{}", err).contains("(server code: 404"));
        }
        run(&mut TestContext::new_from_env());
    }

    #[test]
    #[ignore = "Requires environment configuration and is expensive"]
    fn test_delete_file_without_login() {
        #[tokio::main]
        async fn run(context: &mut TestContext) {
            let username = context.get_username(1);

            context.do_login(1).await;
            let (filename, _content) = context.random_file();

            context.do_logout().await;
            let err = context.service.delete_file(&username, &filename).await.unwrap_err();
            assert_eq!(io::ErrorKind::PermissionDenied, err.kind(), "{}", err);
            assert!(format!("{}", err).contains("Not logged in"));
        }
        run(&mut TestContext::new_from_env());
    }
}
