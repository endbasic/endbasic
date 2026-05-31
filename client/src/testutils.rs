// EndBASIC
// Copyright 2021 Julio Merino
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

//! Test utilities for the cloud service.

use crate::{AccessToken, GetFilesResponse, LoginResponse, Service, SignupRequest};
use async_trait::async_trait;
use std::collections::VecDeque;
use std::io;

/// Service client implementation that allows specifying expectations on requests and yields the
/// responses previously recorded into it.
#[derive(Default)]
#[allow(clippy::type_complexity)]
pub struct MockService {
    /// Access token captured by the mock service during login.
    pub access_token: Option<AccessToken>,

    mock_signup: VecDeque<(SignupRequest, io::Result<()>)>,
    mock_login: VecDeque<((String, String), io::Result<LoginResponse>)>,
    mock_get_files: VecDeque<(String, io::Result<GetFilesResponse>)>,
    mock_get_file: VecDeque<((String, String), io::Result<Vec<u8>>)>,
    mock_get_file_acls: VecDeque<((String, String), io::Result<Vec<String>>)>,
    mock_patch_file_content: VecDeque<((String, String, Vec<u8>), io::Result<()>)>,
    mock_patch_file_acls: VecDeque<((String, String, Vec<String>, Vec<String>), io::Result<()>)>,
    mock_delete_file: VecDeque<((String, String), io::Result<()>)>,
}

impl MockService {
    /// Performs an explicit authentication for those tests that don't go through the `LOGIN`
    /// command logic.  The access token that's generated is different every time this is called
    /// within the same `MockService`.
    pub async fn do_login(&mut self) {
        self.access_token = match &self.access_token {
            Some(previous) => Some(AccessToken::new(format!("{}$", previous.as_str()))),
            None => Some(AccessToken::new("$")),
        }
    }

    /// Records the behavior of an upcoming signup operation with `request` and that returns
    /// `result`.
    pub fn add_mock_signup(&mut self, request: SignupRequest, result: io::Result<()>) {
        self.mock_signup.push_back((request, result));
    }

    /// Records the behavior of an upcoming login operation with `username` and `password`
    /// credentials and that returns `result`.
    pub fn add_mock_login(
        &mut self,
        username: &str,
        password: &str,
        result: io::Result<LoginResponse>,
    ) {
        let exp_request = (username.to_owned(), password.to_owned());
        self.mock_login.push_back((exp_request, result));
    }

    /// Records the behavior of an upcoming "get files" operation for `username` and that returns
    /// `result`.
    pub fn add_mock_get_files(&mut self, username: &str, result: io::Result<GetFilesResponse>) {
        let exp_request = username.to_owned();
        self.mock_get_files.push_back((exp_request, result));
    }

    /// Records the behavior of an upcoming "get file" operation for the `username`/`filename`
    /// pair that returns `result`.
    pub fn add_mock_get_file<B: Into<Vec<u8>>>(
        &mut self,
        username: &str,
        filename: &str,
        result: io::Result<B>,
    ) {
        let exp_request = (username.to_owned(), filename.to_owned());
        self.mock_get_file.push_back((exp_request, result.map(|b| b.into())));
    }

    /// Records the behavior of an upcoming "get file ACLs" operation for the `username`/`filename`
    /// pair that returns `result`.
    pub fn add_mock_get_file_acls(
        &mut self,
        username: &str,
        filename: &str,
        result: io::Result<Vec<String>>,
    ) {
        let exp_request = (username.to_owned(), filename.to_owned());
        self.mock_get_file_acls.push_back((exp_request, result));
    }

    /// Records the behavior of an upcoming "patch file content" operation for the
    /// `username`/`filename` pair with `exp_content` and that returns `result`.
    pub fn add_mock_patch_file_content<B: Into<Vec<u8>>>(
        &mut self,
        username: &str,
        filename: &str,
        exp_content: B,
        result: io::Result<()>,
    ) {
        let exp_request = (username.to_owned(), filename.to_owned(), exp_content.into());
        self.mock_patch_file_content.push_back((exp_request, result));
    }

    /// Records the behavior of an upcoming "patch file ACLS" operation for the
    /// `username`/`filename` pair with `exp_add` and `exp_remove` and that returns `result`.
    pub fn add_mock_patch_file_acls<S: Into<String>, V: Into<Vec<S>>>(
        &mut self,
        username: &str,
        filename: &str,
        exp_add_readers: V,
        exp_remove_readers: V,
        result: io::Result<()>,
    ) {
        let exp_add_readers =
            exp_add_readers.into().into_iter().map(|v| v.into()).collect::<Vec<String>>();
        let exp_remove_readers =
            exp_remove_readers.into().into_iter().map(|v| v.into()).collect::<Vec<String>>();
        let exp_request =
            (username.to_owned(), filename.to_owned(), exp_add_readers, exp_remove_readers);
        self.mock_patch_file_acls.push_back((exp_request, result));
    }

    /// Records the behavior of an upcoming "delete file" operation for the `username`/`filename`
    /// pair and that returns `result`.
    pub fn add_mock_delete_file(&mut self, username: &str, filename: &str, result: io::Result<()>) {
        let exp_request = (username.to_owned(), filename.to_owned());
        self.mock_delete_file.push_back((exp_request, result));
    }

    /// Ensures that all requests and responses have been consumed.
    pub fn verify_all_used(&mut self) {
        assert!(self.mock_signup.is_empty(), "Mock requests not fully consumed");
        assert!(self.mock_login.is_empty(), "Mock requests not fully consumed");
        assert!(self.mock_get_files.is_empty(), "Mock requests not fully consumed");
        assert!(self.mock_get_file.is_empty(), "Mock requests not fully consumed");
        assert!(self.mock_get_file_acls.is_empty(), "Mock requests not fully consumed");
        assert!(self.mock_patch_file_content.is_empty(), "Mock requests not fully consumed");
        assert!(self.mock_patch_file_acls.is_empty(), "Mock requests not fully consumed");
        assert!(self.mock_delete_file.is_empty(), "Mock requests not fully consumed");
    }
}

#[async_trait(?Send)]
impl Service for MockService {
    async fn signup(&mut self, request: &SignupRequest) -> io::Result<()> {
        let mock = self.mock_signup.pop_front().expect("No mock requests available");
        assert_eq!(&mock.0, request);
        mock.1
    }

    async fn login(&mut self, username: &str, password: &str) -> io::Result<LoginResponse> {
        let mock = self.mock_login.pop_front().expect("No mock requests available");
        assert_eq!(&mock.0.0, username);
        assert_eq!(&mock.0.1, password);

        if let Ok(response) = &mock.1 {
            self.access_token = Some(response.access_token.clone());
        }

        mock.1
    }

    async fn logout(&mut self) -> io::Result<()> {
        self.access_token.as_ref().expect("login not called yet");
        self.access_token = None;
        Ok(())
    }

    fn is_logged_in(&self) -> bool {
        self.access_token.is_some()
    }

    fn logged_in_username(&self) -> Option<String> {
        self.access_token.as_ref().map(|_| "logged-in-username".to_owned())
    }

    async fn list_users(&mut self) -> io::Result<Vec<String>> {
        unimplemented!("MockService does not implement list_users")
    }

    async fn get_files(&mut self, username: &str) -> io::Result<GetFilesResponse> {
        self.access_token.as_ref().expect("login not called yet");
        let mock = self.mock_get_files.pop_front().expect("No mock requests available");
        assert_eq!(&mock.0, username);
        mock.1
    }

    async fn get_file(&mut self, username: &str, filename: &str) -> io::Result<Vec<u8>> {
        self.access_token.as_ref().expect("login not called yet");

        let mock = self.mock_get_file.pop_front().expect("No mock requests available");
        assert_eq!(&mock.0.0, username);
        assert_eq!(&mock.0.1, filename);
        mock.1
    }

    async fn get_file_acls(&mut self, username: &str, filename: &str) -> io::Result<Vec<String>> {
        self.access_token.as_ref().expect("login not called yet");

        let mock = self.mock_get_file_acls.pop_front().expect("No mock requests available");
        assert_eq!(&mock.0.0, username);
        assert_eq!(&mock.0.1, filename);
        mock.1
    }

    async fn patch_file_content(
        &mut self,
        username: &str,
        filename: &str,
        content: Vec<u8>,
    ) -> io::Result<()> {
        self.access_token.as_ref().expect("login not called yet");

        let mock = self.mock_patch_file_content.pop_front().expect("No mock requests available");
        assert_eq!(&mock.0.0, username);
        assert_eq!(&mock.0.1, filename);
        assert_eq!(&mock.0.2, &content);
        mock.1
    }

    async fn patch_file_acls(
        &mut self,
        username: &str,
        filename: &str,
        add_readers: &Vec<String>,
        remove_readers: &Vec<String>,
    ) -> io::Result<()> {
        self.access_token.as_ref().expect("login not called yet");

        let mock = self.mock_patch_file_acls.pop_front().expect("No mock requests available");
        assert_eq!(&mock.0.0, username);
        assert_eq!(&mock.0.1, filename);
        assert_eq!(&mock.0.2, add_readers);
        assert_eq!(&mock.0.3, remove_readers);
        mock.1
    }

    async fn delete_file(&mut self, username: &str, filename: &str) -> io::Result<()> {
        self.access_token.as_ref().expect("login not called yet");

        let mock = self.mock_delete_file.pop_front().expect("No mock requests available");
        assert_eq!(&mock.0.0, username);
        assert_eq!(&mock.0.1, filename);
        mock.1
    }
}
