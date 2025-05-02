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

//! Test utilities for the cloud service.

use crate::{
    add_all, AccessToken, GetFilesResponse, LoginResponse, PatchFileRequest, Service, SignupRequest,
};
use async_trait::async_trait;
use endbasic_std::storage::{FileAcls, Storage};
use endbasic_std::testutils::*;
use std::cell::RefCell;
use std::collections::VecDeque;
use std::io;
use std::rc::Rc;

/// Service client implementation that allows specifying expectations on requests and yields the
/// responses previously recorded into it.
#[derive(Default)]
pub struct MockService {
    access_token: Option<AccessToken>,

    mock_signup: VecDeque<(SignupRequest, io::Result<()>)>,
    mock_login: VecDeque<((String, String), io::Result<LoginResponse>)>,
    mock_get_files: VecDeque<(String, io::Result<GetFilesResponse>)>,
    mock_get_file: VecDeque<((String, String), io::Result<Vec<u8>>)>,
    mock_get_file_acls: VecDeque<((String, String), io::Result<FileAcls>)>,
    mock_patch_file: VecDeque<((String, String, PatchFileRequest), io::Result<()>)>,
    mock_delete_file: VecDeque<((String, String), io::Result<()>)>,
}

impl MockService {
    /// Performs an explicit authentication for those tests that don't go through the `LOGIN`
    /// command logic.  The access token that's generated is different every time this is called
    /// within the same `MockService`.
    #[cfg(test)]
    pub(crate) async fn do_login(&mut self) {
        self.access_token = match &self.access_token {
            Some(previous) => Some(AccessToken::new(format!("{}$", previous.as_str()))),
            None => Some(AccessToken::new("$")),
        }
    }

    /// Records the behavior of an upcoming signup operation with `request` and that returns
    /// `result`.
    #[cfg(test)]
    pub(crate) fn add_mock_signup(&mut self, request: SignupRequest, result: io::Result<()>) {
        self.mock_signup.push_back((request, result));
    }

    /// Records the behavior of an upcoming login operation with `username` and `password`
    /// credentials and that returns `result`.
    #[cfg(test)]
    pub(crate) fn add_mock_login(
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
    #[cfg(test)]
    pub(crate) fn add_mock_get_files(
        &mut self,
        username: &str,
        result: io::Result<GetFilesResponse>,
    ) {
        let exp_request = username.to_owned();
        self.mock_get_files.push_back((exp_request, result));
    }

    /// Records the behavior of an upcoming "get file" operation for the `username`/`filename`
    /// pair that returns `result`.
    #[cfg(test)]
    pub(crate) fn add_mock_get_file<B: Into<Vec<u8>>>(
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
    #[cfg(test)]
    pub(crate) fn add_mock_get_file_acls(
        &mut self,
        username: &str,
        filename: &str,
        result: io::Result<FileAcls>,
    ) {
        let exp_request = (username.to_owned(), filename.to_owned());
        self.mock_get_file_acls.push_back((exp_request, result));
    }

    /// Records the behavior of an upcoming "patch file" operation for the `username`/`filename`
    /// pair with a request that looks like `exp_request` and that returns `result`.
    #[cfg(test)]
    pub(crate) fn add_mock_patch_file(
        &mut self,
        username: &str,
        filename: &str,
        exp_request: PatchFileRequest,
        result: io::Result<()>,
    ) {
        let exp_request = (username.to_owned(), filename.to_owned(), exp_request);
        self.mock_patch_file.push_back((exp_request, result));
    }

    /// Records the behavior of an upcoming "delete file" operation for the `username`/`filename`
    /// pair and that returns `result`.
    #[cfg(test)]
    pub(crate) fn add_mock_delete_file(
        &mut self,
        username: &str,
        filename: &str,
        result: io::Result<()>,
    ) {
        let exp_request = (username.to_owned(), filename.to_owned());
        self.mock_delete_file.push_back((exp_request, result));
    }

    /// Ensures that all requests and responses have been consumed.
    pub(crate) fn verify_all_used(&mut self) {
        assert!(self.mock_signup.is_empty(), "Mock requests not fully consumed");
        assert!(self.mock_login.is_empty(), "Mock requests not fully consumed");
        assert!(self.mock_get_files.is_empty(), "Mock requests not fully consumed");
        assert!(self.mock_get_file.is_empty(), "Mock requests not fully consumed");
        assert!(self.mock_patch_file.is_empty(), "Mock requests not fully consumed");
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
        assert_eq!(&mock.0 .0, username);
        assert_eq!(&mock.0 .1, password);

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
        match self.access_token {
            Some(_) => Some("logged-in-username".to_owned()),
            None => None,
        }
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
        assert_eq!(&mock.0 .0, username);
        assert_eq!(&mock.0 .1, filename);
        mock.1
    }

    async fn get_file_acls(&mut self, username: &str, filename: &str) -> io::Result<FileAcls> {
        self.access_token.as_ref().expect("login not called yet");

        let mock = self.mock_get_file_acls.pop_front().expect("No mock requests available");
        assert_eq!(&mock.0 .0, username);
        assert_eq!(&mock.0 .1, filename);
        mock.1
    }

    async fn patch_file(
        &mut self,
        username: &str,
        filename: &str,
        request: &PatchFileRequest,
    ) -> io::Result<()> {
        self.access_token.as_ref().expect("login not called yet");

        let mock = self.mock_patch_file.pop_front().expect("No mock requests available");
        assert_eq!(&mock.0 .0, username);
        assert_eq!(&mock.0 .1, filename);
        assert_eq!(&mock.0 .2, request);
        mock.1
    }

    async fn delete_file(&mut self, username: &str, filename: &str) -> io::Result<()> {
        self.access_token.as_ref().expect("login not called yet");

        let mock = self.mock_delete_file.pop_front().expect("No mock requests available");
        assert_eq!(&mock.0 .0, username);
        assert_eq!(&mock.0 .1, filename);
        mock.1
    }
}

/// Wrapper over the generic `Tester` to validate features related to the cloud service.
#[must_use]
pub(crate) struct ClientTester {
    tester: Tester,
    service: Rc<RefCell<MockService>>,
}

impl Default for ClientTester {
    fn default() -> Self {
        let mut tester = Tester::default();
        let console = tester.get_console();
        let storage = tester.get_storage();
        let service = Rc::from(RefCell::from(MockService::default()));
        add_all(
            tester.get_machine(),
            service.clone(),
            console,
            storage,
            "https://repl.example.com/",
        );
        ClientTester { tester, service }
    }
}

impl ClientTester {
    /// See the wrapped `Tester::add_input_chars` function for details.
    pub fn add_input_chars(self, golden_in: &str) -> Self {
        ClientTester { tester: self.tester.add_input_chars(golden_in), service: self.service }
    }

    /// See the wrapped `Tester::get_console` function for details.
    pub fn get_console(&self) -> Rc<RefCell<MockConsole>> {
        self.tester.get_console()
    }

    /// Gets the mock service client from the tester.
    ///
    /// This method should generally not be used.  Its primary utility is to hook
    /// externally-instantiated commands into the testing features.
    pub(crate) fn get_service(&self) -> Rc<RefCell<MockService>> {
        self.service.clone()
    }

    /// See the wrapped `Tester::get_storage` function for details.
    pub fn get_storage(&self) -> Rc<RefCell<Storage>> {
        self.tester.get_storage()
    }

    /// See the wrapped `Tester::run` function for details.
    pub(crate) fn run<S: Into<String>>(&mut self, script: S) -> ClientChecker {
        let checker = self.tester.run(script);
        ClientChecker { checker, service: self.service.clone(), exp_access_token: None }
    }
}

/// Wrapper over the generic `Checker` to validate features related to the cloud service.
#[must_use]
pub(crate) struct ClientChecker<'a> {
    checker: Checker<'a>,
    service: Rc<RefCell<MockService>>,
    exp_access_token: Option<AccessToken>,
}

impl<'a> ClientChecker<'a> {
    /// Expects the mock service to have logged in with the access `token`.
    pub(crate) fn expect_access_token<S: Into<String>>(self, token: S) -> Self {
        Self {
            checker: self.checker,
            service: self.service,
            exp_access_token: Some(AccessToken::new(token.into())),
        }
    }

    /// See the wrapped `Checker::expect_err` function for details.
    pub fn expect_compilation_err<S: Into<String>>(self, message: S) -> Self {
        Self {
            checker: self.checker.expect_compilation_err(message),
            service: self.service,
            exp_access_token: self.exp_access_token,
        }
    }

    /// See the wrapped `Checker::expect_err` function for details.
    pub fn expect_err<S: Into<String>>(self, message: S) -> Self {
        Self {
            checker: self.checker.expect_err(message),
            service: self.service,
            exp_access_token: self.exp_access_token,
        }
    }

    /// See the wrapped `Checker::expect_file` function for details.
    pub fn expect_file<N: Into<String>, C: Into<String>>(self, name: N, content: C) -> Self {
        Self {
            checker: self.checker.expect_file(name, content),
            service: self.service,
            exp_access_token: self.exp_access_token,
        }
    }

    /// See the wrapped `Checker::expect_output` function for details.
    pub fn expect_output<V: Into<Vec<CapturedOut>>>(self, out: V) -> Self {
        Self {
            checker: self.checker.expect_output(out),
            service: self.service,
            exp_access_token: self.exp_access_token,
        }
    }

    /// See the wrapped `Checker::expect_prints` function for details.
    pub fn expect_prints<S: Into<String>, V: Into<Vec<S>>>(self, out: V) -> Self {
        Self {
            checker: self.checker.expect_prints(out),
            service: self.service,
            exp_access_token: self.exp_access_token,
        }
    }

    /// See the wrapped `Checker::take_captured_out` function for details.
    #[must_use]
    pub fn take_captured_out(&mut self) -> Vec<CapturedOut> {
        self.checker.take_captured_out()
    }

    /// Validates all expectations.
    pub(crate) fn check(self) {
        self.checker.check();

        let mut service = self.service.borrow_mut();
        assert_eq!(self.exp_access_token, service.access_token);
        service.verify_all_used();
    }
}

/// See the wrapped `check_stmt_compilation_err` function for details.
pub fn client_check_stmt_compilation_err<S: Into<String>>(exp_error: S, stmt: &str) {
    ClientTester::default().run(stmt).expect_compilation_err(exp_error).check();
}

/// See the wrapped `check_stmt_err` function for details.
pub fn client_check_stmt_err<S: Into<String>>(exp_error: S, stmt: &str) {
    ClientTester::default().run(stmt).expect_err(exp_error).check();
}
