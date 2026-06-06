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

use crate::cmds::{LoginCommand, LogoutCommand, ShareCommand, SignupCommand};
use endbasic_client::testutils::*;
use endbasic_client::*;
use endbasic_std::storage::Storage;
use endbasic_std::testutils::*;
use std::cell::RefCell;
use std::rc::Rc;

/// Wrapper over the generic `Tester` to validate features related to the cloud service.
#[must_use]
pub(crate) struct ClientTester {
    tester: Tester,
    service: Rc<RefCell<MockService>>,
}

impl Default for ClientTester {
    fn default() -> Self {
        let tester = Tester::default();
        let console = tester.get_console();
        let storage = tester.get_storage();
        let service = Rc::from(RefCell::from(MockService::default()));
        storage
            .borrow_mut()
            .register_scheme("cloud", Box::from(crate::CloudDriveFactory::new(service.clone())));
        let tester = tester
            .add_callable(LoginCommand::new(service.clone(), console.clone(), storage.clone()))
            .add_callable(LogoutCommand::new(service.clone(), console.clone(), storage.clone()))
            .add_callable(ShareCommand::new(
                service.clone(),
                console.clone(),
                storage,
                "https://repl.example.com/",
            ))
            .add_callable(SignupCommand::new(service.clone(), console));
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
    pub(crate) fn run<S: Into<String>>(&mut self, script: S) -> ClientChecker<'_> {
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
