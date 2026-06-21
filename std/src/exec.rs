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

//! Commands that manipulate the machine's state or the program's execution.

use async_trait::async_trait;
use endbasic_core::{
    CallResult, Callable, CallableMetadata, CallableMetadataBuilder, ExprType, Scope,
};
use std::cell::RefCell;
use std::rc::Rc;

use crate::{MachineAction, MachineBuilder};

/// Category description for all symbols provided by this module.
pub(crate) const CATEGORY: &str = "Interpreter";

/// The `CLEAR` command.
pub struct ClearCommand {
    metadata: Rc<CallableMetadata>,
    actions: Rc<RefCell<Vec<MachineAction>>>,
}

impl ClearCommand {
    /// Creates a new `CLEAR` command that resets the state of the machine.
    pub fn new(actions: Rc<RefCell<Vec<MachineAction>>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("CLEAR")
                .with_async(true)
                .with_syntax(&[(&[], None)])
                .with_category(CATEGORY)
                .with_description(
                    "Restores initial machine state but keeps the stored program.
This command resets the machine to a semi-pristine state by clearing all user-defined variables \
and restoring the state of shared resources.  These resources include: the console, whose color \
and video syncing bit are reset; and the GPIO pins, which are set to their default state.
The stored program is kept in memory.  To clear that too, use NEW (but don't forget to first \
SAVE your program!).
This command is for interactive use only.",
                )
                .build(),
            actions,
        })
    }
}

#[async_trait(?Send)]
impl Callable for ClearCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn async_exec(&self, _scope: Scope<'_>) -> CallResult<()> {
        self.actions.borrow_mut().push(MachineAction::Clear);
        Ok(())
    }
}

/// The `ERRMSG` function.
pub struct ErrmsgFunction {
    metadata: Rc<CallableMetadata>,
}

impl ErrmsgFunction {
    /// Creates a new instance of the function.
    pub fn new() -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("ERRMSG")
                .with_return_type(ExprType::Text)
                .with_syntax(&[(&[], None)])
                .with_category(CATEGORY)
                .with_description(
                    "Returns the last captured error message.
When used in combination of ON ERROR to set an error handler, this function returns the string \
representation of the last captured error.  If this is called before any error is captured, \
returns the empty string.",
                )
                .build(),
        })
    }
}

#[async_trait(?Send)]
impl Callable for ErrmsgFunction {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(0, scope.nargs());

        let message = scope
            .last_error()
            .map(|(pos, message)| format!("{}: {}", pos, message))
            .unwrap_or_default();
        scope.return_string(message)
    }
}

/// Instantiates all REPL commands for the scripting machine and adds them to the `machine`.
pub fn add_scripting(machine: &mut MachineBuilder) {
    machine.add_callable(ErrmsgFunction::new());
}

/// Instantiates all REPL commands for the interactive machine and adds them to the `machine`.
pub fn add_interactive(machine: &mut MachineBuilder) {
    machine.add_callable(ClearCommand::new(machine.actions()));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutils::*;
    use crate::{Error, MachineBuilder, Signal, Yielder};
    use futures_lite::FutureExt;
    use futures_lite::future::{BoxedLocal, block_on};
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::time::Duration;

    #[test]
    fn test_clear_ok() {
        Tester::default().run("a = 1: CLEAR").expect_clear().check();
        Tester::default()
            .run_n(&["DIM a(2): CLEAR", "DIM a(5) AS STRING: CLEAR"])
            .expect_clear()
            .expect_clear()
            .check();
    }

    #[test]
    fn test_clear_inside_gosub_stops_execution() {
        // TODO(jmmv): CLEAR should not stop execution; these assertions only
        // document current behavior.
        Tester::default().run("GOSUB @sub: END\n@sub:\nCLEAR").expect_clear().check();
    }

    #[test]
    fn test_clear_inside_sub_stops_execution() {
        // TODO(jmmv): CLEAR should not stop execution; PRINT 5 and the second
        // foo call should also execute.  These assertions only document current
        // behavior where CLEAR terminates the program.
        Tester::default()
            .run("SUB foo: PRINT 3: CLEAR: PRINT 5: END SUB: foo: foo")
            .expect_prints([" 3"])
            .expect_clear()
            .check();
    }

    #[test]
    fn test_clear_errors() {
        check_stmt_compilation_err("1:1: CLEAR expected no arguments", "CLEAR 123");
    }

    #[test]
    fn test_errmsg_before_error() {
        check_expr_ok("", r#"ERRMSG"#);
    }

    #[test]
    fn test_errmsg_after_error() {
        Tester::default()
            .run("ON ERROR RESUME NEXT: COLOR -1: PRINT \"Captured: \"; ERRMSG")
            .expect_prints(["Captured: 1:29: Color out of range"])
            .check();
    }

    #[test]
    fn test_errmsg_errors() {
        check_expr_compilation_error("1:10: ERRMSG expected no arguments", r#"ERRMSG()"#);
        check_expr_compilation_error("1:10: ERRMSG expected no arguments", r#"ERRMSG(3)"#);
    }

    #[test]
    fn test_break_stops_after_upcall() {
        let (tx, rx) = async_channel::unbounded();
        let break_tx = tx.clone();
        let sleep_fake = move |_d: Duration| -> BoxedLocal<Result<(), String>> {
            let break_tx = break_tx.clone();
            async move {
                break_tx.send(Signal::Break).await.unwrap();
                Ok(())
            }
            .boxed_local()
        };

        let mut machine = MachineBuilder::default()
            .with_signals_chan((tx.clone(), rx))
            .with_sleep_fn(Box::from(sleep_fake))
            .build();
        machine.compile(&mut "DO: SLEEP 0: LOOP".as_bytes()).unwrap();

        match block_on(machine.exec()) {
            Err(Error::Break) => (),
            r => panic!("Expected Break but got {:?}", r),
        }
        assert_eq!(0, tx.len());
    }

    #[test]
    fn test_yielder_called_on_stop_reason_yield() {
        struct CountingYielder {
            count: Rc<RefCell<usize>>,
        }

        #[async_trait(?Send)]
        impl Yielder for CountingYielder {
            async fn yield_now(&mut self) {
                *self.count.borrow_mut() += 1;
            }
        }

        let (tx, rx) = async_channel::unbounded();
        let yield_count = Rc::from(RefCell::from(0));

        let mut machine = MachineBuilder::default()
            .with_signals_chan((tx.clone(), rx))
            .with_yielder(Rc::from(RefCell::from(CountingYielder { count: yield_count.clone() })))
            .build();

        block_on(tx.send(Signal::Break)).unwrap();
        machine.compile(&mut "@here: GOTO @here".as_bytes()).unwrap();
        match block_on(machine.exec()) {
            Err(Error::Break) => (),
            r => panic!("Expected Break but got {:?}", r),
        }

        assert_eq!(1, *yield_count.borrow());
    }

    #[test]
    fn test_drain_signals_ignores_pending_break() {
        let (tx, rx) = async_channel::unbounded();
        let mut machine = MachineBuilder::default().with_signals_chan((tx.clone(), rx)).build();

        block_on(tx.send(Signal::Break)).unwrap();
        machine.drain_signals();

        machine.compile(&mut "a = 1".as_bytes()).unwrap();
        match block_on(machine.exec()) {
            Ok(None) => (),
            r => panic!("Expected Ok(None) but got {:?}", r),
        }
        assert_eq!(0, tx.len());
    }

    fn do_no_check_stop_test(code: &str) {
        let (tx, rx) = async_channel::unbounded();
        let mut machine = MachineBuilder::default().with_signals_chan((tx.clone(), rx)).build();

        block_on(tx.send(Signal::Break)).unwrap();

        machine.compile(&mut code.as_bytes()).unwrap();
        match block_on(machine.exec()) {
            Ok(None) => (),
            r => panic!("Expected Ok(None) but got {:?}", r),
        }

        assert_eq!(1, tx.len());
    }

    fn do_check_stop_test(code: &str) {
        let (tx, rx) = async_channel::unbounded();
        let mut machine = MachineBuilder::default().with_signals_chan((tx.clone(), rx)).build();

        block_on(tx.send(Signal::Break)).unwrap();

        machine.compile(&mut code.as_bytes()).unwrap();
        match block_on(machine.exec()) {
            Err(Error::Break) => (),
            r => panic!("Expected Break but got {:?}", r),
        }

        assert_eq!(0, tx.len());
    }

    #[test]
    fn test_goto_forward_does_not_check_stop() {
        do_no_check_stop_test("GOTO @after: a = 1: @after");
    }

    #[test]
    fn test_if_taken_does_not_check_stop() {
        do_no_check_stop_test("a = 3: IF a = 3 THEN b = 0 ELSE b = 1: a = 7");
    }

    #[test]
    fn test_if_not_taken_does_not_check_stop() {
        do_no_check_stop_test("a = 3: IF a = 5 THEN b = 0 ELSE b = 1: a = 7");
    }

    #[test]
    fn test_goto_checks_stop() {
        do_check_stop_test("@here: GOTO @here");
        do_check_stop_test("@before: a = 1: GOTO @before");
    }

    #[test]
    fn test_gosub_checks_stop() {
        do_check_stop_test("GOTO @skip: @sub: a = 1: RETURN: @skip: GOSUB @sub: a = 1");
    }

    #[test]
    fn test_do_checks_stop() {
        do_check_stop_test("DO: LOOP");
        do_check_stop_test("DO: a = 1: LOOP");

        do_check_stop_test("DO UNTIL FALSE: LOOP");
        do_check_stop_test("DO UNTIL FALSE: a = 1: LOOP");

        do_check_stop_test("DO WHILE TRUE: LOOP");
        do_check_stop_test("DO WHILE TRUE: a = 1: LOOP");

        do_check_stop_test("DO: LOOP UNTIL FALSE");
        do_check_stop_test("DO: a = 1: LOOP UNTIL FALSE");

        do_check_stop_test("DO: LOOP WHILE TRUE");
        do_check_stop_test("DO: a = 1: LOOP WHILE TRUE");
    }

    #[test]
    fn test_for_checks_stop() {
        do_check_stop_test("FOR a = 1 TO 10: NEXT");
        do_check_stop_test("FOR a = 1 TO 10: b = 2: NEXT");
    }

    #[test]
    fn test_while_checks_stop() {
        do_check_stop_test("WHILE TRUE: WEND");
        do_check_stop_test("WHILE TRUE: a = 1: WEND");
    }
}
