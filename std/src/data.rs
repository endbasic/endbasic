// EndBASIC
// Copyright 2022 Julio Merino
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

//! Commands to interact with the data provided by `DATA` statements.

use crate::numerics::double_to_integer;
use crate::{Clearable, MachineBuilder};
use async_trait::async_trait;
use endbasic_core2::{
    ArgSep, ArgSepSyntax, CallError, CallResult, Callable, CallableMetadata,
    CallableMetadataBuilder, ConstantDatum, ExprType, RepeatedSyntax, RepeatedTypeSyntax, Scope,
    VarArgTag,
};
use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;

/// Category description for all symbols provided by this module.
pub(crate) const CATEGORY: &str = "Data management";

struct ClearableIndex(Rc<RefCell<usize>>);

impl Clearable for ClearableIndex {
    fn reset_state(&self) {
        *self.0.borrow_mut() = 0;
    }
}

fn expr_type_name(vtype: ExprType) -> &'static str {
    match vtype {
        ExprType::Boolean => "BOOLEAN",
        ExprType::Double => "DOUBLE",
        ExprType::Integer => "INTEGER",
        ExprType::Text => "STRING",
    }
}

fn value_type_name(value: &ConstantDatum) -> &'static str {
    match value {
        ConstantDatum::Boolean(..) => "BOOLEAN",
        ConstantDatum::Double(..) => "DOUBLE",
        ConstantDatum::Integer(..) => "INTEGER",
        ConstantDatum::Text(..) => "STRING",
    }
}

/// The `READ` command.
pub struct ReadCommand {
    metadata: Rc<CallableMetadata>,
    index: Rc<RefCell<usize>>,
}

impl ReadCommand {
    /// Creates a new `READ` command.
    pub fn new(index: Rc<RefCell<usize>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("READ")
                .with_syntax(&[(
                    &[],
                    Some(&RepeatedSyntax {
                        name: Cow::Borrowed("vref"),
                        type_syn: RepeatedTypeSyntax::VariableRef,
                        sep: ArgSepSyntax::Exactly(ArgSep::Long),
                        require_one: true,
                        allow_missing: false,
                    }),
                )])
                .with_category(CATEGORY)
                .with_description(
                    "Extracts data values from DATA statements.
DATA statements can appear anywhere in the program and they register data values into an array of \
values.  READ is then used to extract values from this array into the provided variables in the \
order in which they were defined.  In other words: READ maintains an internal index into the data \
array that gets incremented by the number of provided variables every time it is executed.
The variable references in the vref1..vrefN list must match the types or be compatible with the \
values in the corresponding position of the data array.  Empty values in the data array can be \
specified by DATA, and those are converted into the default values for the relevant types: \
booleans are false, numbers are 0, and strings are empty.
Attempting to extract more values than are defined by DATA results in an \"out of data\" error.
The index that READ uses to extract DATA values can be reset by RESTORE and, more generally, by \
CLEAR.",
                )
                .build(),
            index,
        })
    }
}

#[async_trait(?Send)]
impl Callable for ReadCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn exec(&self, mut scope: Scope<'_>) -> CallResult<()> {
        debug_assert_ne!(0, scope.nargs());

        fn assign_datum(scope: &mut Scope<'_>, reg: u8, datum: ConstantDatum) -> CallResult<()> {
            let target_type = scope.get_ref(reg).vtype;
            match (target_type, datum) {
                (ExprType::Boolean, ConstantDatum::Boolean(b)) => {
                    scope.get_mut_ref(reg).set_boolean(b);
                    Ok(())
                }
                (ExprType::Double, ConstantDatum::Double(d)) => {
                    scope.get_mut_ref(reg).set_double(d);
                    Ok(())
                }
                (ExprType::Double, ConstantDatum::Integer(i)) => {
                    scope.get_mut_ref(reg).set_double(i as f64);
                    Ok(())
                }
                (ExprType::Integer, ConstantDatum::Double(d)) => {
                    let i = double_to_integer(d)
                        .map_err(|e| CallError::Syntax(scope.get_pos(reg), e.to_string()))?;
                    scope.get_mut_ref(reg).set_integer(i);
                    Ok(())
                }
                (ExprType::Integer, ConstantDatum::Integer(i)) => {
                    scope.get_mut_ref(reg).set_integer(i);
                    Ok(())
                }
                (ExprType::Text, ConstantDatum::Text(s)) => {
                    scope.get_mut_ref(reg).set_string(s);
                    Ok(())
                }
                (target_type, source_value) => Err(CallError::Syntax(
                    scope.get_pos(reg),
                    format!(
                        "Cannot assign value of type {} to variable of type {}",
                        value_type_name(&source_value),
                        expr_type_name(target_type),
                    ),
                )),
            }
        }

        let mut index = self.index.borrow_mut();
        let mut reg = 0;
        loop {
            let sep = if let VarArgTag::Pointer(sep) = scope.get_type(reg) {
                sep
            } else {
                unreachable!();
            };
            reg += 1;

            let vtype = scope.get_ref(reg).vtype;
            let datum = match scope.data().get(*index) {
                None => {
                    return Err(CallError::Syntax(scope.get_pos(reg), "Out of data".to_owned()));
                }
                Some(Some(datum)) => datum.clone(),
                Some(None) => match vtype {
                    ExprType::Boolean => ConstantDatum::Boolean(false),
                    ExprType::Double => ConstantDatum::Double(0.0),
                    ExprType::Integer => ConstantDatum::Integer(0),
                    ExprType::Text => ConstantDatum::Text(String::new()),
                },
            };
            *index += 1;
            assign_datum(&mut scope, reg, datum)?;
            reg += 1;

            if sep == ArgSep::End {
                break;
            }
        }

        Ok(())
    }
}

/// The `RESTORE` command.
pub struct RestoreCommand {
    metadata: Rc<CallableMetadata>,
    index: Rc<RefCell<usize>>,
}

impl RestoreCommand {
    /// Creates a new `RESTORE` command.
    pub fn new(index: Rc<RefCell<usize>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("RESTORE")
                .with_syntax(&[(&[], None)])
                .with_category(CATEGORY)
                .with_description(
                    "Resets the index of the data element to be returned.
This allows READ to re-return the same elements that were previously extracted from the array of \
values defined by DATA.",
                )
                .build(),
            index,
        })
    }
}

#[async_trait(?Send)]
impl Callable for RestoreCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(0, scope.nargs());
        *self.index.borrow_mut() = 0;
        Ok(())
    }
}

/// Instantiates all symbols in this module and adds them to the `machine`.
pub fn add_all(machine: &mut MachineBuilder) {
    let index = Rc::from(RefCell::from(0));
    machine.add_clearable(Box::from(ClearableIndex(index.clone())));
    machine.add_callable(ReadCommand::new(index.clone()));
    machine.add_callable(RestoreCommand::new(index));
}

#[cfg(test)]
mod tests {
    use crate::testutils::*;

    #[test]
    fn test_read_simple() {
        Tester::default()
            .run(
                r#"
            READ i: PRINT i
            READ i: PRINT i
            DATA 3, 5, -7
            READ i: PRINT i
            "#,
            )
            .expect_prints([" 3", " 5", "-7"])
            .expect_var("I", -7)
            .check();
    }

    #[test]
    fn test_read_multiple() {
        Tester::default()
            .run(
                r#"
            READ i, j, k, i
            DATA 3, 5, 7, 6
            "#,
            )
            .expect_var("I", 6)
            .expect_var("J", 5)
            .expect_var("K", 7)
            .check();
    }

    #[test]
    fn test_read_defaults_with_annotations() {
        Tester::default()
            .run(r#"DATA , , , ,: READ a, b?, d#, i%, s$"#)
            .expect_var("a", 0)
            .expect_var("b", false)
            .expect_var("d", 0.0)
            .expect_var("i", 0)
            .expect_var("s", "")
            .check();
    }

    #[test]
    fn test_read_defaults_without_annotations() {
        Tester::default()
            .run(
                r#"
            DIM SHARED b AS BOOLEAN
            DIM SHARED d AS DOUBLE
            DIM SHARED i AS INTEGER
            DIM SHARED s AS STRING
            DATA , , , ,
            READ a, b, d, i, s
            "#,
            )
            .expect_var("a", 0)
            .expect_var("b", false)
            .expect_var("d", 0.0)
            .expect_var("i", 0)
            .expect_var("s", "")
            .check();
    }

    #[test]
    fn test_read_double_to_integer() {
        Tester::default().run(r#"DATA 5.6: READ i%"#).expect_var("i", 6).check();
    }

    #[test]
    fn test_read_integer_to_double() {
        Tester::default().run(r#"DATA 5: READ d#"#).expect_var("d", 5.0).check();
    }

    #[test]
    fn test_read_out_of_data() {
        Tester::default()
            .run(r#"DATA 5: READ i: READ j"#)
            .expect_err("1:22: Out of data")
            .expect_var("I", 5)
            .check();
    }

    #[test]
    fn test_read_clear_on_run() {
        Tester::default()
            .set_program(None, "DATA 1: READ i: PRINT i")
            .run(r#"RUN: RUN"#)
            .expect_clear()
            .expect_prints([" 1"])
            .expect_var("I", 1)
            .expect_program(None as Option<String>, "DATA 1: READ i: PRINT i")
            .check();
    }

    #[test]
    fn test_read_index_remains_out_of_bounds() {
        let mut t = Tester::default();
        t.run(r#"DATA 1: READ i, j"#).expect_var("i", 1).expect_err("1:17: Out of data").check();

        // This represents a second invocation in the REPL, and the read index is reset before this
        // execution, so the first and second data values are returned as expected.
        t.run(r#"DATA 1, 2: READ i, j"#).expect_var("i", 1).expect_var("j", 2).check();

        // Running `CLEAR` explicitly should resolve the issue described above and give us the
        // expected behavior.
        t.run(r#"CLEAR"#).expect_clear().check();
        t.run(r#"DATA 1, 2: READ i, j"#)
            .expect_clear()
            .expect_var("i", 1)
            .expect_var("j", 2)
            .check();
    }

    #[test]
    fn test_read_errors() {
        check_stmt_compilation_err("1:1: READ expected vref1[, .., vrefN]", "READ");
        check_stmt_compilation_err("1:6: READ expected vref1[, .., vrefN]", "READ 3");
        check_stmt_compilation_err("1:7: READ expected vref1[, .., vrefN]", "READ i; j");

        check_stmt_err(
            "1:34: Cannot assign value of type STRING to variable of type INTEGER",
            "DIM i AS INTEGER: DATA \"x\": READ i",
        );
        check_stmt_err(
            "1:36: Cannot assign value of type BOOLEAN to variable of type INTEGER",
            "DIM s AS INTEGER: DATA FALSE: READ s",
        );
    }

    #[test]
    fn test_restore_nothing() {
        Tester::default().run("RESTORE").check();
    }

    #[test]
    fn test_restore_before_read() {
        Tester::default()
            .run(
                r#"
            DATA 3, 5, 7
            RESTORE
            READ i: PRINT i
            READ i: PRINT i
            "#,
            )
            .expect_prints([" 3", " 5"])
            .expect_var("I", 5)
            .check();
    }

    #[test]
    fn test_restore_after_read() {
        Tester::default()
            .run(
                r#"
            DATA 3, -5, 7
            READ i: PRINT i
            READ i: PRINT i
            RESTORE
            READ i: PRINT i
            "#,
            )
            .expect_prints([" 3", "-5", " 3"])
            .expect_var("I", 3)
            .check();
    }

    #[test]
    fn test_restore_errors() {
        check_stmt_compilation_err("1:1: RESTORE expected no arguments", "RESTORE 123");
    }
}
