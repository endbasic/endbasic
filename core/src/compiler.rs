// EndBASIC
// Copyright 2022 Julio Merino
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

//! Converts our AST into bytecode.

use std::collections::HashMap;

use crate::ast::*;
use crate::bytecode::*;
use crate::reader::LineCol;

/// Compilation errors.
#[derive(Debug, thiserror::Error)]
#[error("{}:{}: {}", pos.line, pos.col, message)]
pub struct Error {
    pos: LineCol,
    message: String,
}

impl Error {
    /// Constructs a new compilation error from its parts.
    fn new<S: Into<String>>(pos: LineCol, message: S) -> Self {
        let message = message.into();
        Self { pos, message }
    }
}

/// Result for compiler return values.
pub type Result<T> = std::result::Result<T, Error>;

/// Indicates the type of fixup required at the address.
enum FixupType {
    Gosub,
    Goto,
    OnError,
}

/// Describes a location in the code needs fixing up after all addresses have been laid out.
struct Fixup {
    target: String,
    target_pos: LineCol,
    ftype: FixupType,
}

impl Fixup {
    /// Constructs a `Fixup` for a `GOSUB` instruction.
    fn from_gosub(span: GotoSpan) -> Self {
        Self { target: span.target, target_pos: span.target_pos, ftype: FixupType::Gosub }
    }

    /// Constructs a `Fixup` for a `GOTO` instruction.
    fn from_goto(span: GotoSpan) -> Self {
        Self { target: span.target, target_pos: span.target_pos, ftype: FixupType::Goto }
    }

    /// Constructs a `Fixup` for a `ON ERROR GOTO` instruction.
    fn from_on_error(span: GotoSpan) -> Self {
        Self { target: span.target, target_pos: span.target_pos, ftype: FixupType::OnError }
    }
}

/// Compilation context to accumulate the results of the translation of various translation units.
#[derive(Default)]
struct Compiler {
    /// Address of the next instruction to be emitted.
    next_pc: Address,

    /// Mapping of discovered labels to the addresses where they are.
    labels: HashMap<String, Address>,

    /// Mapping of addresses that need fixing up to the type of the fixup they require.
    fixups: HashMap<Address, Fixup>,

    /// Instructions compiled so far.
    instrs: Vec<Instruction>,

    /// Data discovered so far.
    data: Vec<Option<Value>>,
}

impl Compiler {
    /// Appends an instruction to the bytecode and returns its address.
    fn emit(&mut self, instr: Instruction) -> Address {
        let pc = self.next_pc;
        self.instrs.push(instr);
        self.next_pc += 1;
        pc
    }

    /// Compiles a `FOR` loop and appends its instructions to the compilation context.
    fn compile_for(&mut self, span: ForSpan) -> Result<()> {
        debug_assert!(
            span.iter.ref_type() == VarType::Auto
                || span.iter.ref_type() == VarType::Double
                || span.iter.ref_type() == VarType::Integer
        );

        if span.iter_double && span.iter.ref_type() == VarType::Auto {
            let skip_pc = self.emit(Instruction::Nop);

            self.emit(Instruction::Dim(DimSpan {
                name: span.iter.name().to_owned(),
                name_pos: span.iter_pos,
                vtype: VarType::Double,
                vtype_pos: span.iter_pos,
            }));

            self.instrs[skip_pc] = Instruction::JumpIfDefined(JumpIfDefinedSpan {
                var: span.iter.name().to_owned(),
                addr: self.next_pc,
            });
        }

        self.emit(Instruction::Assignment(AssignmentSpan {
            vref: span.iter.clone(),
            vref_pos: span.iter_pos,
            expr: span.start,
        }));

        let start_pc = self.emit(Instruction::Nop);

        self.compile_many(span.body)?;

        self.emit(Instruction::Assignment(AssignmentSpan {
            vref: span.iter,
            vref_pos: span.iter_pos,
            expr: span.next,
        }));

        self.emit(Instruction::Jump(JumpSpan { addr: start_pc }));

        self.instrs[start_pc] = Instruction::JumpIfNotTrue(JumpIfNotTrueSpan {
            cond: span.end,
            addr: self.next_pc,
            error_msg: "FOR supports numeric iteration only",
        });

        Ok(())
    }

    /// Compiles an `IF` statement and appends its instructions to the compilation context.
    fn compile_if(&mut self, span: IfSpan) -> Result<()> {
        let mut end_pcs = vec![];

        let mut iter = span.branches.into_iter();
        let mut next = iter.next();
        while let Some(branch) = next {
            let next2 = iter.next();

            let guard_pc = self.emit(Instruction::Nop);
            self.compile_many(branch.body)?;

            if next2.is_some() {
                end_pcs.push(self.next_pc);
                self.emit(Instruction::Nop);
            }

            self.instrs[guard_pc] = Instruction::JumpIfNotTrue(JumpIfNotTrueSpan {
                cond: branch.guard,
                addr: self.next_pc,
                error_msg: "IF/ELSEIF require a boolean condition",
            });

            next = next2;
        }

        for end_pc in end_pcs {
            self.instrs[end_pc] = Instruction::Jump(JumpSpan { addr: self.next_pc });
        }

        Ok(())
    }

    /// Compiles an `ON ERROR` statement and appends its instructions to the compilation context.
    fn compile_on_error(&mut self, span: OnErrorSpan) {
        match span {
            OnErrorSpan::Goto(span) => {
                let goto_pc = self.emit(Instruction::Nop);
                self.fixups.insert(goto_pc, Fixup::from_on_error(span));
            }
            OnErrorSpan::Reset => {
                self.emit(Instruction::SetErrorHandler(ErrorHandlerSpan::None));
            }
            OnErrorSpan::ResumeNext => {
                self.emit(Instruction::SetErrorHandler(ErrorHandlerSpan::ResumeNext));
            }
        }
    }

    /// Compiles a `WHILE` loop and appends its instructions to the compilation context.
    fn compile_while(&mut self, span: WhileSpan) -> Result<()> {
        let start_pc = self.emit(Instruction::Nop);

        self.compile_many(span.body)?;

        self.emit(Instruction::Jump(JumpSpan { addr: start_pc }));

        self.instrs[start_pc] = Instruction::JumpIfNotTrue(JumpIfNotTrueSpan {
            cond: span.expr,
            addr: self.next_pc,
            error_msg: "WHILE requires a boolean condition",
        });

        Ok(())
    }

    /// Compiles one statement and appends its bytecode to the current compilation context.
    fn compile_one(&mut self, stmt: Statement) -> Result<()> {
        match stmt {
            Statement::ArrayAssignment(span) => {
                self.emit(Instruction::ArrayAssignment(span));
            }

            Statement::Assignment(span) => {
                self.emit(Instruction::Assignment(span));
            }

            Statement::BuiltinCall(span) => {
                self.emit(Instruction::BuiltinCall(span));
            }

            Statement::Data(mut span) => {
                self.data.append(&mut span.values);
            }

            Statement::Dim(span) => {
                self.emit(Instruction::Dim(span));
            }

            Statement::DimArray(span) => {
                self.emit(Instruction::DimArray(span));
            }

            Statement::For(span) => {
                self.compile_for(span)?;
            }

            Statement::Gosub(span) => {
                let gosub_pc = self.emit(Instruction::Nop);
                self.fixups.insert(gosub_pc, Fixup::from_gosub(span));
            }

            Statement::Goto(span) => {
                let goto_pc = self.emit(Instruction::Nop);
                self.fixups.insert(goto_pc, Fixup::from_goto(span));
            }

            Statement::If(span) => {
                self.compile_if(span)?;
            }

            Statement::Label(span) => {
                if self.labels.insert(span.name.clone(), self.next_pc).is_some() {
                    return Err(Error::new(
                        span.name_pos,
                        format!("Duplicate label {}", span.name),
                    ));
                }
            }

            Statement::OnError(span) => {
                self.compile_on_error(span);
            }

            Statement::Return(span) => {
                self.emit(Instruction::Return(span));
            }

            Statement::While(span) => {
                self.compile_while(span)?;
            }
        }

        Ok(())
    }

    /// Compiles a collection of statements and appends their bytecode to the current compilation
    /// context.
    fn compile_many(&mut self, stmts: Vec<Statement>) -> Result<()> {
        for stmt in stmts {
            self.compile_one(stmt)?;
        }

        Ok(())
    }

    /// Finishes compilation and returns the image representing the compiled program.
    #[allow(clippy::wrong_self_convention)]
    fn to_image(mut self) -> Result<Image> {
        for (pc, fixup) in self.fixups {
            let addr = match self.labels.get(&fixup.target) {
                Some(addr) => *addr,
                None => {
                    return Err(Error::new(
                        fixup.target_pos,
                        format!("Unknown label {}", fixup.target),
                    ));
                }
            };

            match fixup.ftype {
                FixupType::Gosub => self.instrs[pc] = Instruction::Call(JumpSpan { addr }),
                FixupType::Goto => self.instrs[pc] = Instruction::Jump(JumpSpan { addr }),
                FixupType::OnError => {
                    self.instrs[pc] = Instruction::SetErrorHandler(ErrorHandlerSpan::Jump(addr))
                }
            }
        }
        Ok(Image { instrs: self.instrs, data: self.data })
    }
}

/// Compiles a collection of statements into an image ready for execution.
pub fn compile(stmts: Vec<Statement>) -> Result<Image> {
    let mut compiler = Compiler::default();
    compiler.compile_many(stmts)?;
    compiler.to_image()
}

#[cfg(test)]
mod testutils {
    use crate::parser;

    use super::*;

    /// Builder pattern to prepare the compiler for testing purposes.
    #[derive(Default)]
    #[must_use]
    pub(crate) struct Tester {
        stmts: Vec<Statement>,
    }

    impl Tester {
        /// Parses and appends statements to the list of statements to be compiled.
        pub(crate) fn parse(mut self, input: &str) -> Self {
            let mut stmts = parser::parse(&mut input.as_bytes()).unwrap();
            self.stmts.append(&mut stmts);
            self
        }

        /// Compiles the collection of accumulated statements and returns a `Checker` object to
        /// validate expectations about the compilation.
        pub(crate) fn compile(self) -> Checker {
            Checker {
                result: compile(self.stmts),
                exp_error: None,
                ignore_instrs: false,
                exp_instrs: vec![],
                exp_data: vec![],
            }
        }
    }

    /// Captures expectations about a compilation and validates them.
    #[must_use]
    pub(crate) struct Checker {
        result: Result<Image>,
        exp_error: Option<String>,
        ignore_instrs: bool,
        exp_instrs: Vec<Instruction>,
        exp_data: Vec<Option<Value>>,
    }

    impl Checker {
        /// Records an instruction to be expected in the compiled output with the given address.
        ///
        /// If the given address is past the last address of the bytecode, the bytecode is extended
        /// with "nops" until the given address.
        pub(crate) fn expect_instr(mut self, addr: Address, instr: Instruction) -> Self {
            if addr >= self.exp_instrs.len() {
                self.exp_instrs.resize_with(addr + 1, || Instruction::Nop);
            }
            self.exp_instrs[addr] = instr;
            self
        }

        /// Indicates that we do not care about the generated instructions in this test.
        pub(crate) fn ignore_instrs(mut self) -> Self {
            self.ignore_instrs = true;
            self
        }

        /// Records a new datum in the compiled output.
        pub(crate) fn expect_datum(mut self, datum: Option<Value>) -> Self {
            self.exp_data.push(datum);
            self
        }

        /// Records that the compilation should fail with the given `message`.
        pub(crate) fn expect_err<S: Into<String>>(mut self, message: S) -> Self {
            let message = message.into();
            self.exp_error = Some(message);
            self
        }

        /// Validates all expectations.
        pub(crate) fn check(self) {
            if let Some(message) = self.exp_error {
                assert_eq!(message, format!("{}", self.result.unwrap_err()));
                return;
            }
            let image = self.result.unwrap();

            if self.ignore_instrs {
                assert!(
                    self.exp_instrs.is_empty(),
                    "Cannot ignore instructions if some are expected"
                );
            } else {
                assert_eq!(self.exp_instrs, image.instrs);
            }
            assert_eq!(self.exp_data, image.data);
        }
    }

    /// Syntactic sugar to instantiate a `LineCol` for testing.
    pub(crate) fn lc(line: usize, col: usize) -> LineCol {
        LineCol { line, col }
    }
}

#[cfg(test)]
mod tests {
    use super::testutils::*;
    use super::*;

    #[test]
    fn test_compile_nothing() {
        Tester::default().compile().check();
    }

    #[test]
    fn test_compile_array_assignment() {
        Tester::default()
            .parse("foo(3) = 5")
            .compile()
            .expect_instr(
                0,
                Instruction::ArrayAssignment(ArrayAssignmentSpan {
                    vref: VarRef::new("foo", VarType::Auto),
                    vref_pos: lc(1, 1),
                    subscripts: vec![Expr::Integer(IntegerSpan { value: 3, pos: lc(1, 5) })],
                    expr: Expr::Integer(IntegerSpan { value: 5, pos: lc(1, 10) }),
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_assignment() {
        Tester::default()
            .parse("foo = 5")
            .compile()
            .expect_instr(
                0,
                Instruction::Assignment(AssignmentSpan {
                    vref: VarRef::new("foo", VarType::Auto),
                    vref_pos: lc(1, 1),
                    expr: Expr::Integer(IntegerSpan { value: 5, pos: lc(1, 7) }),
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_builtin_call() {
        Tester::default()
            .parse("CMD")
            .compile()
            .expect_instr(
                0,
                Instruction::BuiltinCall(BuiltinCallSpan {
                    name: "CMD".to_owned(),
                    name_pos: lc(1, 1),
                    args: vec![],
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_data_top_level() {
        Tester::default()
            .parse("DATA TRUE, 3\nDATA , 1")
            .compile()
            .expect_datum(Some(Value::Boolean(true)))
            .expect_datum(Some(Value::Integer(3)))
            .expect_datum(None)
            .expect_datum(Some(Value::Integer(1)))
            .check();
    }

    #[test]
    fn test_compile_data_interspersed() {
        Tester::default()
            .parse("IF FALSE THEN: DATA TRUE: END IF")
            .parse("FOR i = 1 TO 10: DATA , 5: NEXT")
            .parse("WHILE FALSE: DATA 2.3: WEND")
            .compile()
            .expect_datum(Some(Value::Boolean(true)))
            .expect_datum(None)
            .expect_datum(Some(Value::Integer(5)))
            .expect_datum(Some(Value::Double(2.3)))
            .ignore_instrs()
            .check();
    }

    #[test]
    fn test_compile_dim() {
        Tester::default()
            .parse("DIM var AS INTEGER")
            .compile()
            .expect_instr(
                0,
                Instruction::Dim(DimSpan {
                    name: "var".to_owned(),
                    name_pos: lc(1, 5),
                    vtype: VarType::Integer,
                    vtype_pos: lc(1, 12),
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_dim_array() {
        Tester::default()
            .parse("DIM var(1) AS INTEGER")
            .compile()
            .expect_instr(
                0,
                Instruction::DimArray(DimArraySpan {
                    name: "var".to_owned(),
                    name_pos: lc(1, 5),
                    dimensions: vec![Expr::Integer(IntegerSpan { value: 1, pos: lc(1, 9) })],
                    subtype: VarType::Integer,
                    subtype_pos: lc(1, 15),
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_for_simple() {
        Tester::default()
            .parse("FOR iter = 1 TO 5: a = FALSE: NEXT")
            .compile()
            .expect_instr(
                0,
                Instruction::Assignment(AssignmentSpan {
                    vref: VarRef::new("iter", VarType::Auto),
                    vref_pos: lc(1, 5),
                    expr: Expr::Integer(IntegerSpan { value: 1, pos: lc(1, 12) }),
                }),
            )
            .expect_instr(
                1,
                Instruction::JumpIfNotTrue(JumpIfNotTrueSpan {
                    cond: Expr::LessEqual(Box::from(BinaryOpSpan {
                        lhs: Expr::Symbol(SymbolSpan {
                            vref: VarRef::new("iter", VarType::Auto),
                            pos: lc(1, 5),
                        }),
                        rhs: Expr::Integer(IntegerSpan { value: 5, pos: lc(1, 17) }),
                        pos: lc(1, 14),
                    })),
                    addr: 5,
                    error_msg: "FOR supports numeric iteration only",
                }),
            )
            .expect_instr(
                2,
                Instruction::Assignment(AssignmentSpan {
                    vref: VarRef::new("a", VarType::Auto),
                    vref_pos: lc(1, 20),
                    expr: Expr::Boolean(BooleanSpan { value: false, pos: lc(1, 24) }),
                }),
            )
            .expect_instr(
                3,
                Instruction::Assignment(AssignmentSpan {
                    vref: VarRef::new("iter", VarType::Auto),
                    vref_pos: lc(1, 5),
                    expr: Expr::Add(Box::from(BinaryOpSpan {
                        lhs: Expr::Symbol(SymbolSpan {
                            vref: VarRef::new("iter", VarType::Auto),
                            pos: lc(1, 5),
                        }),
                        rhs: Expr::Integer(IntegerSpan { value: 1, pos: lc(1, 18) }),
                        pos: lc(1, 14),
                    })),
                }),
            )
            .expect_instr(4, Instruction::Jump(JumpSpan { addr: 1 }))
            .check();
    }

    #[test]
    fn test_compile_for_double_auto_iterator() {
        Tester::default()
            .parse("FOR iter = 0 TO 2 STEP 0.1\nNEXT")
            .compile()
            .expect_instr(
                0,
                Instruction::JumpIfDefined(JumpIfDefinedSpan { var: "iter".to_owned(), addr: 2 }),
            )
            .expect_instr(
                1,
                Instruction::Dim(DimSpan {
                    name: "iter".to_owned(),
                    name_pos: lc(1, 5),
                    vtype: VarType::Double,
                    vtype_pos: lc(1, 5),
                }),
            )
            .expect_instr(
                2,
                Instruction::Assignment(AssignmentSpan {
                    vref: VarRef::new("iter", VarType::Auto),
                    vref_pos: lc(1, 5),
                    expr: Expr::Integer(IntegerSpan { value: 0, pos: lc(1, 12) }),
                }),
            )
            .expect_instr(
                3,
                Instruction::JumpIfNotTrue(JumpIfNotTrueSpan {
                    cond: Expr::LessEqual(Box::from(BinaryOpSpan {
                        lhs: Expr::Symbol(SymbolSpan {
                            vref: VarRef::new("iter", VarType::Auto),
                            pos: lc(1, 5),
                        }),
                        rhs: Expr::Integer(IntegerSpan { value: 2, pos: lc(1, 17) }),
                        pos: lc(1, 14),
                    })),
                    addr: 6,
                    error_msg: "FOR supports numeric iteration only",
                }),
            )
            .expect_instr(
                4,
                Instruction::Assignment(AssignmentSpan {
                    vref: VarRef::new("iter", VarType::Auto),
                    vref_pos: lc(1, 5),
                    expr: Expr::Add(Box::from(BinaryOpSpan {
                        lhs: Expr::Symbol(SymbolSpan {
                            vref: VarRef::new("iter", VarType::Auto),
                            pos: lc(1, 5),
                        }),
                        rhs: Expr::Double(DoubleSpan { value: 0.1, pos: lc(1, 24) }),
                        pos: lc(1, 14),
                    })),
                }),
            )
            .expect_instr(5, Instruction::Jump(JumpSpan { addr: 3 }))
            .check();
    }

    #[test]
    fn test_compile_goto() {
        Tester::default()
            .parse("@first: GOTO @second")
            .parse("@second: GOTO @first")
            .compile()
            .expect_instr(0, Instruction::Jump(JumpSpan { addr: 1 }))
            .expect_instr(1, Instruction::Jump(JumpSpan { addr: 0 }))
            .check();
    }

    #[test]
    fn test_compile_gosub_and_return() {
        Tester::default()
            .parse("@sub\nFOO\nRETURN\nGOSUB @sub")
            .compile()
            .expect_instr(
                0,
                Instruction::BuiltinCall(BuiltinCallSpan {
                    name: "FOO".to_owned(),
                    name_pos: lc(2, 1),
                    args: vec![],
                }),
            )
            .expect_instr(1, Instruction::Return(ReturnSpan { pos: lc(3, 1) }))
            .expect_instr(2, Instruction::Call(JumpSpan { addr: 0 }))
            .check();
    }

    #[test]
    fn test_compile_goto_unknown_label() {
        Tester::default()
            .parse("@fo: GOTO @foo")
            .compile()
            .expect_err("1:11: Unknown label foo")
            .check();
    }

    #[test]
    fn test_compile_if_one_branch() {
        Tester::default()
            .parse("IF FALSE THEN: FOO: END IF")
            .compile()
            .expect_instr(
                0,
                Instruction::JumpIfNotTrue(JumpIfNotTrueSpan {
                    cond: Expr::Boolean(BooleanSpan { value: false, pos: lc(1, 4) }),
                    addr: 2,
                    error_msg: "IF/ELSEIF require a boolean condition",
                }),
            )
            .expect_instr(
                1,
                Instruction::BuiltinCall(BuiltinCallSpan {
                    name: "FOO".to_owned(),
                    name_pos: lc(1, 16),
                    args: vec![],
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_if_many_branches() {
        Tester::default()
            .parse("IF FALSE THEN\nFOO\nELSEIF TRUE THEN\nBAR\nELSE\nBAZ\nEND IF")
            .compile()
            .expect_instr(
                0,
                Instruction::JumpIfNotTrue(JumpIfNotTrueSpan {
                    cond: Expr::Boolean(BooleanSpan { value: false, pos: lc(1, 4) }),
                    addr: 3,
                    error_msg: "IF/ELSEIF require a boolean condition",
                }),
            )
            .expect_instr(
                1,
                Instruction::BuiltinCall(BuiltinCallSpan {
                    name: "FOO".to_owned(),
                    name_pos: lc(2, 1),
                    args: vec![],
                }),
            )
            .expect_instr(2, Instruction::Jump(JumpSpan { addr: 8 }))
            .expect_instr(
                3,
                Instruction::JumpIfNotTrue(JumpIfNotTrueSpan {
                    cond: Expr::Boolean(BooleanSpan { value: true, pos: lc(3, 8) }),
                    addr: 6,
                    error_msg: "IF/ELSEIF require a boolean condition",
                }),
            )
            .expect_instr(
                4,
                Instruction::BuiltinCall(BuiltinCallSpan {
                    name: "BAR".to_owned(),
                    name_pos: lc(4, 1),
                    args: vec![],
                }),
            )
            .expect_instr(5, Instruction::Jump(JumpSpan { addr: 8 }))
            .expect_instr(
                6,
                Instruction::JumpIfNotTrue(JumpIfNotTrueSpan {
                    cond: Expr::Boolean(BooleanSpan { value: true, pos: lc(5, 1) }),
                    addr: 8,
                    error_msg: "IF/ELSEIF require a boolean condition",
                }),
            )
            .expect_instr(
                7,
                Instruction::BuiltinCall(BuiltinCallSpan {
                    name: "BAZ".to_owned(),
                    name_pos: lc(6, 1),
                    args: vec![],
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_on_error_reset() {
        Tester::default()
            .parse("ON ERROR GOTO 0")
            .compile()
            .expect_instr(0, Instruction::SetErrorHandler(ErrorHandlerSpan::None))
            .check();
    }

    #[test]
    fn test_compile_on_error_goto_label() {
        Tester::default()
            .parse("ON ERROR GOTO @foo\n\n\n@foo")
            .compile()
            .expect_instr(0, Instruction::SetErrorHandler(ErrorHandlerSpan::Jump(1)))
            .check();
    }

    #[test]
    fn test_compile_on_error_goto_unknown_label() {
        Tester::default()
            .parse("ON ERROR GOTO @foo")
            .compile()
            .expect_err("1:15: Unknown label foo")
            .check();
    }

    #[test]
    fn test_compile_on_error_resume_next() {
        Tester::default()
            .parse("ON ERROR RESUME NEXT")
            .compile()
            .expect_instr(0, Instruction::SetErrorHandler(ErrorHandlerSpan::ResumeNext))
            .check();
    }

    #[test]
    fn test_compile_while() {
        Tester::default()
            .parse("WHILE TRUE\nFOO\nWEND")
            .compile()
            .expect_instr(
                0,
                Instruction::JumpIfNotTrue(JumpIfNotTrueSpan {
                    cond: Expr::Boolean(BooleanSpan { value: true, pos: lc(1, 7) }),
                    addr: 3,
                    error_msg: "WHILE requires a boolean condition",
                }),
            )
            .expect_instr(
                1,
                Instruction::BuiltinCall(BuiltinCallSpan {
                    name: "FOO".to_owned(),
                    name_pos: lc(2, 1),
                    args: vec![],
                }),
            )
            .expect_instr(2, Instruction::Jump(JumpSpan { addr: 0 }))
            .check();
    }
}
