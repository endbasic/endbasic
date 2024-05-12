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

use crate::ast::*;
use crate::bytecode::*;
use crate::reader::LineCol;
use crate::syms::{Symbol, SymbolKey, Symbols};
use std::collections::HashMap;
use std::fmt;

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

/// Represents type of an expression.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum ExprType {
    Boolean,
    Double,
    Integer,
    Text,
}

impl From<VarType> for ExprType {
    fn from(value: VarType) -> Self {
        match value {
            VarType::Auto => unreachable!(),
            VarType::Boolean => ExprType::Boolean,
            VarType::Double => ExprType::Double,
            VarType::Integer => ExprType::Integer,
            VarType::Text => ExprType::Text,
            VarType::Void => unreachable!(),
        }
    }
}

impl From<ExprType> for VarType {
    fn from(value: ExprType) -> Self {
        match value {
            ExprType::Boolean => VarType::Boolean,
            ExprType::Double => VarType::Double,
            ExprType::Integer => VarType::Integer,
            ExprType::Text => VarType::Text,
        }
    }
}

impl fmt::Display for ExprType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExprType::Boolean => write!(f, "BOOLEAN"),
            ExprType::Double => write!(f, "DOUBLE"),
            ExprType::Integer => write!(f, "INTEGER"),
            ExprType::Text => write!(f, "STRING"),
        }
    }
}

/// Represents the type of a callable.
///
/// This is a superset of `ExprType` with the addition of the `Void` required to represent
/// commands.
#[derive(Clone, Copy, PartialEq)]
#[cfg_attr(any(debug_assertions, test), derive(Debug))]
pub(crate) enum CallableType {
    Boolean,
    Double,
    Integer,
    Text,
    Void,
}

impl From<VarType> for CallableType {
    fn from(value: VarType) -> Self {
        match value {
            VarType::Auto => unreachable!(),
            VarType::Boolean => CallableType::Boolean,
            VarType::Double => CallableType::Double,
            VarType::Integer => CallableType::Integer,
            VarType::Text => CallableType::Text,
            VarType::Void => CallableType::Void,
        }
    }
}

impl From<CallableType> for VarType {
    fn from(value: CallableType) -> Self {
        match value {
            CallableType::Boolean => VarType::Boolean,
            CallableType::Double => VarType::Double,
            CallableType::Integer => VarType::Integer,
            CallableType::Text => VarType::Text,
            CallableType::Void => VarType::Void,
        }
    }
}

impl CallableType {
    /// Returns the expression type of this callable, or `None` if this corresponds to a command.
    fn as_expr_type(self) -> Option<ExprType> {
        match self {
            CallableType::Boolean => Some(ExprType::Boolean),
            CallableType::Double => Some(ExprType::Double),
            CallableType::Integer => Some(ExprType::Integer),
            CallableType::Text => Some(ExprType::Text),
            CallableType::Void => None,
        }
    }
}

/// Information about a symbol in the symbols table.
#[derive(Clone, Copy)]
#[cfg_attr(any(debug_assertions, test), derive(Debug, PartialEq))]
pub(crate) enum SymbolPrototype {
    /// Information about an array.
    Array(ExprType),

    /// Information about a callable.  The boolean indicates if this callable is an argless function
    /// or not.
    Callable(CallableType, bool),

    /// Information about a variable.
    Variable(#[allow(unused)] ExprType),
}

/// Type for the symbols table.
#[derive(Default)]
#[cfg_attr(test, derive(Debug))]
pub(crate) struct SymbolsTable {
    table: HashMap<SymbolKey, SymbolPrototype>,
}

impl From<HashMap<SymbolKey, SymbolPrototype>> for SymbolsTable {
    fn from(table: HashMap<SymbolKey, SymbolPrototype>) -> Self {
        Self { table }
    }
}

impl From<&Symbols> for SymbolsTable {
    fn from(syms: &Symbols) -> Self {
        let mut table = HashMap::default();
        for (name, symbol) in syms.as_hashmap() {
            let proto = match symbol {
                Symbol::Array(array) => SymbolPrototype::Array(array.subtype().into()),
                Symbol::Callable(callable) => {
                    let md = callable.metadata();
                    SymbolPrototype::Callable(md.return_type().into(), md.is_argless())
                }
                Symbol::Variable(var) => SymbolPrototype::Variable(var.as_vartype().into()),
            };
            debug_assert_eq!(name, &name.to_ascii_uppercase());
            table.insert(SymbolKey::from(name), proto);
        }
        Self { table }
    }
}

impl SymbolsTable {
    /// Returns true if the symbols table contains `key`.
    fn contains_key(&mut self, key: &SymbolKey) -> bool {
        self.table.contains_key(key)
    }

    /// Returns the information for the symbol `key` if it exists, otherwise `None`.
    fn get(&self, key: &SymbolKey) -> Option<SymbolPrototype> {
        self.table.get(key).copied()
    }

    /// Inserts the new information `proto` about symbol `key` into the symbols table.
    /// The symbol must not yet exist.
    fn insert(&mut self, key: SymbolKey, proto: SymbolPrototype) {
        let previous = self.table.insert(key, proto);
        assert!(previous.is_none(), "Cannot redefine a symbol");
    }

    /// Removes information about the symbol `key`.
    fn remove(&mut self, key: SymbolKey) {
        let previous = self.table.remove(&key);
        assert!(previous.is_some(), "Cannot unset a non-existing symbol");
    }
}

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
    /// Constructs a `Fixup` for an `EXIT DO` instruction.
    fn from_exit_do(target: String, span: ExitDoSpan) -> Self {
        Self { target, target_pos: span.pos, ftype: FixupType::Goto }
    }

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

    /// Current nesting of `DO` loops, needed to assign targets for `EXIT DO` statements.
    ///
    /// The first component of this pair indicates which block of `EXIT DO`s we are dealing with and
    /// the second component indicates their nesting.  Every time the second component reaches zero,
    /// the first component has to be incremented.
    exit_do_level: (usize, usize),

    /// Current number of `SELECT` statements, needed to assign internal variable names.
    selects: usize,

    /// Mapping of discovered labels to the addresses where they are.
    labels: HashMap<String, Address>,

    /// Mapping of addresses that need fixing up to the type of the fixup they require.
    fixups: HashMap<Address, Fixup>,

    /// Instructions compiled so far.
    instrs: Vec<Instruction>,

    /// Data discovered so far.
    data: Vec<Option<Value>>,

    /// Symbols table.
    symtable: SymbolsTable,
}

impl Compiler {
    /// Appends an instruction to the bytecode and returns its address.
    fn emit(&mut self, instr: Instruction) -> Address {
        let pc = self.next_pc;
        self.instrs.push(instr);
        self.next_pc += 1;
        pc
    }

    /// Generates a fake label for the end of a `DO` loop based on the current nesting `level`.
    ///
    /// This is a little hack to reuse the same machinery that handles `GOTO`s to handle early exits
    /// in `DO` loops.  We can do this because we know that users cannot specify custom labels that
    /// start with a digit and all user-provided labels that do start with a digit are also fully
    /// numeric.
    fn do_label(level: (usize, usize)) -> String {
        format!("0do{}_{}", level.0, level.1)
    }

    /// Generates an internal variable name to hold the result of a `SELECT` test evaluation.
    ///
    /// This is a little hack needed because we don't yet have a value stack nor registers.  We can
    /// do this because we know that users cannot specify custom variable names that start with a
    /// digit.
    fn select_test_var_name(selects: usize) -> String {
        format!("0select{}", selects)
    }

    /// Emits the necessary casts to convert the value at the top of the stack from its type `from`
    /// to the new type `target`.
    ///
    /// Returns `target` if the conversion is possible, or `from` otherwise.
    fn maybe_cast(&mut self, target: ExprType, from: ExprType) -> ExprType {
        match (target, from) {
            (ExprType::Double, ExprType::Integer) => {
                self.emit(Instruction::IntegerToDouble);
                target
            }
            (ExprType::Integer, ExprType::Double) => {
                self.emit(Instruction::DoubleToInteger);
                target
            }
            _ => from,
        }
    }

    /// Compiles an assignment, be it from the code or one synthesized during compilation.
    ///
    /// It's important to always use this function instead of manually emitting `Instruction::Assign`
    /// instructions to ensure consistent handling of the symbols table.
    fn compile_assignment(&mut self, vref: VarRef, vref_pos: LineCol, expr: Expr) -> Result<()> {
        let key = SymbolKey::from(&vref.name());
        let etype = self.compile_expr(expr, false)?;

        let vtype = match self.symtable.get(&key) {
            Some(SymbolPrototype::Variable(vtype)) => vtype,
            Some(_) => {
                return Err(Error::new(vref_pos, format!("Cannot redefine {} as a variable", vref)))
            }
            None => {
                // TODO(jmmv): Compile separate Dim instructions for new variables instead of
                // checking this every time.
                let key = key.clone();
                if vref.ref_type() == VarType::Auto {
                    self.symtable.insert(key, SymbolPrototype::Variable(etype));
                    etype
                } else {
                    self.symtable.insert(key, SymbolPrototype::Variable(vref.ref_type().into()));
                    vref.ref_type().into()
                }
            }
        };

        let etype = self.maybe_cast(vtype, etype);
        if etype != vtype {
            return Err(Error::new(
                vref_pos,
                format!("Cannot assign value of type {} to variable of type {}", etype, vtype,),
            ));
        }

        if vref.ref_type() != VarType::Auto && vref.ref_type() != vtype.into() {
            return Err(Error::new(vref_pos, format!("Incompatible types in {} reference", vref)));
        }

        self.emit(Instruction::Assign(key));

        Ok(())
    }

    /// Compiles a `DIM` statement.
    fn compile_dim(&mut self, span: DimSpan) -> Result<()> {
        let key = SymbolKey::from(&span.name);
        if self.symtable.contains_key(&key) {
            return Err(Error::new(
                span.name_pos,
                format!("Cannot DIM already-defined symbol {}", span.name),
            ));
        }

        self.emit(Instruction::Dim(key.clone(), span.vtype));
        self.symtable.insert(key, SymbolPrototype::Variable(span.vtype.into()));

        Ok(())
    }

    /// Compiles a `DO` loop and appends its instructions to the compilation context.
    fn compile_do(&mut self, span: DoSpan) -> Result<()> {
        self.exit_do_level.1 += 1;

        let end_pc;
        match span.guard {
            DoGuard::Infinite => {
                let start_pc = self.next_pc;
                self.compile_many(span.body)?;
                end_pc = self.emit(Instruction::Jump(JumpISpan { addr: start_pc }));
            }

            DoGuard::PreUntil(guard) => {
                let start_pc = self.next_pc;
                self.compile_expr(guard, false)?;
                let jump_pc = self.emit(Instruction::Nop);
                self.compile_many(span.body)?;
                end_pc = self.emit(Instruction::Jump(JumpISpan { addr: start_pc }));
                self.instrs[jump_pc] = Instruction::JumpIfTrue(JumpIfBoolISpan {
                    addr: self.next_pc,
                    error_msg: "DO requires a boolean condition",
                });
            }

            DoGuard::PreWhile(guard) => {
                let start_pc = self.next_pc;
                self.compile_expr(guard, false)?;
                let jump_pc = self.emit(Instruction::Nop);
                self.compile_many(span.body)?;
                end_pc = self.emit(Instruction::Jump(JumpISpan { addr: start_pc }));
                self.instrs[jump_pc] = Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: self.next_pc,
                    error_msg: "DO requires a boolean condition",
                });
            }

            DoGuard::PostUntil(guard) => {
                let start_pc = self.next_pc;
                self.compile_many(span.body)?;
                self.compile_expr(guard, false)?;
                end_pc = self.emit(Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: start_pc,
                    error_msg: "LOOP requires a boolean condition",
                }));
            }

            DoGuard::PostWhile(guard) => {
                let start_pc = self.next_pc;
                self.compile_many(span.body)?;
                self.compile_expr(guard, false)?;
                end_pc = self.emit(Instruction::JumpIfTrue(JumpIfBoolISpan {
                    addr: start_pc,
                    error_msg: "LOOP requires a boolean condition",
                }));
            }
        }

        let existing = self.labels.insert(Compiler::do_label(self.exit_do_level), end_pc + 1);
        assert!(existing.is_none(), "Auto-generated label must be unique");
        self.exit_do_level.1 -= 1;
        if self.exit_do_level.1 == 0 {
            self.exit_do_level.0 += 1;
        }

        Ok(())
    }

    /// Compiles a `FOR` loop and appends its instructions to the compilation context.
    fn compile_for(&mut self, span: ForSpan) -> Result<()> {
        debug_assert!(
            span.iter.ref_type() == VarType::Auto
                || span.iter.ref_type() == VarType::Double
                || span.iter.ref_type() == VarType::Integer
        );

        if span.iter_double && span.iter.ref_type() == VarType::Auto {
            let key = SymbolKey::from(span.iter.name());
            let skip_pc = self.emit(Instruction::Nop);

            if self.symtable.get(&key).is_none() {
                self.emit(Instruction::Dim(key, VarType::Double));
                self.symtable.insert(
                    SymbolKey::from(span.iter.name()),
                    SymbolPrototype::Variable(ExprType::Double),
                );
            }

            self.instrs[skip_pc] = Instruction::JumpIfDefined(JumpIfDefinedISpan {
                var: span.iter.name().to_owned(),
                addr: self.next_pc,
            });
        }

        self.compile_assignment(span.iter.clone(), span.iter_pos, span.start)?;

        let start_pc = self.next_pc;
        self.compile_expr(span.end, false)?;
        let jump_pc = self.emit(Instruction::Nop);

        self.compile_many(span.body)?;

        self.compile_assignment(span.iter.clone(), span.iter_pos, span.next)?;

        self.emit(Instruction::Jump(JumpISpan { addr: start_pc }));

        self.instrs[jump_pc] = Instruction::JumpIfNotTrue(JumpIfBoolISpan {
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

            self.compile_expr(branch.guard, false)?;
            let jump_pc = self.emit(Instruction::Nop);
            self.compile_many(branch.body)?;

            if next2.is_some() {
                end_pcs.push(self.next_pc);
                self.emit(Instruction::Nop);
            }

            self.instrs[jump_pc] = Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                addr: self.next_pc,
                error_msg: "IF/ELSEIF require a boolean condition",
            });

            next = next2;
        }

        for end_pc in end_pcs {
            self.instrs[end_pc] = Instruction::Jump(JumpISpan { addr: self.next_pc });
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
                self.emit(Instruction::SetErrorHandler(ErrorHandlerISpan::None));
            }
            OnErrorSpan::ResumeNext => {
                self.emit(Instruction::SetErrorHandler(ErrorHandlerISpan::ResumeNext));
            }
        }
    }

    /// Generates the expression to evaluate a list of `guards`, which are compared against the
    /// test expression stored in `test_vref`.
    fn compile_case_guards(test_vref: &VarRef, guards: Vec<CaseGuardSpan>) -> Option<Expr> {
        let mut expr = None;
        for guard in guards {
            let one_expr = match guard {
                CaseGuardSpan::Is(relop, expr) => {
                    let pos = expr.start_pos();
                    let test_expr = Expr::Symbol(SymbolSpan { vref: test_vref.clone(), pos });
                    let binop = Box::from(BinaryOpSpan { lhs: test_expr, rhs: expr, pos });
                    match relop {
                        CaseRelOp::Equal => Expr::Equal(binop),
                        CaseRelOp::NotEqual => Expr::NotEqual(binop),
                        CaseRelOp::Less => Expr::Less(binop),
                        CaseRelOp::LessEqual => Expr::LessEqual(binop),
                        CaseRelOp::Greater => Expr::Greater(binop),
                        CaseRelOp::GreaterEqual => Expr::GreaterEqual(binop),
                    }
                }

                CaseGuardSpan::To(from_expr, to_expr) => {
                    let from_pos = from_expr.start_pos();
                    let to_pos = to_expr.start_pos();
                    let test_expr =
                        Expr::Symbol(SymbolSpan { vref: test_vref.clone(), pos: from_pos });
                    Expr::And(Box::from(BinaryOpSpan {
                        lhs: Expr::GreaterEqual(Box::from(BinaryOpSpan {
                            lhs: test_expr.clone(),
                            rhs: from_expr,
                            pos: from_pos,
                        })),
                        rhs: Expr::LessEqual(Box::from(BinaryOpSpan {
                            lhs: test_expr,
                            rhs: to_expr,
                            pos: to_pos,
                        })),
                        pos: from_pos,
                    }))
                }
            };

            expr = match expr {
                None => Some(one_expr),
                Some(expr) => {
                    let pos = expr.start_pos();
                    Some(Expr::Or(Box::from(BinaryOpSpan { lhs: expr, rhs: one_expr, pos })))
                }
            };
        }
        expr
    }

    /// Compiles a `SELECT` statement and appends its instructions to the compilation context.
    fn compile_select(&mut self, span: SelectSpan) -> Result<()> {
        let mut end_pcs = vec![];

        self.selects += 1;
        let test_vref = VarRef::new(Compiler::select_test_var_name(self.selects), VarType::Auto);
        self.compile_assignment(test_vref.clone(), span.expr.start_pos(), span.expr)?;

        let mut iter = span.cases.into_iter();
        let mut next = iter.next();
        while let Some(case) = next {
            let next2 = iter.next();

            match Compiler::compile_case_guards(&test_vref, case.guards) {
                None => {
                    self.compile_many(case.body)?;
                }
                Some(guard) => {
                    self.compile_expr(guard, false)?;
                    let jump_pc = self.emit(Instruction::Nop);
                    self.compile_many(case.body)?;

                    if next2.is_some() {
                        end_pcs.push(self.next_pc);
                        self.emit(Instruction::Nop);
                    }

                    self.instrs[jump_pc] = Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                        addr: self.next_pc,
                        error_msg: "SELECT requires a boolean condition",
                    });
                }
            }

            next = next2;
        }

        for end_pc in end_pcs {
            self.instrs[end_pc] = Instruction::Jump(JumpISpan { addr: self.next_pc });
        }

        let test_key = SymbolKey::from(test_vref.name());
        self.emit(Instruction::Unset(UnsetISpan {
            name: test_vref.take_name(),
            pos: span.end_pos,
        }));
        self.symtable.remove(test_key);

        Ok(())
    }

    /// Compiles a `WHILE` loop and appends its instructions to the compilation context.
    fn compile_while(&mut self, span: WhileSpan) -> Result<()> {
        let start_pc = self.next_pc;
        self.compile_expr(span.expr, false)?;
        let jump_pc = self.emit(Instruction::Nop);

        self.compile_many(span.body)?;

        self.emit(Instruction::Jump(JumpISpan { addr: start_pc }));

        self.instrs[jump_pc] = Instruction::JumpIfNotTrue(JumpIfBoolISpan {
            addr: self.next_pc,
            error_msg: "WHILE requires a boolean condition",
        });

        Ok(())
    }

    /// Compiles a logical or bitwise unary operator and appends its instructions to the compilation
    /// context.
    fn compile_not_op(&mut self, span: UnaryOpSpan) -> Result<ExprType> {
        let expr_type = self.compile_expr(span.expr, false)?;
        match expr_type {
            ExprType::Boolean | ExprType::Integer => (),
            _ => {
                return Err(Error::new(span.pos, format!("Cannot apply NOT to {}", expr_type)));
            }
        };
        self.emit(Instruction::Not(span.pos));
        Ok(expr_type)
    }

    /// Compiles a negate operator and appends its instructions to the compilation context.
    fn compile_neg_op(&mut self, span: UnaryOpSpan) -> Result<ExprType> {
        let expr_type = self.compile_expr(span.expr, false)?;
        match expr_type {
            ExprType::Double | ExprType::Integer => (),
            _ => {
                return Err(Error::new(span.pos, format!("Cannot negate {}", expr_type)));
            }
        };
        self.emit(Instruction::Negate(span.pos));
        Ok(expr_type)
    }

    /// Compiles a logical binary operator and appends its instructions to the compilation context.
    fn compile_logical_binary_op<F: Fn(LineCol) -> Instruction>(
        &mut self,
        make_inst: F,
        span: BinaryOpSpan,
        op_name: &str,
    ) -> Result<ExprType> {
        let lhs_type = self.compile_expr(span.lhs, false)?;
        let rhs_type = self.compile_expr(span.rhs, false)?;
        let result = match (lhs_type, rhs_type) {
            (ExprType::Boolean, ExprType::Boolean) => ExprType::Boolean,
            (ExprType::Integer, ExprType::Integer) => ExprType::Integer,
            (_, _) => {
                return Err(Error::new(
                    span.pos,
                    format!("Cannot {} {} and {}", op_name, lhs_type, rhs_type),
                ));
            }
        };

        self.emit(make_inst(span.pos));
        Ok(result)
    }

    /// Compiles a logical or bitwise binary operator and appends its instructions to the
    /// compilation context.
    fn compile_equality_binary_op<F: Fn(LineCol) -> Instruction>(
        &mut self,
        make_inst: F,
        span: BinaryOpSpan,
        op_name: &str,
    ) -> Result<ExprType> {
        let lhs_type = self.compile_expr(span.lhs, false)?;
        let pc = self.next_pc;
        self.emit(Instruction::Nop);

        let mut keep_nop = false;
        let rhs_type = self.compile_expr(span.rhs, false)?;
        match (lhs_type, rhs_type) {
            (lhs_type, rhs_type) if lhs_type == rhs_type => (),

            (ExprType::Double, ExprType::Integer) => {
                self.emit(Instruction::IntegerToDouble);
            }

            (ExprType::Integer, ExprType::Double) => {
                self.instrs[pc] = Instruction::IntegerToDouble;
                keep_nop = true;
            }

            (_, _) => {
                return Err(Error::new(
                    span.pos,
                    format!("Cannot compare {} and {} with {}", lhs_type, rhs_type, op_name),
                ));
            }
        };

        if !keep_nop {
            self.instrs.remove(pc);
            self.next_pc -= 1;
        }

        self.emit(make_inst(span.pos));

        Ok(ExprType::Boolean)
    }

    /// Compiles a binary shift operator and appends its instructions to the compilation context.
    fn compile_shift_binary_op<F: Fn(LineCol) -> Instruction>(
        &mut self,
        make_inst: F,
        span: BinaryOpSpan,
        op_name: &str,
    ) -> Result<ExprType> {
        let lhs_type = self.compile_expr(span.lhs, false)?;
        match lhs_type {
            ExprType::Integer => (),
            _ => {
                return Err(Error::new(
                    span.pos,
                    format!("Cannot apply {} to {}", op_name, lhs_type),
                ));
            }
        };

        let rhs_type = self.compile_expr(span.rhs, false)?;
        match rhs_type {
            ExprType::Integer => (),
            _ => {
                return Err(Error::new(
                    span.pos,
                    format!(
                        "Number of bits to {} must be an {}, not a {}",
                        op_name,
                        ExprType::Integer,
                        rhs_type
                    ),
                ));
            }
        };

        self.emit(make_inst(span.pos));

        Ok(ExprType::Integer)
    }

    /// Compiles the evaluation of an expression, appends its instructions to the
    /// Compiles a binary operator and appends its instructions to the compilation context.
    fn compile_arithmetic_binary_op<F: Fn(LineCol) -> Instruction>(
        &mut self,
        make_inst: F,
        span: BinaryOpSpan,
        op_name: &str,
    ) -> Result<ExprType> {
        let lhs_type = self.compile_expr(span.lhs, false)?;
        let pc = self.next_pc;
        self.emit(Instruction::Nop);

        let mut keep_nop = false;
        let rhs_type = self.compile_expr(span.rhs, false)?;
        let result = match (lhs_type, rhs_type) {
            (ExprType::Text, ExprType::Text) => ExprType::Text,
            (ExprType::Double, ExprType::Double) => ExprType::Double,
            (ExprType::Integer, ExprType::Integer) => ExprType::Integer,

            (ExprType::Double, ExprType::Integer) => {
                self.emit(Instruction::IntegerToDouble);
                ExprType::Double
            }

            (ExprType::Integer, ExprType::Double) => {
                self.instrs[pc] = Instruction::IntegerToDouble;
                keep_nop = true;
                ExprType::Double
            }

            (_, _) => {
                return Err(Error::new(
                    span.pos,
                    format!("Cannot {} {} and {}", op_name, lhs_type, rhs_type),
                ));
            }
        };

        if !keep_nop {
            self.instrs.remove(pc);
            self.next_pc -= 1;
        }

        self.emit(make_inst(span.pos));

        Ok(result)
    }

    /// Compiles the evaluation of an expression, appends its instructions to the
    /// compilation context, and returns the type of the compiled expression.
    ///
    /// `allow_varrefs` should be true for top-level expression compilations within
    /// function arguments.  In that specific case, we must leave bare variable
    /// references unevaluated because we don't know if the function wants to take
    /// the reference or the value.
    fn compile_expr(&mut self, expr: Expr, allow_varrefs: bool) -> Result<ExprType> {
        match expr {
            Expr::Boolean(span) => {
                self.emit(Instruction::Push(Value::Boolean(span.value), span.pos));
                Ok(ExprType::Boolean)
            }

            Expr::Double(span) => {
                self.emit(Instruction::Push(Value::Double(span.value), span.pos));
                Ok(ExprType::Double)
            }

            Expr::Integer(span) => {
                self.emit(Instruction::Push(Value::Integer(span.value), span.pos));
                Ok(ExprType::Integer)
            }

            Expr::Text(span) => {
                self.emit(Instruction::Push(Value::Text(span.value), span.pos));
                Ok(ExprType::Text)
            }

            Expr::Symbol(span) => {
                let key = SymbolKey::from(span.vref.name());
                if allow_varrefs {
                    let result = match self.symtable.get(&key) {
                        None => {
                            let vtype = if span.vref.ref_type() == VarType::Auto {
                                ExprType::Integer
                            } else {
                                span.vref.ref_type().into()
                            };
                            self.symtable.insert(key, SymbolPrototype::Variable(vtype));
                            vtype
                        }

                        Some(SymbolPrototype::Array(vtype))
                        | Some(SymbolPrototype::Variable(vtype)) => vtype,

                        Some(SymbolPrototype::Callable(ctype, is_argless)) => {
                            if !is_argless {
                                unreachable!();
                            }
                            match ctype.as_expr_type() {
                                Some(etype) => etype,
                                None => {
                                    return Err(Error::new(
                                        span.pos,
                                        format!(
                                            "{} is not an array nor a function",
                                            span.vref.name()
                                        ),
                                    ));
                                }
                            }
                        }
                    };
                    self.emit(Instruction::LoadRef(span.vref, span.pos));
                    Ok(result)
                } else {
                    let result = match self.symtable.get(&key) {
                        None => {
                            return Err(Error::new(
                                span.pos,
                                format!("Undefined variable {}", span.vref.name()),
                            ))
                        }
                        Some(SymbolPrototype::Variable(vtype)) => vtype,
                        Some(SymbolPrototype::Callable(ctype, is_argless)) if is_argless => {
                            // TODO(jmmv): This could emit a Call instruction instead of Load,
                            // avoiding the runtime check.
                            match ctype.as_expr_type() {
                                Some(etype) => etype,
                                None => {
                                    return Err(Error::new(
                                        span.pos,
                                        format!(
                                            "{} is not an array nor a function",
                                            span.vref.name()
                                        ),
                                    ));
                                }
                            }
                        }
                        Some(_) => {
                            return Err(Error::new(
                                span.pos,
                                format!("{} is not a variable", span.vref.name()),
                            ))
                        }
                    };
                    self.emit(Instruction::Load(span.vref, span.pos));
                    Ok(result)
                }
            }

            Expr::And(span) => self.compile_logical_binary_op(Instruction::And, *span, "AND"),

            Expr::Or(span) => self.compile_logical_binary_op(Instruction::Or, *span, "OR"),

            Expr::Xor(span) => self.compile_logical_binary_op(Instruction::Xor, *span, "XOR"),

            Expr::Not(span) => self.compile_not_op(*span),

            Expr::ShiftLeft(span) => {
                let result = self.compile_shift_binary_op(Instruction::ShiftLeft, *span, "<<")?;
                debug_assert_eq!(ExprType::Integer, result);
                Ok(result)
            }

            Expr::ShiftRight(span) => {
                let result = self.compile_shift_binary_op(Instruction::ShiftRight, *span, ">>")?;
                debug_assert_eq!(ExprType::Integer, result);
                Ok(result)
            }

            Expr::Equal(span) => {
                let result = self.compile_equality_binary_op(Instruction::Equal, *span, "=")?;
                debug_assert_eq!(ExprType::Boolean, result);
                Ok(result)
            }

            Expr::NotEqual(span) => {
                let result = self.compile_equality_binary_op(Instruction::NotEqual, *span, "<>")?;
                debug_assert_eq!(ExprType::Boolean, result);
                Ok(result)
            }

            Expr::Less(span) => {
                let result = self.compile_equality_binary_op(Instruction::Less, *span, "<")?;
                debug_assert_eq!(ExprType::Boolean, result);
                Ok(result)
            }

            Expr::LessEqual(span) => {
                let result =
                    self.compile_equality_binary_op(Instruction::LessEqual, *span, "<=")?;
                debug_assert_eq!(ExprType::Boolean, result);
                Ok(result)
            }

            Expr::Greater(span) => {
                let result = self.compile_equality_binary_op(Instruction::Greater, *span, ">")?;
                debug_assert_eq!(ExprType::Boolean, result);
                Ok(result)
            }

            Expr::GreaterEqual(span) => {
                let result =
                    self.compile_equality_binary_op(Instruction::GreaterEqual, *span, ">=")?;
                debug_assert_eq!(ExprType::Boolean, result);
                Ok(result)
            }

            Expr::Add(span) => {
                // TODO(jmmv): Need to emit different addition operations depending on the types
                // and remove the logic from the runtime.  Applies to all other operators as well.
                Ok(self.compile_arithmetic_binary_op(Instruction::Add, *span, "+")?)
            }

            Expr::Subtract(span) => {
                Ok(self.compile_arithmetic_binary_op(Instruction::Subtract, *span, "-")?)
            }

            Expr::Multiply(span) => {
                Ok(self.compile_arithmetic_binary_op(Instruction::Multiply, *span, "*")?)
            }

            Expr::Divide(span) => {
                Ok(self.compile_arithmetic_binary_op(Instruction::Divide, *span, "/")?)
            }

            Expr::Modulo(span) => {
                Ok(self.compile_arithmetic_binary_op(Instruction::Modulo, *span, "MOD")?)
            }

            Expr::Power(span) => {
                Ok(self.compile_arithmetic_binary_op(Instruction::Power, *span, "^")?)
            }

            Expr::Negate(span) => Ok(self.compile_neg_op(*span)?),

            Expr::Call(span) => {
                let nargs = span.args.len();
                for arg in span.args.into_iter().rev() {
                    self.compile_expr(arg, true)?;
                }

                let key = SymbolKey::from(span.fref.name());
                let result = match self.symtable.get(&key) {
                    Some(SymbolPrototype::Array(vtype)) => {
                        if !span.fref.accepts((vtype).into()) {
                            return Err(Error::new(
                                span.pos,
                                format!("Incompatible type annotation in {} reference", span.fref),
                            ));
                        }
                        self.emit(Instruction::ArrayLoad(span.fref, span.pos, nargs));
                        vtype
                    }

                    Some(SymbolPrototype::Callable(ctype, _is_argless)) => {
                        if !span.fref.accepts((ctype).into()) {
                            return Err(Error::new(
                                span.pos,
                                format!("Incompatible type annotation in {} reference", span.fref),
                            ));
                        }

                        let vtype = match ctype.as_expr_type() {
                            Some(vtype) => vtype,
                            None => {
                                return Err(Error::new(
                                    span.pos,
                                    format!("{} is not an array nor a function", span.fref.name()),
                                ));
                            }
                        };

                        self.emit(Instruction::FunctionCall(span.fref, span.pos, nargs));
                        vtype
                    }

                    Some(SymbolPrototype::Variable(_)) => {
                        return Err(Error::new(
                            span.pos,
                            format!("{} is not an array nor a function", span.fref.name()),
                        ));
                    }

                    None => {
                        return Err(Error::new(
                            span.pos,
                            format!("Unknown function or array {}", span.fref.name()),
                        ));
                    }
                };
                Ok(result)
            }
        }
    }

    /// Compiles one statement and appends its bytecode to the current compilation context.
    fn compile_one(&mut self, stmt: Statement) -> Result<()> {
        match stmt {
            Statement::ArrayAssignment(span) => {
                self.compile_expr(span.expr, false)?;
                let nargs = span.subscripts.len();
                for arg in span.subscripts.into_iter().rev() {
                    self.compile_expr(arg, false)?;
                }
                self.emit(Instruction::ArrayAssignment(span.vref, span.vref_pos, nargs));
            }

            Statement::Assignment(span) => {
                self.compile_assignment(span.vref, span.vref_pos, span.expr)?;
            }

            Statement::BuiltinCall(span) => {
                let key = SymbolKey::from(&span.name);
                match self.symtable.get(&key) {
                    Some(SymbolPrototype::Callable(ftype, _is_argless)) => {
                        if ftype != CallableType::Void {
                            return Err(Error::new(
                                span.name_pos,
                                format!("{} is not a command", span.name),
                            ));
                        }
                    }

                    Some(_) => {
                        return Err(Error::new(
                            span.name_pos,
                            format!("{} is not a command", span.name),
                        ));
                    }

                    None => {
                        return Err(Error::new(
                            span.name_pos,
                            format!("Unknown builtin {}", span.name),
                        ));
                    }
                }

                let mut nargs = 0;
                for argspan in span.args.into_iter().rev() {
                    if argspan.sep != ArgSep::End {
                        self.emit(Instruction::Push(
                            Value::Separator(argspan.sep),
                            argspan.sep_pos,
                        ));
                        nargs += 1;
                    }

                    match argspan.expr {
                        Some(expr) => {
                            self.compile_expr(expr, true)?;
                        }
                        None => {
                            self.emit(Instruction::Push(Value::Missing, argspan.sep_pos));
                        }
                    }
                    nargs += 1;
                }

                let bref = VarRef::new(span.name, VarType::Auto);
                self.emit(Instruction::BuiltinCall(bref, span.name_pos, nargs));
            }

            Statement::Data(mut span) => {
                self.data.append(&mut span.values);
            }

            Statement::Dim(span) => {
                self.compile_dim(span)?;
            }

            Statement::DimArray(span) => {
                let key = SymbolKey::from(&span.name);
                if self.symtable.contains_key(&key) {
                    return Err(Error::new(
                        span.name_pos,
                        format!("Cannot DIM already-defined symbol {}", span.name),
                    ));
                }

                let nargs = span.dimensions.len();
                for arg in span.dimensions.into_iter().rev() {
                    self.compile_expr(arg, false)?;
                }
                self.emit(Instruction::DimArray(DimArrayISpan {
                    name: key.clone(),
                    name_pos: span.name_pos,
                    dimensions: nargs,
                    subtype: span.subtype,
                    subtype_pos: span.subtype_pos,
                }));

                self.symtable.insert(key, SymbolPrototype::Array(span.subtype.into()));
            }

            Statement::Do(span) => {
                self.compile_do(span)?;
            }

            Statement::End(span) => match span.code {
                Some(expr) => {
                    self.compile_expr(expr, false)?;
                    self.emit(Instruction::End(true));
                }
                None => {
                    self.emit(Instruction::End(false));
                }
            },

            Statement::ExitDo(span) => {
                if self.exit_do_level.1 == 0 {
                    return Err(Error::new(span.pos, "EXIT DO outside of DO loop".to_owned()));
                }
                let exit_do_pc = self.emit(Instruction::Nop);
                self.fixups.insert(
                    exit_do_pc,
                    Fixup::from_exit_do(Compiler::do_label(self.exit_do_level), span),
                );
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
                self.emit(Instruction::Return(span.pos));
            }

            Statement::Select(span) => {
                self.compile_select(span)?;
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
    fn to_image(mut self) -> Result<(Image, SymbolsTable)> {
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
                FixupType::Gosub => self.instrs[pc] = Instruction::Call(JumpISpan { addr }),
                FixupType::Goto => self.instrs[pc] = Instruction::Jump(JumpISpan { addr }),
                FixupType::OnError => {
                    self.instrs[pc] = Instruction::SetErrorHandler(ErrorHandlerISpan::Jump(addr))
                }
            }
        }
        let image = Image { instrs: self.instrs, data: self.data };
        Ok((image, self.symtable))
    }
}

/// Compiles a collection of statements into an image ready for execution.
///
/// `symtable` is the symbols table as used by the compiler and should be prepopulated with any
/// callables that the compiled program should recognize.
fn compile_aux(stmts: Vec<Statement>, symtable: SymbolsTable) -> Result<(Image, SymbolsTable)> {
    let mut compiler = Compiler { symtable, ..Default::default() };
    compiler.compile_many(stmts)?;
    compiler.to_image()
}

/// Compiles a collection of statements into an image ready for execution.
///
/// `syms` is a reference to the execution symbols and is used to obtain the names of the callables
/// that exist in the virtual machine.
// TODO(jmmv): This is ugly.  Now that we have a symbols table in here, we should not _also_ have a
// Symbols object to maintain runtime state (or if we do, we shouldn't be getting it here).
pub fn compile(stmts: Vec<Statement>, syms: &Symbols) -> Result<Image> {
    compile_aux(stmts, SymbolsTable::from(syms)).map(|(image, _symtable)| image)
}

#[cfg(test)]
mod testutils {
    use super::*;
    use crate::parser;

    /// Builder pattern to prepare the compiler for testing purposes.
    #[derive(Default)]
    #[must_use]
    pub(crate) struct Tester {
        stmts: Vec<Statement>,
        symtable: SymbolsTable,
    }

    impl Tester {
        /// Inserts `name` into the symbols table with the type defined by `proto`.
        pub(crate) fn define<K: Into<SymbolKey>>(
            mut self,
            name: K,
            proto: SymbolPrototype,
        ) -> Self {
            self.symtable.insert(name.into(), proto);
            self
        }

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
                result: compile_aux(self.stmts, self.symtable),
                exp_error: None,
                ignore_instrs: false,
                exp_instrs: vec![],
                exp_data: vec![],
                exp_symtable: HashMap::default(),
            }
        }
    }

    /// Captures expectations about a compilation and validates them.
    #[must_use]
    pub(crate) struct Checker {
        result: Result<(Image, SymbolsTable)>,
        exp_error: Option<String>,
        ignore_instrs: bool,
        exp_instrs: Vec<Instruction>,
        exp_data: Vec<Option<Value>>,
        exp_symtable: HashMap<SymbolKey, SymbolPrototype>,
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

        /// Records an entry to be expected in the symbols table.
        pub(crate) fn expect_symtable(mut self, key: SymbolKey, proto: SymbolPrototype) -> Self {
            let previous = self.exp_symtable.insert(key, proto);
            assert!(previous.is_none());
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
            let (image, symtable) = self.result.unwrap();

            if self.ignore_instrs {
                assert!(
                    self.exp_instrs.is_empty(),
                    "Cannot ignore instructions if some are expected"
                );
            } else {
                assert_eq!(self.exp_instrs, image.instrs);
            }

            assert_eq!(self.exp_data, image.data);

            // TODO(jmmv): This should do an equality comparison to check all symbols, not just
            // those that tests have specified.  I did not do this when adding this check here
            // to avoid having to update all tests that didn't require this feature.
            for (key, exp_proto) in self.exp_symtable {
                match symtable.get(&key) {
                    Some(proto) => assert_eq!(exp_proto, proto),
                    None => panic!("Expected symbol {:?} not defined", key),
                }
            }
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
            .define("i", SymbolPrototype::Variable(ExprType::Integer))
            .parse("foo(3, 4 + i, i) = 5")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Integer(5), lc(1, 20)))
            .expect_instr(1, Instruction::Load(VarRef::new("i", VarType::Auto), lc(1, 15)))
            .expect_instr(2, Instruction::Push(Value::Integer(4), lc(1, 8)))
            .expect_instr(3, Instruction::Load(VarRef::new("i", VarType::Auto), lc(1, 12)))
            .expect_instr(4, Instruction::Add(lc(1, 10)))
            .expect_instr(5, Instruction::Push(Value::Integer(3), lc(1, 5)))
            .expect_instr(
                6,
                Instruction::ArrayAssignment(VarRef::new("foo", VarType::Auto), lc(1, 1), 3),
            )
            .check();
    }

    #[test]
    fn test_compile_assignment_literal() {
        Tester::default()
            .parse("foo = 5")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Integer(5), lc(1, 7)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("foo")))
            .check();
    }

    #[test]
    fn test_compile_assignment_varref_is_evaluated() {
        Tester::default()
            .define("i", SymbolPrototype::Variable(ExprType::Integer))
            .parse("foo = i")
            .compile()
            .expect_instr(0, Instruction::Load(VarRef::new("i", VarType::Auto), lc(1, 7)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("foo")))
            .check();
    }

    #[test]
    fn test_compile_assignment_new_var_auto_ref_expr_determines_type() {
        Tester::default()
            .parse("foo = 2.3")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Double(2.3), lc(1, 7)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("foo")))
            .expect_symtable(SymbolKey::from("foo"), SymbolPrototype::Variable(ExprType::Double))
            .check();
    }

    #[test]
    fn test_compile_assignment_new_var_explicit_ref_determines_type() {
        Tester::default()
            .parse("foo# = 2")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Integer(2), lc(1, 8)))
            .expect_instr(1, Instruction::IntegerToDouble)
            .expect_instr(2, Instruction::Assign(SymbolKey::from("foo")))
            .expect_symtable(SymbolKey::from("foo"), SymbolPrototype::Variable(ExprType::Double))
            .check();
    }

    #[test]
    fn test_compile_assignment_bad_types_existing_var() {
        Tester::default()
            .parse("foo# = TRUE")
            .compile()
            .expect_err("1:1: Cannot assign value of type BOOLEAN to variable of type DOUBLE")
            .check();
    }

    #[test]
    fn test_compile_assignment_bad_annotation_existing_var() {
        Tester::default()
            .define(SymbolKey::from("foo"), SymbolPrototype::Variable(ExprType::Text))
            .parse("foo# = \"hello\"")
            .compile()
            .expect_err("1:1: Incompatible types in foo# reference")
            .check();
    }

    #[test]
    fn test_compile_builtin_call_no_args() {
        Tester::default()
            .define("CMD", SymbolPrototype::Callable(CallableType::Void, false))
            .parse("CMD")
            .compile()
            .expect_instr(
                0,
                Instruction::BuiltinCall(VarRef::new("CMD", VarType::Auto), lc(1, 1), 0),
            )
            .check();
    }

    #[test]
    fn test_compile_builtin_call_separator_types() {
        Tester::default()
            .define("CMD", SymbolPrototype::Callable(CallableType::Void, false))
            .parse("CMD a;;b,c AS d")
            .compile()
            .expect_instr(0, Instruction::LoadRef(VarRef::new("d", VarType::Auto), lc(1, 15)))
            .expect_instr(1, Instruction::Push(Value::Separator(ArgSep::As), lc(1, 12)))
            .expect_instr(2, Instruction::LoadRef(VarRef::new("c", VarType::Auto), lc(1, 10)))
            .expect_instr(3, Instruction::Push(Value::Separator(ArgSep::Long), lc(1, 9)))
            .expect_instr(4, Instruction::LoadRef(VarRef::new("b", VarType::Auto), lc(1, 8)))
            .expect_instr(5, Instruction::Push(Value::Separator(ArgSep::Short), lc(1, 7)))
            .expect_instr(6, Instruction::Push(Value::Missing, lc(1, 7)))
            .expect_instr(7, Instruction::Push(Value::Separator(ArgSep::Short), lc(1, 6)))
            .expect_instr(8, Instruction::LoadRef(VarRef::new("a", VarType::Auto), lc(1, 5)))
            .expect_instr(
                9,
                Instruction::BuiltinCall(VarRef::new("CMD", VarType::Auto), lc(1, 1), 9),
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
    fn test_compile_dim_ok() {
        Tester::default()
            .parse("DIM var AS BOOLEAN")
            .compile()
            .expect_instr(0, Instruction::Dim(SymbolKey::from("var"), VarType::Boolean))
            .check();
        Tester::default()
            .parse("DIM var AS DOUBLE")
            .compile()
            .expect_instr(0, Instruction::Dim(SymbolKey::from("var"), VarType::Double))
            .check();
        Tester::default()
            .parse("DIM var AS INTEGER")
            .compile()
            .expect_instr(0, Instruction::Dim(SymbolKey::from("var"), VarType::Integer))
            .check();
        Tester::default()
            .parse("DIM var AS STRING")
            .compile()
            .expect_instr(0, Instruction::Dim(SymbolKey::from("var"), VarType::Text))
            .check();
    }

    #[test]
    fn test_compile_dim_case_insensitivity() {
        Tester::default()
            .parse("DIM foo: DIM Foo")
            .compile()
            .expect_err("1:14: Cannot DIM already-defined symbol Foo")
            .check();
    }

    #[test]
    fn test_compile_dim_name_overlap() {
        Tester::default()
            .define("SomeArray", SymbolPrototype::Array(ExprType::Integer))
            .parse("DIM somearray")
            .compile()
            .expect_err("1:5: Cannot DIM already-defined symbol somearray")
            .check();

        Tester::default()
            .define("Out", SymbolPrototype::Callable(CallableType::Integer, false))
            .parse("DIM OuT")
            .compile()
            .expect_err("1:5: Cannot DIM already-defined symbol OuT")
            .check();

        Tester::default()
            .define("SomeVar", SymbolPrototype::Variable(ExprType::Integer))
            .parse("DIM SOMEVAR")
            .compile()
            .expect_err("1:5: Cannot DIM already-defined symbol SOMEVAR")
            .check();
    }

    #[test]
    fn test_compile_dim_array_immediate() {
        Tester::default()
            .parse("DIM var(1) AS INTEGER")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Integer(1), lc(1, 9)))
            .expect_instr(
                1,
                Instruction::DimArray(DimArrayISpan {
                    name: SymbolKey::from("var"),
                    name_pos: lc(1, 5),
                    dimensions: 1,
                    subtype: VarType::Integer,
                    subtype_pos: lc(1, 15),
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_dim_array_exprs() {
        Tester::default()
            .define("i", SymbolPrototype::Variable(ExprType::Integer))
            .parse("DIM var(i, 3 + 4) AS INTEGER")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Integer(3), lc(1, 12)))
            .expect_instr(1, Instruction::Push(Value::Integer(4), lc(1, 16)))
            .expect_instr(2, Instruction::Add(lc(1, 14)))
            .expect_instr(3, Instruction::Load(VarRef::new("i", VarType::Auto), lc(1, 9)))
            .expect_instr(
                4,
                Instruction::DimArray(DimArrayISpan {
                    name: SymbolKey::from("var"),
                    name_pos: lc(1, 5),
                    dimensions: 2,
                    subtype: VarType::Integer,
                    subtype_pos: lc(1, 22),
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_do_infinite() {
        Tester::default()
            .define("FOO", SymbolPrototype::Callable(CallableType::Void, false))
            .parse("DO\nFOO\nLOOP")
            .compile()
            .expect_instr(
                0,
                Instruction::BuiltinCall(VarRef::new("FOO", VarType::Auto), lc(2, 1), 0),
            )
            .expect_instr(1, Instruction::Jump(JumpISpan { addr: 0 }))
            .check();
    }

    #[test]
    fn test_compile_do_pre_guard() {
        Tester::default()
            .define("FOO", SymbolPrototype::Callable(CallableType::Void, false))
            .parse("DO WHILE TRUE\nFOO\nLOOP")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Boolean(true), lc(1, 10)))
            .expect_instr(
                1,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 4,
                    error_msg: "DO requires a boolean condition",
                }),
            )
            .expect_instr(
                2,
                Instruction::BuiltinCall(VarRef::new("FOO", VarType::Auto), lc(2, 1), 0),
            )
            .expect_instr(3, Instruction::Jump(JumpISpan { addr: 0 }))
            .check();
    }

    #[test]
    fn test_compile_do_post_guard() {
        Tester::default()
            .define("FOO", SymbolPrototype::Callable(CallableType::Void, false))
            .parse("DO\nFOO\nLOOP WHILE TRUE")
            .compile()
            .expect_instr(
                0,
                Instruction::BuiltinCall(VarRef::new("FOO", VarType::Auto), lc(2, 1), 0),
            )
            .expect_instr(1, Instruction::Push(Value::Boolean(true), lc(3, 12)))
            .expect_instr(
                2,
                Instruction::JumpIfTrue(JumpIfBoolISpan {
                    addr: 0,
                    error_msg: "LOOP requires a boolean condition",
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_end_without_exit_code() {
        Tester::default().parse("END").compile().expect_instr(0, Instruction::End(false)).check();
    }

    #[test]
    fn test_compile_end_with_exit_code_expr() {
        Tester::default()
            .define("i", SymbolPrototype::Variable(ExprType::Integer))
            .parse("END 2 + i")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Integer(2), lc(1, 5)))
            .expect_instr(1, Instruction::Load(VarRef::new("i", VarType::Auto), lc(1, 9)))
            .expect_instr(2, Instruction::Add(lc(1, 7)))
            .expect_instr(3, Instruction::End(true))
            .check();
    }

    #[test]
    fn test_compile_end_with_exit_code_varref() {
        Tester::default()
            .define("i", SymbolPrototype::Variable(ExprType::Integer))
            .parse("END i")
            .compile()
            .expect_instr(0, Instruction::Load(VarRef::new("i", VarType::Auto), lc(1, 5)))
            .expect_instr(1, Instruction::End(true))
            .check();
    }

    #[test]
    fn test_compile_exit_do_infinite_simple() {
        Tester::default()
            .parse("DO\nEXIT DO\nLOOP")
            .compile()
            .expect_instr(0, Instruction::Jump(JumpISpan { addr: 2 }))
            .expect_instr(1, Instruction::Jump(JumpISpan { addr: 0 }))
            .check();
    }

    #[test]
    fn test_compile_exit_do_pre_simple() {
        Tester::default()
            .parse("DO WHILE TRUE\nEXIT DO\nLOOP")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Boolean(true), lc(1, 10)))
            .expect_instr(
                1,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 4,
                    error_msg: "DO requires a boolean condition",
                }),
            )
            .expect_instr(2, Instruction::Jump(JumpISpan { addr: 4 }))
            .expect_instr(3, Instruction::Jump(JumpISpan { addr: 0 }))
            .check();
    }

    #[test]
    fn test_compile_exit_do_nested() {
        Tester::default()
            .parse("DO WHILE TRUE\nEXIT DO\nDO UNTIL FALSE\nEXIT DO\nLOOP\nLOOP")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Boolean(true), lc(1, 10)))
            .expect_instr(
                1,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 8,
                    error_msg: "DO requires a boolean condition",
                }),
            )
            .expect_instr(2, Instruction::Jump(JumpISpan { addr: 8 }))
            .expect_instr(3, Instruction::Push(Value::Boolean(false), lc(3, 10)))
            .expect_instr(
                4,
                Instruction::JumpIfTrue(JumpIfBoolISpan {
                    addr: 7,
                    error_msg: "DO requires a boolean condition",
                }),
            )
            .expect_instr(5, Instruction::Jump(JumpISpan { addr: 7 }))
            .expect_instr(6, Instruction::Jump(JumpISpan { addr: 3 }))
            .expect_instr(7, Instruction::Jump(JumpISpan { addr: 0 }))
            .check();
    }

    #[test]
    fn test_compile_exit_do_sequential() {
        Tester::default()
            .parse("DO WHILE TRUE\nEXIT DO\nLOOP\nDO WHILE TRUE\nEXIT DO\nLOOP")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Boolean(true), lc(1, 10)))
            .expect_instr(
                1,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 4,
                    error_msg: "DO requires a boolean condition",
                }),
            )
            .expect_instr(2, Instruction::Jump(JumpISpan { addr: 4 }))
            .expect_instr(3, Instruction::Jump(JumpISpan { addr: 0 }))
            .expect_instr(4, Instruction::Push(Value::Boolean(true), lc(4, 10)))
            .expect_instr(
                5,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 8,
                    error_msg: "DO requires a boolean condition",
                }),
            )
            .expect_instr(6, Instruction::Jump(JumpISpan { addr: 8 }))
            .expect_instr(7, Instruction::Jump(JumpISpan { addr: 4 }))
            .check();
    }

    #[test]
    fn test_compile_exit_do_from_nested_while() {
        Tester::default()
            .parse("DO WHILE TRUE\nEXIT DO\nWHILE FALSE\nEXIT DO\nWEND\nLOOP")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Boolean(true), lc(1, 10)))
            .expect_instr(
                1,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 8,
                    error_msg: "DO requires a boolean condition",
                }),
            )
            .expect_instr(2, Instruction::Jump(JumpISpan { addr: 8 }))
            .expect_instr(3, Instruction::Push(Value::Boolean(false), lc(3, 7)))
            .expect_instr(
                4,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 7,
                    error_msg: "WHILE requires a boolean condition",
                }),
            )
            .expect_instr(5, Instruction::Jump(JumpISpan { addr: 8 }))
            .expect_instr(6, Instruction::Jump(JumpISpan { addr: 3 }))
            .expect_instr(7, Instruction::Jump(JumpISpan { addr: 0 }))
            .check();
    }

    #[test]
    fn test_compile_exit_do_outside_of_loop() {
        Tester::default()
            .parse("EXIT DO")
            .compile()
            .expect_err("1:1: EXIT DO outside of DO loop")
            .check();

        Tester::default()
            .parse("WHILE TRUE: EXIT DO: WEND")
            .compile()
            .expect_err("1:13: EXIT DO outside of DO loop")
            .check();
    }

    #[test]
    fn test_compile_expr_literals() {
        Tester::default()
            .parse("b = TRUE\nd = 2.3\ni = 5\nt = \"foo\"")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Boolean(true), lc(1, 5)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("b")))
            .expect_instr(2, Instruction::Push(Value::Double(2.3), lc(2, 5)))
            .expect_instr(3, Instruction::Assign(SymbolKey::from("d")))
            .expect_instr(4, Instruction::Push(Value::Integer(5), lc(3, 5)))
            .expect_instr(5, Instruction::Assign(SymbolKey::from("i")))
            .expect_instr(6, Instruction::Push(Value::Text("foo".to_owned()), lc(4, 5)))
            .expect_instr(7, Instruction::Assign(SymbolKey::from("t")))
            .check();
    }

    #[test]
    fn test_compile_expr_varrefs_are_evaluated() {
        Tester::default()
            .define("j", SymbolPrototype::Variable(ExprType::Integer))
            .parse("i = j")
            .compile()
            .expect_instr(0, Instruction::Load(VarRef::new("j", VarType::Auto), lc(1, 5)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("i")))
            .check();
    }

    #[test]
    fn test_compile_expr_logical_ops() {
        Tester::default()
            .define("x", SymbolPrototype::Variable(ExprType::Boolean))
            .define("y", SymbolPrototype::Variable(ExprType::Boolean))
            .define("z", SymbolPrototype::Variable(ExprType::Boolean))
            .parse("b = true OR x AND y XOR NOT z")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Boolean(true), lc(1, 5)))
            .expect_instr(1, Instruction::Load(VarRef::new("x", VarType::Auto), lc(1, 13)))
            .expect_instr(2, Instruction::Or(lc(1, 10)))
            .expect_instr(3, Instruction::Load(VarRef::new("y", VarType::Auto), lc(1, 19)))
            .expect_instr(4, Instruction::And(lc(1, 15)))
            .expect_instr(5, Instruction::Load(VarRef::new("z", VarType::Auto), lc(1, 29)))
            .expect_instr(6, Instruction::Not(lc(1, 25)))
            .expect_instr(7, Instruction::Xor(lc(1, 21)))
            .expect_instr(8, Instruction::Assign(SymbolKey::from("b")))
            .check();
    }

    #[test]
    fn test_compile_expr_bitwise_ops() {
        Tester::default()
            .define("a", SymbolPrototype::Variable(ExprType::Integer))
            .define("b", SymbolPrototype::Variable(ExprType::Integer))
            .parse("i = a >> 5 << b")
            .compile()
            .expect_instr(0, Instruction::Load(VarRef::new("a", VarType::Auto), lc(1, 5)))
            .expect_instr(1, Instruction::Push(Value::Integer(5), lc(1, 10)))
            .expect_instr(2, Instruction::ShiftRight(lc(1, 7)))
            .expect_instr(3, Instruction::Load(VarRef::new("b", VarType::Auto), lc(1, 15)))
            .expect_instr(4, Instruction::ShiftLeft(lc(1, 12)))
            .expect_instr(5, Instruction::Assign(SymbolKey::from("i")))
            .check();
    }

    #[test]
    fn test_compile_expr_relational_ops() {
        fn test_op<F: Fn(LineCol) -> Instruction>(make_inst: F, op_name: &str) {
            Tester::default()
                .define("a", SymbolPrototype::Variable(ExprType::Integer))
                .parse(&format!("b = a {} 10", op_name))
                .compile()
                .expect_instr(0, Instruction::Load(VarRef::new("a", VarType::Auto), lc(1, 5)))
                .expect_instr(1, Instruction::Push(Value::Integer(10), lc(1, 8 + op_name.len())))
                .expect_instr(2, make_inst(lc(1, 7)))
                .expect_instr(3, Instruction::Assign(SymbolKey::from("b")))
                .check();
        }

        test_op(Instruction::Equal, "=");
        test_op(Instruction::NotEqual, "<>");
        test_op(Instruction::Less, "<");
        test_op(Instruction::LessEqual, "<=");
        test_op(Instruction::Greater, ">");
        test_op(Instruction::GreaterEqual, ">=");
    }

    #[test]
    fn test_compile_expr_arithmetic_ops() {
        Tester::default()
            .define("a", SymbolPrototype::Variable(ExprType::Integer))
            .parse("i = a + 10 - 20 * 30 / 40 MOD 50 ^ (-60)")
            .compile()
            .expect_instr(0, Instruction::Load(VarRef::new("a", VarType::Auto), lc(1, 5)))
            .expect_instr(1, Instruction::Push(Value::Integer(10), lc(1, 9)))
            .expect_instr(2, Instruction::Add(lc(1, 7)))
            .expect_instr(3, Instruction::Push(Value::Integer(20), lc(1, 14)))
            .expect_instr(4, Instruction::Push(Value::Integer(30), lc(1, 19)))
            .expect_instr(5, Instruction::Multiply(lc(1, 17)))
            .expect_instr(6, Instruction::Push(Value::Integer(40), lc(1, 24)))
            .expect_instr(7, Instruction::Divide(lc(1, 22)))
            .expect_instr(8, Instruction::Push(Value::Integer(50), lc(1, 31)))
            .expect_instr(9, Instruction::Push(Value::Integer(60), lc(1, 38)))
            .expect_instr(10, Instruction::Negate(lc(1, 37)))
            .expect_instr(11, Instruction::Power(lc(1, 34)))
            .expect_instr(12, Instruction::Modulo(lc(1, 27)))
            .expect_instr(13, Instruction::Subtract(lc(1, 12)))
            .expect_instr(14, Instruction::Assign(SymbolKey::from("i")))
            .check();
    }

    #[test]
    fn test_compile_expr_array_ref() {
        Tester::default()
            .define("FOO", SymbolPrototype::Array(ExprType::Integer))
            .define("j", SymbolPrototype::Variable(ExprType::Text))
            .define("k", SymbolPrototype::Variable(ExprType::Integer))
            .parse("i = FOO(3, j, k + 1)")
            .compile()
            .expect_instr(0, Instruction::Load(VarRef::new("k", VarType::Auto), lc(1, 15)))
            .expect_instr(1, Instruction::Push(Value::Integer(1), lc(1, 19)))
            .expect_instr(2, Instruction::Add(lc(1, 17)))
            .expect_instr(3, Instruction::LoadRef(VarRef::new("j", VarType::Auto), lc(1, 12)))
            .expect_instr(4, Instruction::Push(Value::Integer(3), lc(1, 9)))
            .expect_instr(5, Instruction::ArrayLoad(VarRef::new("FOO", VarType::Auto), lc(1, 5), 3))
            .expect_instr(6, Instruction::Assign(SymbolKey::from("i")))
            .check();
    }

    #[test]
    fn test_compile_expr_function_call() {
        Tester::default()
            .define("FOO", SymbolPrototype::Callable(CallableType::Integer, false))
            .define("j", SymbolPrototype::Variable(ExprType::Text))
            .define("k", SymbolPrototype::Variable(ExprType::Double))
            .parse("i = FOO(3, j, k + 1)")
            .compile()
            .expect_instr(0, Instruction::Load(VarRef::new("k", VarType::Auto), lc(1, 15)))
            .expect_instr(1, Instruction::Push(Value::Integer(1), lc(1, 19)))
            .expect_instr(2, Instruction::IntegerToDouble)
            .expect_instr(3, Instruction::Add(lc(1, 17)))
            .expect_instr(4, Instruction::LoadRef(VarRef::new("j", VarType::Auto), lc(1, 12)))
            .expect_instr(5, Instruction::Push(Value::Integer(3), lc(1, 9)))
            .expect_instr(
                6,
                Instruction::FunctionCall(VarRef::new("FOO", VarType::Auto), lc(1, 5), 3),
            )
            .expect_instr(7, Instruction::Assign(SymbolKey::from("i")))
            .check();
    }

    #[test]
    fn test_compile_expr_array_or_function_not_defined() {
        Tester::default()
            .define("j", SymbolPrototype::Variable(ExprType::Integer))
            .define("k", SymbolPrototype::Variable(ExprType::Integer))
            .parse("i = FOO(3, j, k + 1)")
            .compile()
            .expect_err("1:5: Unknown function or array FOO")
            .check();
    }

    #[test]
    fn test_compile_expr_array_or_function_references_variable() {
        Tester::default()
            .parse("i = 3: j = i()")
            .compile()
            .expect_err("1:12: i is not an array nor a function")
            .check();
    }

    #[test]
    fn test_compile_for_simple_literals() {
        Tester::default()
            .parse("FOR iter = 1 TO 5: a = FALSE: NEXT")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Integer(1), lc(1, 12)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("iter")))
            .expect_instr(2, Instruction::Load(VarRef::new("iter", VarType::Auto), lc(1, 5)))
            .expect_instr(3, Instruction::Push(Value::Integer(5), lc(1, 17)))
            .expect_instr(4, Instruction::LessEqual(lc(1, 14)))
            .expect_instr(
                5,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 13,
                    error_msg: "FOR supports numeric iteration only",
                }),
            )
            .expect_instr(6, Instruction::Push(Value::Boolean(false), lc(1, 24)))
            .expect_instr(7, Instruction::Assign(SymbolKey::from("a")))
            .expect_instr(8, Instruction::Load(VarRef::new("iter", VarType::Auto), lc(1, 5)))
            .expect_instr(9, Instruction::Push(Value::Integer(1), lc(1, 18)))
            .expect_instr(10, Instruction::Add(lc(1, 14)))
            .expect_instr(11, Instruction::Assign(SymbolKey::from("iter")))
            .expect_instr(12, Instruction::Jump(JumpISpan { addr: 2 }))
            .check();
    }

    #[test]
    fn test_compile_for_simple_varrefs_are_evaluated() {
        Tester::default()
            .define("i", SymbolPrototype::Variable(ExprType::Integer))
            .define("j", SymbolPrototype::Variable(ExprType::Integer))
            .parse("FOR iter = i TO j: a = FALSE: NEXT")
            .compile()
            .expect_instr(0, Instruction::Load(VarRef::new("i", VarType::Auto), lc(1, 12)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("iter")))
            .expect_instr(2, Instruction::Load(VarRef::new("iter", VarType::Auto), lc(1, 5)))
            .expect_instr(3, Instruction::Load(VarRef::new("j", VarType::Auto), lc(1, 17)))
            .expect_instr(4, Instruction::LessEqual(lc(1, 14)))
            .expect_instr(
                5,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 13,
                    error_msg: "FOR supports numeric iteration only",
                }),
            )
            .expect_instr(6, Instruction::Push(Value::Boolean(false), lc(1, 24)))
            .expect_instr(7, Instruction::Assign(SymbolKey::from("a")))
            .expect_instr(8, Instruction::Load(VarRef::new("iter", VarType::Auto), lc(1, 5)))
            .expect_instr(9, Instruction::Push(Value::Integer(1), lc(1, 18)))
            .expect_instr(10, Instruction::Add(lc(1, 14)))
            .expect_instr(11, Instruction::Assign(SymbolKey::from("iter")))
            .expect_instr(12, Instruction::Jump(JumpISpan { addr: 2 }))
            .check();
    }

    #[test]
    fn test_compile_for_expressions() {
        Tester::default()
            .define("i", SymbolPrototype::Variable(ExprType::Integer))
            .define("j", SymbolPrototype::Variable(ExprType::Integer))
            .parse("FOR iter = (i + 1) TO (2 + j): a = FALSE: NEXT")
            .compile()
            .expect_instr(0, Instruction::Load(VarRef::new("i", VarType::Auto), lc(1, 13)))
            .expect_instr(1, Instruction::Push(Value::Integer(1), lc(1, 17)))
            .expect_instr(2, Instruction::Add(lc(1, 15)))
            .expect_instr(3, Instruction::Assign(SymbolKey::from("iter")))
            .expect_instr(4, Instruction::Load(VarRef::new("iter", VarType::Auto), lc(1, 5)))
            .expect_instr(5, Instruction::Push(Value::Integer(2), lc(1, 24)))
            .expect_instr(6, Instruction::Load(VarRef::new("j", VarType::Auto), lc(1, 28)))
            .expect_instr(7, Instruction::Add(lc(1, 26)))
            .expect_instr(8, Instruction::LessEqual(lc(1, 20)))
            .expect_instr(
                9,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 17,
                    error_msg: "FOR supports numeric iteration only",
                }),
            )
            .expect_instr(10, Instruction::Push(Value::Boolean(false), lc(1, 36)))
            .expect_instr(11, Instruction::Assign(SymbolKey::from("a")))
            .expect_instr(12, Instruction::Load(VarRef::new("iter", VarType::Auto), lc(1, 5)))
            .expect_instr(13, Instruction::Push(Value::Integer(1), lc(1, 30)))
            .expect_instr(14, Instruction::Add(lc(1, 20)))
            .expect_instr(15, Instruction::Assign(SymbolKey::from("iter")))
            .expect_instr(16, Instruction::Jump(JumpISpan { addr: 4 }))
            .check();
    }

    #[test]
    fn test_compile_for_double_auto_iterator() {
        Tester::default()
            .parse("FOR iter = 0 TO 2 STEP 0.1\nNEXT")
            .compile()
            .expect_instr(
                0,
                Instruction::JumpIfDefined(JumpIfDefinedISpan { var: "iter".to_owned(), addr: 2 }),
            )
            .expect_instr(1, Instruction::Dim(SymbolKey::from("iter"), VarType::Double))
            .expect_instr(2, Instruction::Push(Value::Integer(0), lc(1, 12)))
            .expect_instr(3, Instruction::IntegerToDouble)
            .expect_instr(4, Instruction::Assign(SymbolKey::from("iter")))
            .expect_instr(5, Instruction::Load(VarRef::new("iter", VarType::Auto), lc(1, 5)))
            .expect_instr(6, Instruction::Push(Value::Integer(2), lc(1, 17)))
            .expect_instr(7, Instruction::IntegerToDouble)
            .expect_instr(8, Instruction::LessEqual(lc(1, 14)))
            .expect_instr(
                9,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 15,
                    error_msg: "FOR supports numeric iteration only",
                }),
            )
            .expect_instr(10, Instruction::Load(VarRef::new("iter", VarType::Auto), lc(1, 5)))
            .expect_instr(11, Instruction::Push(Value::Double(0.1), lc(1, 24)))
            .expect_instr(12, Instruction::Add(lc(1, 14)))
            .expect_instr(13, Instruction::Assign(SymbolKey::from("iter")))
            .expect_instr(14, Instruction::Jump(JumpISpan { addr: 5 }))
            .check();
    }

    #[test]
    fn test_compile_goto() {
        Tester::default()
            .parse("@first GOTO @second")
            .parse("@second: GOTO @first")
            .compile()
            .expect_instr(0, Instruction::Jump(JumpISpan { addr: 1 }))
            .expect_instr(1, Instruction::Jump(JumpISpan { addr: 0 }))
            .check();
    }

    #[test]
    fn test_compile_gosub_and_return() {
        Tester::default()
            .define("FOO", SymbolPrototype::Callable(CallableType::Void, false))
            .parse("@sub\nFOO\nRETURN\nGOSUB @sub")
            .compile()
            .expect_instr(
                0,
                Instruction::BuiltinCall(VarRef::new("FOO", VarType::Auto), lc(2, 1), 0),
            )
            .expect_instr(1, Instruction::Return(lc(3, 1)))
            .expect_instr(2, Instruction::Call(JumpISpan { addr: 0 }))
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
            .define("FOO", SymbolPrototype::Callable(CallableType::Void, false))
            .parse("IF FALSE THEN: FOO: END IF")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Boolean(false), lc(1, 4)))
            .expect_instr(
                1,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 3,
                    error_msg: "IF/ELSEIF require a boolean condition",
                }),
            )
            .expect_instr(
                2,
                Instruction::BuiltinCall(VarRef::new("FOO", VarType::Auto), lc(1, 16), 0),
            )
            .check();
    }

    #[test]
    fn test_compile_if_many_branches() {
        Tester::default()
            .define("FOO", SymbolPrototype::Callable(CallableType::Void, false))
            .define("BAR", SymbolPrototype::Callable(CallableType::Void, false))
            .define("BAZ", SymbolPrototype::Callable(CallableType::Void, false))
            .parse("IF FALSE THEN\nFOO\nELSEIF TRUE THEN\nBAR\nELSE\nBAZ\nEND IF")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Boolean(false), lc(1, 4)))
            .expect_instr(
                1,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 4,
                    error_msg: "IF/ELSEIF require a boolean condition",
                }),
            )
            .expect_instr(
                2,
                Instruction::BuiltinCall(VarRef::new("FOO", VarType::Auto), lc(2, 1), 0),
            )
            .expect_instr(3, Instruction::Jump(JumpISpan { addr: 11 }))
            .expect_instr(4, Instruction::Push(Value::Boolean(true), lc(3, 8)))
            .expect_instr(
                5,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 8,
                    error_msg: "IF/ELSEIF require a boolean condition",
                }),
            )
            .expect_instr(
                6,
                Instruction::BuiltinCall(VarRef::new("BAR", VarType::Auto), lc(4, 1), 0),
            )
            .expect_instr(7, Instruction::Jump(JumpISpan { addr: 11 }))
            .expect_instr(8, Instruction::Push(Value::Boolean(true), lc(5, 1)))
            .expect_instr(
                9,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 11,
                    error_msg: "IF/ELSEIF require a boolean condition",
                }),
            )
            .expect_instr(
                10,
                Instruction::BuiltinCall(VarRef::new("BAZ", VarType::Auto), lc(6, 1), 0),
            )
            .check();
    }

    #[test]
    fn test_compile_on_error_reset() {
        Tester::default()
            .parse("ON ERROR GOTO 0")
            .compile()
            .expect_instr(0, Instruction::SetErrorHandler(ErrorHandlerISpan::None))
            .check();
    }

    #[test]
    fn test_compile_on_error_goto_label() {
        Tester::default()
            .parse("ON ERROR GOTO @foo\n\n\n@foo")
            .compile()
            .expect_instr(0, Instruction::SetErrorHandler(ErrorHandlerISpan::Jump(1)))
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
            .expect_instr(0, Instruction::SetErrorHandler(ErrorHandlerISpan::ResumeNext))
            .check();
    }

    /// Tests that parsing one or more `guards` as supplied after `CASE` yields the expected
    /// expression in `exp_expr`.
    ///
    /// `exp_expr` must assume that its position starts at `(2, 6)`.
    fn do_compile_case_guard_test(guards: &str, exp_expr_instrs: Vec<Instruction>) {
        let mut t = Tester::default()
            .define("FOO", SymbolPrototype::Callable(CallableType::Void, false))
            .parse(&format!("SELECT CASE 5\nCASE {}\nFOO\nEND SELECT", guards))
            .compile()
            .expect_instr(0, Instruction::Push(Value::Integer(5), lc(1, 13)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("0select1")));
        let mut n = 2;
        for instr in exp_expr_instrs {
            t = t.expect_instr(n, instr);
            n += 1;
        }
        t.expect_instr(
            n,
            Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                addr: n + 2,
                error_msg: "SELECT requires a boolean condition",
            }),
        )
        .expect_instr(
            n + 1,
            Instruction::BuiltinCall(VarRef::new("FOO", VarType::Auto), lc(3, 1), 0),
        )
        .expect_instr(
            n + 2,
            Instruction::Unset(UnsetISpan { name: "0select1".to_owned(), pos: lc(4, 1) }),
        )
        .check();
    }

    #[test]
    fn test_compile_case_guards_equals() {
        do_compile_case_guard_test(
            "1 + 2",
            vec![
                Instruction::Load(VarRef::new("0select1", VarType::Auto), lc(2, 6)),
                Instruction::Push(Value::Integer(1), lc(2, 6)),
                Instruction::Push(Value::Integer(2), lc(2, 10)),
                Instruction::Add(lc(2, 8)),
                Instruction::Equal(lc(2, 6)),
            ],
        );
    }

    #[test]
    fn test_compile_case_guards_is() {
        do_compile_case_guard_test(
            "IS = 9 + 8",
            vec![
                Instruction::Load(VarRef::new("0select1", VarType::Auto), lc(2, 11)),
                Instruction::Push(Value::Integer(9), lc(2, 11)),
                Instruction::Push(Value::Integer(8), lc(2, 15)),
                Instruction::Add(lc(2, 13)),
                Instruction::Equal(lc(2, 11)),
            ],
        );

        do_compile_case_guard_test(
            "IS <> 9",
            vec![
                Instruction::Load(VarRef::new("0select1", VarType::Auto), lc(2, 12)),
                Instruction::Push(Value::Integer(9), lc(2, 12)),
                Instruction::NotEqual(lc(2, 12)),
            ],
        );

        do_compile_case_guard_test(
            "IS < 9",
            vec![
                Instruction::Load(VarRef::new("0select1", VarType::Auto), lc(2, 11)),
                Instruction::Push(Value::Integer(9), lc(2, 11)),
                Instruction::Less(lc(2, 11)),
            ],
        );

        do_compile_case_guard_test(
            "IS <= 9",
            vec![
                Instruction::Load(VarRef::new("0select1", VarType::Auto), lc(2, 12)),
                Instruction::Push(Value::Integer(9), lc(2, 12)),
                Instruction::LessEqual(lc(2, 12)),
            ],
        );

        do_compile_case_guard_test(
            "IS > 9",
            vec![
                Instruction::Load(VarRef::new("0select1", VarType::Auto), lc(2, 11)),
                Instruction::Push(Value::Integer(9), lc(2, 11)),
                Instruction::Greater(lc(2, 11)),
            ],
        );

        do_compile_case_guard_test(
            "IS >= 9",
            vec![
                Instruction::Load(VarRef::new("0select1", VarType::Auto), lc(2, 12)),
                Instruction::Push(Value::Integer(9), lc(2, 12)),
                Instruction::GreaterEqual(lc(2, 12)),
            ],
        );
    }

    #[test]
    fn test_compile_case_guards_to() {
        do_compile_case_guard_test(
            "1 TO 2",
            vec![
                Instruction::Load(VarRef::new("0select1", VarType::Auto), lc(2, 6)),
                Instruction::Push(Value::Integer(1), lc(2, 6)),
                Instruction::GreaterEqual(lc(2, 6)),
                Instruction::Load(VarRef::new("0select1", VarType::Auto), lc(2, 6)),
                Instruction::Push(Value::Integer(2), lc(2, 11)),
                Instruction::LessEqual(lc(2, 11)),
                Instruction::And(lc(2, 6)),
            ],
        );
    }

    #[test]
    fn test_compile_case_guards_many() {
        do_compile_case_guard_test(
            "IS <> 9, 8",
            vec![
                Instruction::Load(VarRef::new("0select1", VarType::Auto), lc(2, 12)),
                Instruction::Push(Value::Integer(9), lc(2, 12)),
                Instruction::NotEqual(lc(2, 12)),
                Instruction::Load(VarRef::new("0select1", VarType::Auto), lc(2, 15)),
                Instruction::Push(Value::Integer(8), lc(2, 15)),
                Instruction::Equal(lc(2, 15)),
                Instruction::Or(lc(2, 12)),
            ],
        );
    }

    #[test]
    fn test_compile_select_no_cases() {
        Tester::default()
            .parse("SELECT CASE 5 + 3: END SELECT")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Integer(5), lc(1, 13)))
            .expect_instr(1, Instruction::Push(Value::Integer(3), lc(1, 17)))
            .expect_instr(2, Instruction::Add(lc(1, 15)))
            .expect_instr(3, Instruction::Assign(SymbolKey::from("0select1")))
            .expect_instr(
                4,
                Instruction::Unset(UnsetISpan { name: "0select1".to_owned(), pos: lc(1, 20) }),
            )
            .check();
    }

    #[test]
    fn test_compile_select_one_case() {
        Tester::default()
            .define("FOO", SymbolPrototype::Callable(CallableType::Void, false))
            .parse("SELECT CASE 5\nCASE 7\nFOO\nEND SELECT")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Integer(5), lc(1, 13)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("0select1")))
            .expect_instr(2, Instruction::Load(VarRef::new("0select1", VarType::Auto), lc(2, 6)))
            .expect_instr(3, Instruction::Push(Value::Integer(7), lc(2, 6)))
            .expect_instr(4, Instruction::Equal(lc(2, 6)))
            .expect_instr(
                5,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 7,
                    error_msg: "SELECT requires a boolean condition",
                }),
            )
            .expect_instr(
                6,
                Instruction::BuiltinCall(VarRef::new("FOO", VarType::Auto), lc(3, 1), 0),
            )
            .expect_instr(
                7,
                Instruction::Unset(UnsetISpan { name: "0select1".to_owned(), pos: lc(4, 1) }),
            )
            .check();
    }

    #[test]
    fn test_compile_select_one_case_varref_is_evaluated() {
        Tester::default()
            .define("i", SymbolPrototype::Variable(ExprType::Integer))
            .parse("SELECT CASE i: END SELECT")
            .compile()
            .expect_instr(0, Instruction::Load(VarRef::new("i", VarType::Auto), lc(1, 13)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("0select1")))
            .expect_instr(
                2,
                Instruction::Unset(UnsetISpan { name: "0select1".to_owned(), pos: lc(1, 16) }),
            )
            .check();
    }

    #[test]
    fn test_compile_select_only_case_else() {
        Tester::default()
            .define("FOO", SymbolPrototype::Callable(CallableType::Void, false))
            .parse("SELECT CASE 5\nCASE ELSE\nFOO\nEND SELECT")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Integer(5), lc(1, 13)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("0select1")))
            .expect_instr(
                2,
                Instruction::BuiltinCall(VarRef::new("FOO", VarType::Auto), lc(3, 1), 0),
            )
            .expect_instr(
                3,
                Instruction::Unset(UnsetISpan { name: "0select1".to_owned(), pos: lc(4, 1) }),
            )
            .check();
    }

    #[test]
    fn test_compile_select_many_cases_without_else() {
        Tester::default()
            .define("FOO", SymbolPrototype::Callable(CallableType::Void, false))
            .define("BAR", SymbolPrototype::Callable(CallableType::Void, false))
            .parse("SELECT CASE 5\nCASE 7\nFOO\nCASE IS <> 8\nBAR\nEND SELECT")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Integer(5), lc(1, 13)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("0select1")))
            .expect_instr(2, Instruction::Load(VarRef::new("0select1", VarType::Auto), lc(2, 6)))
            .expect_instr(3, Instruction::Push(Value::Integer(7), lc(2, 6)))
            .expect_instr(4, Instruction::Equal(lc(2, 6)))
            .expect_instr(
                5,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 8,
                    error_msg: "SELECT requires a boolean condition",
                }),
            )
            .expect_instr(
                6,
                Instruction::BuiltinCall(VarRef::new("FOO", VarType::Auto), lc(3, 1), 0),
            )
            .expect_instr(7, Instruction::Jump(JumpISpan { addr: 13 }))
            .expect_instr(8, Instruction::Load(VarRef::new("0select1", VarType::Auto), lc(4, 12)))
            .expect_instr(9, Instruction::Push(Value::Integer(8), lc(4, 12)))
            .expect_instr(10, Instruction::NotEqual(lc(4, 12)))
            .expect_instr(
                11,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 13,
                    error_msg: "SELECT requires a boolean condition",
                }),
            )
            .expect_instr(
                12,
                Instruction::BuiltinCall(VarRef::new("BAR", VarType::Auto), lc(5, 1), 0),
            )
            .expect_instr(
                13,
                Instruction::Unset(UnsetISpan { name: "0select1".to_owned(), pos: lc(6, 1) }),
            )
            .check();
    }

    #[test]
    fn test_compile_select_many_cases_with_else() {
        Tester::default()
            .define("FOO", SymbolPrototype::Callable(CallableType::Void, false))
            .define("BAR", SymbolPrototype::Callable(CallableType::Void, false))
            .parse("SELECT CASE 5\nCASE 7\nFOO\nCASE ELSE\nBAR\nEND SELECT")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Integer(5), lc(1, 13)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("0select1")))
            .expect_instr(2, Instruction::Load(VarRef::new("0select1", VarType::Auto), lc(2, 6)))
            .expect_instr(3, Instruction::Push(Value::Integer(7), lc(2, 6)))
            .expect_instr(4, Instruction::Equal(lc(2, 6)))
            .expect_instr(
                5,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 8,
                    error_msg: "SELECT requires a boolean condition",
                }),
            )
            .expect_instr(
                6,
                Instruction::BuiltinCall(VarRef::new("FOO", VarType::Auto), lc(3, 1), 0),
            )
            .expect_instr(7, Instruction::Jump(JumpISpan { addr: 9 }))
            .expect_instr(
                8,
                Instruction::BuiltinCall(VarRef::new("BAR", VarType::Auto), lc(5, 1), 0),
            )
            .expect_instr(
                9,
                Instruction::Unset(UnsetISpan { name: "0select1".to_owned(), pos: lc(6, 1) }),
            )
            .check();
    }

    #[test]
    fn test_compile_select_internal_var_names() {
        Tester::default()
            .parse("SELECT CASE 0: END SELECT\nSELECT CASE 0: END SELECT")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Integer(0), lc(1, 13)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("0select1")))
            .expect_instr(
                2,
                Instruction::Unset(UnsetISpan { name: "0select1".to_owned(), pos: lc(1, 16) }),
            )
            .expect_instr(3, Instruction::Push(Value::Integer(0), lc(2, 13)))
            .expect_instr(4, Instruction::Assign(SymbolKey::from("0select2")))
            .expect_instr(
                5,
                Instruction::Unset(UnsetISpan { name: "0select2".to_owned(), pos: lc(2, 16) }),
            )
            .check();
    }

    #[test]
    fn test_compile_while() {
        Tester::default()
            .define("FOO", SymbolPrototype::Callable(CallableType::Void, false))
            .parse("WHILE TRUE\nFOO\nWEND")
            .compile()
            .expect_instr(0, Instruction::Push(Value::Boolean(true), lc(1, 7)))
            .expect_instr(
                1,
                Instruction::JumpIfNotTrue(JumpIfBoolISpan {
                    addr: 4,
                    error_msg: "WHILE requires a boolean condition",
                }),
            )
            .expect_instr(
                2,
                Instruction::BuiltinCall(VarRef::new("FOO", VarType::Auto), lc(2, 1), 0),
            )
            .expect_instr(3, Instruction::Jump(JumpISpan { addr: 0 }))
            .check();
    }
}
