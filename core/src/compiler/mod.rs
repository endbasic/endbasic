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
use crate::syms::{
    CallError, CallableMetadata, CallableMetadataBuilder, Symbol, SymbolKey, Symbols,
};
use std::borrow::Cow;
use std::collections::HashMap;
#[cfg(test)]
use std::collections::HashSet;

mod args;
pub use args::*;
mod exprs;
use exprs::{compile_expr, compile_expr_as_type, compile_expr_in_command};

/// Compilation errors.
#[derive(Debug, thiserror::Error)]
#[error("{}: {}", pos, message)]
pub struct Error {
    pub(crate) pos: LineCol,
    pub(crate) message: String,
}

impl Error {
    /// Constructs a new compilation error from its parts.
    pub(crate) fn new<S: Into<String>>(pos: LineCol, message: S) -> Self {
        let message = message.into();
        Self { pos, message }
    }

    /// Annotates a call evaluation error with the command's metadata.
    // TODO(jmmv): This is a hack to support the transition to a parameterized arguments compilers
    // in callables.  Should be removed and/or somehow unified with the `Error` in this module given
    // that `CallError` can specify errors that make no sense in this context.
    fn from_call_error(md: &CallableMetadata, e: CallError, pos: LineCol) -> Self {
        match e {
            CallError::ArgumentError(pos2, e) => {
                Self::new(pos, format!("In call to {}: {}: {}", md.name(), pos2, e))
            }
            CallError::EvalError(pos2, e) => {
                if !md.is_function() {
                    Self::new(pos2, e)
                } else {
                    Self::new(pos, format!("In call to {}: {}: {}", md.name(), pos2, e))
                }
            }
            CallError::InternalError(pos2, e) => {
                Self::new(pos, format!("In call to {}: {}: {}", md.name(), pos2, e))
            }
            CallError::IoError(_) => unreachable!("I/O errors are not possible during compilation"),
            CallError::NestedError(_) => unreachable!("Nested are not possible during compilation"),
            CallError::SyntaxError if md.syntax().is_empty() => {
                Self::new(pos, format!("In call to {}: expected no arguments", md.name()))
            }
            CallError::SyntaxError => {
                Self::new(pos, format!("In call to {}: expected {}", md.name(), md.syntax()))
            }
        }
    }
}

/// Result for compiler return values.
pub type Result<T> = std::result::Result<T, Error>;

/// Information about a symbol in the symbols table.
#[derive(Clone)]
enum SymbolPrototype {
    /// Information about an array.  The integer indicates the number of dimensions in the array.
    Array(ExprType, usize),

    /// Information about a callable.
    Callable(CallableMetadata),

    /// Information about a variable.
    Variable(ExprType),
}

/// The symbols table used during compilation.
///
/// Symbols are represented as a two-layer map: the globals map contains all symbols that are
/// visible by all scopes, and the scope contains all symbols that are only visible within a
/// given scope.
///
/// The collection of symbols that is visible at any given point in time is thus the union of
/// the global symbols and the symbols in the last scope.
///
/// There is always at least one scope in the scopes stack: at the program level outside of
/// functions, variables are not global by default and thus they are kept in their own scope.
/// But because we do not support nested function definitions, the scopes "stack" should
/// always have size of one or two.
struct SymbolsTable {
    /// Map of global symbol names to their definitions.
    globals: HashMap<SymbolKey, SymbolPrototype>,

    /// Map of local symbol names to their definitions.
    scopes: Vec<HashMap<SymbolKey, SymbolPrototype>>,
}

impl Default for SymbolsTable {
    fn default() -> Self {
        Self { globals: HashMap::default(), scopes: vec![HashMap::default()] }
    }
}

impl From<HashMap<SymbolKey, SymbolPrototype>> for SymbolsTable {
    fn from(globals: HashMap<SymbolKey, SymbolPrototype>) -> Self {
        Self { globals, scopes: vec![HashMap::default()] }
    }
}

impl From<&Symbols> for SymbolsTable {
    fn from(syms: &Symbols) -> Self {
        let mut globals = HashMap::default();
        for (name, callable) in syms.callables() {
            let proto = SymbolPrototype::Callable(callable.metadata().clone());
            globals.insert(name.clone(), proto);
        }

        let mut scope = HashMap::default();
        for (name, symbol) in syms.locals() {
            let proto = match symbol {
                Symbol::Array(array) => {
                    SymbolPrototype::Array(array.subtype(), array.dimensions().len())
                }
                Symbol::Callable(_) => {
                    unreachable!("Callables must only be global");
                }
                Symbol::Variable(var) => SymbolPrototype::Variable(var.as_exprtype()),
            };
            scope.insert(name.clone(), proto);
        }

        Self { globals, scopes: vec![scope] }
    }
}

impl SymbolsTable {
    /// Enters a new scope.
    fn enter_scope(&mut self) {
        self.scopes.push(HashMap::default());
    }

    /// Leaves the current scope.
    fn leave_scope(&mut self) {
        let last = self.scopes.pop();
        assert!(last.is_some(), "Must have at least one scope to pop");
        assert!(!self.scopes.is_empty(), "Cannot pop the global scope");
    }

    /// Returns true if the symbols table contains `key`.
    fn contains_key(&mut self, key: &SymbolKey) -> bool {
        self.scopes.last().unwrap().contains_key(key) || self.globals.contains_key(key)
    }

    /// Returns the information for the symbol `key` if it exists, otherwise `None`.
    fn get(&self, key: &SymbolKey) -> Option<&SymbolPrototype> {
        let proto = self.scopes.last().unwrap().get(key);
        if proto.is_some() {
            return proto;
        }

        self.globals.get(key)
    }

    /// Inserts the new information `proto` about symbol `key` into the symbols table.
    /// The symbol must not yet exist.
    fn insert(&mut self, key: SymbolKey, proto: SymbolPrototype) {
        debug_assert!(!self.globals.contains_key(&key), "Cannot redefine a symbol");
        let previous = self.scopes.last_mut().unwrap().insert(key, proto);
        debug_assert!(previous.is_none(), "Cannot redefine a symbol");
    }

    /// Inserts the new information `proto` about symbol `key` into the symbols table.
    /// The symbol must not yet exist.
    fn insert_global(&mut self, key: SymbolKey, proto: SymbolPrototype) {
        let previous = self.globals.insert(key, proto);
        debug_assert!(previous.is_none(), "Cannot redefine a symbol");
    }

    /// Removes information about the symbol `key`.
    fn remove(&mut self, key: SymbolKey) {
        let previous = self.scopes.last_mut().unwrap().remove(&key);
        debug_assert!(previous.is_some(), "Cannot unset a non-existing symbol");
    }

    /// Returns a view of the keys in the symbols table.
    #[cfg(test)]
    fn keys(&self) -> HashSet<&SymbolKey> {
        let mut keys = HashSet::default();
        keys.extend(self.globals.keys());
        keys.extend(self.scopes.last().unwrap().keys());
        keys
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

    /// Name of the function being compiled, needed to set the return value in assignment operators.
    current_function: Option<SymbolKey>,

    /// Callables to be compiled.
    callable_spans: Vec<CallableSpan>,
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

    /// Generates the name of the symbol that holds the return value of the function `name`.
    fn return_key(name: &SymbolKey) -> SymbolKey {
        SymbolKey::from(format!("0return_{}", name))
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

    /// Compiles the indices used to address an array.
    fn compile_array_indices(
        &mut self,
        exp_nargs: usize,
        args: Vec<Expr>,
        name_pos: LineCol,
    ) -> Result<()> {
        let mut instrs = vec![];
        match exprs::compile_array_indices(&mut instrs, &self.symtable, exp_nargs, args, name_pos) {
            Ok(result) => {
                self.next_pc += instrs.len();
                self.instrs.append(&mut instrs);
                Ok(result)
            }
            Err(e) => Err(e),
        }
    }

    /// Compiles an assignment to an array position.
    fn compile_array_assignment(&mut self, span: ArrayAssignmentSpan) -> Result<()> {
        let key = SymbolKey::from(span.vref.name());
        let (atype, dims) = match self.symtable.get(&key) {
            Some(SymbolPrototype::Array(atype, dims)) => (*atype, *dims),
            Some(_) => {
                return Err(Error::new(
                    span.vref_pos,
                    format!("Cannot index non-array {}", span.vref),
                ));
            }
            None => {
                return Err(Error::new(
                    span.vref_pos,
                    format!("Cannot index undefined array {}", span.vref),
                ));
            }
        };

        if !span.vref.accepts(atype) {
            return Err(Error::new(
                span.vref_pos,
                format!("Incompatible types in {} reference", span.vref),
            ));
        }

        let etype = self.compile_expr(span.expr, false)?;
        let etype = self.maybe_cast(atype, etype);
        if etype != atype {
            return Err(Error::new(
                span.vref_pos,
                format!("Cannot assign value of type {} to array of type {}", etype, atype),
            ));
        }

        let nargs = span.subscripts.len();
        self.compile_array_indices(dims, span.subscripts, span.vref_pos)?;

        self.emit(Instruction::ArrayAssignment(key, span.vref_pos, nargs));

        Ok(())
    }

    /// Compiles an assignment, be it from the code or one synthesized during compilation.
    ///
    /// It's important to always use this function instead of manually emitting `Instruction::Assign`
    /// instructions to ensure consistent handling of the symbols table.
    fn compile_assignment(&mut self, vref: VarRef, vref_pos: LineCol, expr: Expr) -> Result<()> {
        let mut key = SymbolKey::from(&vref.name());
        let etype = self.compile_expr(expr, false)?;

        if let Some(current_function) = self.current_function.as_ref() {
            if &key == current_function {
                key = Compiler::return_key(current_function);
            }
        }

        let vtype = match self.symtable.get(&key) {
            Some(SymbolPrototype::Variable(vtype)) => *vtype,
            Some(_) => {
                return Err(Error::new(vref_pos, format!("Cannot redefine {} as a variable", vref)))
            }
            None => {
                // TODO(jmmv): Compile separate Dim instructions for new variables instead of
                // checking this every time.
                let key = key.clone();
                let vtype = vref.ref_type().unwrap_or(etype);
                self.symtable.insert(key, SymbolPrototype::Variable(vtype));
                vtype
            }
        };

        let etype = self.maybe_cast(vtype, etype);
        if etype != vtype {
            return Err(Error::new(
                vref_pos,
                format!("Cannot assign value of type {} to variable of type {}", etype, vtype,),
            ));
        }

        if let Some(ref_type) = vref.ref_type() {
            if ref_type != vtype {
                return Err(Error::new(
                    vref_pos,
                    format!("Incompatible types in {} reference", vref),
                ));
            }
        }

        self.emit(Instruction::Assign(key));

        Ok(())
    }

    /// Compiles a `FUNCTION` or `SUB` definition.
    fn compile_callable(&mut self, span: CallableSpan) -> Result<()> {
        let key = SymbolKey::from(span.name.name());
        if self.symtable.contains_key(&key) {
            return Err(Error::new(
                span.name_pos,
                format!("Cannot define already-defined symbol {}", span.name),
            ));
        }

        let mut syntax = vec![];
        for (i, param) in span.params.iter().enumerate() {
            let sep = if i == span.params.len() - 1 {
                ArgSepSyntax::End
            } else {
                ArgSepSyntax::Exactly(ArgSep::Long)
            };
            syntax.push(SingularArgSyntax::RequiredValue(
                RequiredValueSyntax {
                    name: Cow::Owned(param.name().to_owned()),
                    vtype: param.ref_type().unwrap_or(ExprType::Integer),
                },
                sep,
            ));
        }

        let mut builder = CallableMetadataBuilder::new_dynamic(span.name.name().to_owned())
            .with_dynamic_syntax(vec![(syntax, None)])
            .with_category("User defined")
            .with_description("User defined symbol.");
        if let Some(ctype) = span.name.ref_type() {
            builder = builder.with_return_type(ctype);
        }
        self.symtable.insert_global(key, SymbolPrototype::Callable(builder.build()));
        self.callable_spans.push(span);

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

        self.emit(Instruction::Dim(DimISpan {
            name: key.clone(),
            shared: span.shared,
            vtype: span.vtype,
        }));
        if span.shared {
            self.symtable.insert_global(key, SymbolPrototype::Variable(span.vtype));
        } else {
            self.symtable.insert(key, SymbolPrototype::Variable(span.vtype));
        }

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
                self.compile_expr_guard(guard, "DO requires a boolean condition")?;
                let jump_pc = self.emit(Instruction::Nop);
                self.compile_many(span.body)?;
                end_pc = self.emit(Instruction::Jump(JumpISpan { addr: start_pc }));
                self.instrs[jump_pc] = Instruction::JumpIfTrue(self.next_pc);
            }

            DoGuard::PreWhile(guard) => {
                let start_pc = self.next_pc;
                self.compile_expr_guard(guard, "DO requires a boolean condition")?;
                let jump_pc = self.emit(Instruction::Nop);
                self.compile_many(span.body)?;
                end_pc = self.emit(Instruction::Jump(JumpISpan { addr: start_pc }));
                self.instrs[jump_pc] = Instruction::JumpIfNotTrue(self.next_pc);
            }

            DoGuard::PostUntil(guard) => {
                let start_pc = self.next_pc;
                self.compile_many(span.body)?;
                self.compile_expr_guard(guard, "LOOP requires a boolean condition")?;
                end_pc = self.emit(Instruction::JumpIfNotTrue(start_pc));
            }

            DoGuard::PostWhile(guard) => {
                let start_pc = self.next_pc;
                self.compile_many(span.body)?;
                self.compile_expr_guard(guard, "LOOP requires a boolean condition")?;
                end_pc = self.emit(Instruction::JumpIfTrue(start_pc));
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
            span.iter.ref_type().is_none()
                || span.iter.ref_type().unwrap() == ExprType::Double
                || span.iter.ref_type().unwrap() == ExprType::Integer
        );

        if span.iter_double && span.iter.ref_type().is_none() {
            let key = SymbolKey::from(span.iter.name());
            let skip_pc = self.emit(Instruction::Nop);

            let iter_key = SymbolKey::from(span.iter.name());
            if self.symtable.get(&key).is_none() {
                self.emit(Instruction::Dim(DimISpan {
                    name: key,
                    shared: false,
                    vtype: ExprType::Double,
                }));
                self.symtable.insert(iter_key.clone(), SymbolPrototype::Variable(ExprType::Double));
            }

            self.instrs[skip_pc] = Instruction::JumpIfDefined(JumpIfDefinedISpan {
                var: iter_key,
                addr: self.next_pc,
            });
        }

        self.compile_assignment(span.iter.clone(), span.iter_pos, span.start)?;

        let start_pc = self.next_pc;
        let end_etype = self.compile_expr(span.end, false)?;
        match end_etype {
            ExprType::Boolean => (),
            _ => panic!("Synthesized end condition for FOR must yield a boolean"),
        };
        let jump_pc = self.emit(Instruction::Nop);

        self.compile_many(span.body)?;

        self.compile_assignment(span.iter.clone(), span.iter_pos, span.next)?;

        self.emit(Instruction::Jump(JumpISpan { addr: start_pc }));

        self.instrs[jump_pc] = Instruction::JumpIfNotTrue(self.next_pc);

        Ok(())
    }

    /// Compiles an `IF` statement and appends its instructions to the compilation context.
    fn compile_if(&mut self, span: IfSpan) -> Result<()> {
        let mut end_pcs = vec![];

        let mut iter = span.branches.into_iter();
        let mut next = iter.next();
        while let Some(branch) = next {
            let next2 = iter.next();

            self.compile_expr_guard(branch.guard, "IF/ELSEIF require a boolean condition")?;
            let jump_pc = self.emit(Instruction::Nop);
            self.compile_many(branch.body)?;

            if next2.is_some() {
                end_pcs.push(self.next_pc);
                self.emit(Instruction::Nop);
            }

            self.instrs[jump_pc] = Instruction::JumpIfNotTrue(self.next_pc);

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
        let test_vref = VarRef::new(Compiler::select_test_var_name(self.selects), None);
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
                    self.compile_expr_guard(guard, "SELECT requires a boolean condition")?;
                    let jump_pc = self.emit(Instruction::Nop);
                    self.compile_many(case.body)?;

                    if next2.is_some() {
                        end_pcs.push(self.next_pc);
                        self.emit(Instruction::Nop);
                    }

                    self.instrs[jump_pc] = Instruction::JumpIfNotTrue(self.next_pc);
                }
            }

            next = next2;
        }

        for end_pc in end_pcs {
            self.instrs[end_pc] = Instruction::Jump(JumpISpan { addr: self.next_pc });
        }

        let test_key = SymbolKey::from(test_vref.name());
        self.emit(Instruction::Unset(UnsetISpan { name: test_key.clone(), pos: span.end_pos }));
        self.symtable.remove(test_key);

        Ok(())
    }

    /// Compiles a `WHILE` loop and appends its instructions to the compilation context.
    fn compile_while(&mut self, span: WhileSpan) -> Result<()> {
        let start_pc = self.next_pc;
        self.compile_expr_guard(span.expr, "WHILE requires a boolean condition")?;
        let jump_pc = self.emit(Instruction::Nop);

        self.compile_many(span.body)?;

        self.emit(Instruction::Jump(JumpISpan { addr: start_pc }));

        self.instrs[jump_pc] = Instruction::JumpIfNotTrue(self.next_pc);

        Ok(())
    }

    /// Compiles the evaluation of an expression, appends its instructions to the
    /// compilation context, and returns the type of the compiled expression.
    ///
    /// `allow_varrefs` should be true for top-level expression compilations within
    /// function arguments.  In that specific case, we must leave bare variable
    /// references unevaluated because we don't know if the function wants to take
    /// the reference or the value.
    fn compile_expr(&mut self, expr: Expr, allow_varrefs: bool) -> Result<ExprType> {
        let result = if allow_varrefs {
            compile_expr_in_command(&mut self.instrs, &mut self.symtable, expr)
        } else {
            compile_expr(&mut self.instrs, &self.symtable, expr, false)
        };
        match result {
            Ok(result) => {
                self.next_pc = self.instrs.len();
                Ok(result)
            }
            Err(e) => Err(e),
        }
    }

    /// Compiles the evaluation of an expression with casts to a target type, appends its
    /// instructions to the compilation context, and returns the type of the compiled expression.
    fn compile_expr_as_type(&mut self, expr: Expr, target: ExprType) -> Result<()> {
        compile_expr_as_type(&mut self.instrs, &self.symtable, expr, target)?;
        self.next_pc = self.instrs.len();
        Ok(())
    }

    /// Compiles an expression that guards a conditional statement.  Returns an error if the
    /// expression is invalid or if it does not evaluate to a boolean.
    fn compile_expr_guard<S: Into<String>>(&mut self, guard: Expr, errmsg: S) -> Result<()> {
        let pos = guard.start_pos();
        match self.compile_expr(guard, false)? {
            ExprType::Boolean => Ok(()),
            _ => Err(Error::new(pos, errmsg.into())),
        }
    }

    /// Compiles one statement and appends its bytecode to the current compilation context.
    fn compile_one(&mut self, stmt: Statement) -> Result<()> {
        match stmt {
            Statement::ArrayAssignment(span) => {
                self.compile_array_assignment(span)?;
            }

            Statement::Assignment(span) => {
                self.compile_assignment(span.vref, span.vref_pos, span.expr)?;
            }

            Statement::Call(span) => {
                let key = SymbolKey::from(&span.vref.name());
                let md = match self.symtable.get(&key) {
                    Some(SymbolPrototype::Callable(md)) => {
                        if md.is_function() {
                            return Err(Error::new(
                                span.vref_pos,
                                format!("{} is not a command", span.vref.name()),
                            ));
                        }
                        md.clone()
                    }

                    Some(_) => {
                        return Err(Error::new(
                            span.vref_pos,
                            format!("{} is not a command", span.vref.name()),
                        ));
                    }

                    None => {
                        return Err(Error::new(
                            span.vref_pos,
                            format!("Unknown builtin {}", span.vref.name()),
                        ))
                    }
                };

                let name_pos = span.vref_pos;
                let nargs = compile_command_args(
                    md.syntaxes(),
                    &mut self.instrs,
                    &mut self.symtable,
                    name_pos,
                    span.args,
                )
                .map_err(|e| Error::from_call_error(&md, e, name_pos))?;
                self.next_pc = self.instrs.len();
                self.emit(Instruction::BuiltinCall(key, span.vref_pos, nargs));
            }

            Statement::Callable(span) => {
                self.compile_callable(span)?;
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
                    self.compile_expr_as_type(arg, ExprType::Integer)?;
                }
                self.emit(Instruction::DimArray(DimArrayISpan {
                    name: key.clone(),
                    name_pos: span.name_pos,
                    shared: span.shared,
                    dimensions: nargs,
                    subtype: span.subtype,
                    subtype_pos: span.subtype_pos,
                }));

                if span.shared {
                    self.symtable.insert_global(key, SymbolPrototype::Array(span.subtype, nargs));
                } else {
                    self.symtable.insert(key, SymbolPrototype::Array(span.subtype, nargs));
                }
            }

            Statement::Do(span) => {
                self.compile_do(span)?;
            }

            Statement::End(span) => match span.code {
                Some(expr) => {
                    self.compile_expr_as_type(expr, ExprType::Integer)?;
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

    /// Compiles all callables discovered during the first phase and fixes up all call sites to
    /// point to the compiled code.
    fn compile_callables(&mut self) -> Result<()> {
        let end = self.emit(Instruction::Nop);

        let mut functions = HashMap::with_capacity(self.callable_spans.len());
        let mut subs = HashMap::with_capacity(self.callable_spans.len());
        let callable_spans = std::mem::take(&mut self.callable_spans);
        for span in callable_spans {
            let pc = self.next_pc;

            let key = SymbolKey::from(span.name.name());
            let return_value = Compiler::return_key(&key);
            match span.name.ref_type() {
                Some(return_type) => {
                    self.emit(Instruction::EnterScope);
                    self.symtable.enter_scope();

                    self.emit(Instruction::Dim(DimISpan {
                        name: return_value.clone(),
                        shared: false,
                        vtype: return_type,
                    }));
                    self.symtable
                        .insert(return_value.clone(), SymbolPrototype::Variable(return_type));

                    for param in span.params {
                        let key = SymbolKey::from(param.name());
                        let ptype = param.ref_type().unwrap_or(ExprType::Integer);
                        self.emit(Instruction::Assign(key.clone()));
                        self.symtable.insert(key, SymbolPrototype::Variable(ptype));
                    }

                    self.current_function = Some(key.clone());
                    self.compile_many(span.body)?;
                    self.current_function = None;

                    let load_inst = match return_type {
                        ExprType::Boolean => Instruction::LoadBoolean,
                        ExprType::Double => Instruction::LoadDouble,
                        ExprType::Integer => Instruction::LoadInteger,
                        ExprType::Text => Instruction::LoadString,
                    };
                    self.emit(load_inst(return_value.clone(), span.end_pos));

                    self.emit(Instruction::LeaveScope);
                    self.symtable.leave_scope();
                    self.emit(Instruction::Return(span.end_pos));

                    functions.insert(key, pc);
                }
                None => {
                    self.emit(Instruction::EnterScope);
                    self.symtable.enter_scope();

                    for param in span.params {
                        let key = SymbolKey::from(param.name());
                        let ptype = param.ref_type().unwrap_or(ExprType::Integer);
                        self.emit(Instruction::Assign(key.clone()));
                        self.symtable.insert(key, SymbolPrototype::Variable(ptype));
                    }

                    self.compile_many(span.body)?;

                    self.emit(Instruction::LeaveScope);
                    self.symtable.leave_scope();
                    self.emit(Instruction::Return(span.end_pos));

                    subs.insert(key, pc);
                }
            }
        }

        for instr in &mut self.instrs {
            match instr {
                Instruction::BuiltinCall(key, _, _) => {
                    if let Some(addr) = subs.get(key) {
                        *instr = Instruction::Call(JumpISpan { addr: *addr });
                    }
                }

                Instruction::FunctionCall(key, _, _, _) => {
                    if let Some(addr) = functions.get(key) {
                        *instr = Instruction::Call(JumpISpan { addr: *addr });
                    }
                }

                _ => (),
            }
        }

        self.instrs[end] = Instruction::Jump(JumpISpan { addr: self.next_pc });

        Ok(())
    }

    /// Finishes compilation and returns the image representing the compiled program.
    #[allow(clippy::wrong_self_convention)]
    fn to_image(mut self) -> Result<(Image, SymbolsTable)> {
        if !self.callable_spans.is_empty() {
            self.compile_callables()?;
        }

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
    use crate::syms::CallableMetadataBuilder;

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

        /// Inserts `name` into the symbols table as a callable.
        ///
        /// This is syntactic sugar over `define` to simplify the definition of callables.
        pub(crate) fn define_callable(mut self, builder: CallableMetadataBuilder) -> Self {
            let md = builder.test_build();
            let key = SymbolKey::from(md.name());
            self.symtable.insert(key, SymbolPrototype::Callable(md));
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
                match self.result {
                    Ok(_) => panic!("Compilation succeeded but expected error: {}", message),
                    Err(e) => assert_eq!(message, e.to_string()),
                }
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
                    Some(proto) => assert_eq!(
                        std::mem::discriminant(&exp_proto),
                        std::mem::discriminant(proto)
                    ),
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
    use crate::syms::CallableMetadataBuilder;
    use std::borrow::Cow;

    #[test]
    fn test_compile_nothing() {
        Tester::default().compile().check();
    }

    #[test]
    fn test_compile_array_assignment_exprs() {
        Tester::default()
            .define("foo", SymbolPrototype::Array(ExprType::Integer, 3))
            .define("i", SymbolPrototype::Variable(ExprType::Integer))
            .parse("foo(3, 4 + i, i) = 5")
            .compile()
            .expect_instr(0, Instruction::PushInteger(5, lc(1, 20)))
            .expect_instr(1, Instruction::LoadInteger(SymbolKey::from("i"), lc(1, 15)))
            .expect_instr(2, Instruction::PushInteger(4, lc(1, 8)))
            .expect_instr(3, Instruction::LoadInteger(SymbolKey::from("i"), lc(1, 12)))
            .expect_instr(4, Instruction::AddIntegers(lc(1, 10)))
            .expect_instr(5, Instruction::PushInteger(3, lc(1, 5)))
            .expect_instr(6, Instruction::ArrayAssignment(SymbolKey::from("foo"), lc(1, 1), 3))
            .check();
    }

    #[test]
    fn test_compile_array_assignment_ok_annotation() {
        Tester::default()
            .define("a", SymbolPrototype::Array(ExprType::Integer, 1))
            .parse("a%(0) = 1")
            .compile()
            .expect_instr(0, Instruction::PushInteger(1, lc(1, 9)))
            .expect_instr(1, Instruction::PushInteger(0, lc(1, 4)))
            .expect_instr(2, Instruction::ArrayAssignment(SymbolKey::from("a"), lc(1, 1), 1))
            .check();
    }

    #[test]
    fn test_compile_array_assignment_index_double() {
        Tester::default()
            .define("a", SymbolPrototype::Array(ExprType::Integer, 1))
            .parse("a(1.2) = 1")
            .compile()
            .expect_instr(0, Instruction::PushInteger(1, lc(1, 10)))
            .expect_instr(1, Instruction::PushDouble(1.2, lc(1, 3)))
            .expect_instr(2, Instruction::DoubleToInteger)
            .expect_instr(3, Instruction::ArrayAssignment(SymbolKey::from("a"), lc(1, 1), 1))
            .check();
    }

    #[test]
    fn test_compile_array_assignment_index_bad_type() {
        Tester::default()
            .define("a", SymbolPrototype::Array(ExprType::Integer, 1))
            .parse("a(TRUE) = 1")
            .compile()
            .expect_err("1:3: Array index must be INTEGER, not BOOLEAN")
            .check();
    }

    #[test]
    fn test_compile_array_assignment_bad_annotation() {
        Tester::default()
            .define("a", SymbolPrototype::Array(ExprType::Integer, 1))
            .parse("a#(0) = 1")
            .compile()
            .expect_err("1:1: Incompatible types in a# reference")
            .check();
    }

    #[test]
    fn test_compile_array_assignment_double_to_integer_promotion() {
        Tester::default()
            .define("a", SymbolPrototype::Array(ExprType::Integer, 1))
            .define("d", SymbolPrototype::Variable(ExprType::Double))
            .parse("a(3) = d")
            .compile()
            .expect_instr(0, Instruction::LoadDouble(SymbolKey::from("d"), lc(1, 8)))
            .expect_instr(1, Instruction::DoubleToInteger)
            .expect_instr(2, Instruction::PushInteger(3, lc(1, 3)))
            .expect_instr(3, Instruction::ArrayAssignment(SymbolKey::from("a"), lc(1, 1), 1))
            .check();
    }

    #[test]
    fn test_compile_array_assignment_integer_to_double_promotion() {
        Tester::default()
            .define("a", SymbolPrototype::Array(ExprType::Double, 1))
            .define("i", SymbolPrototype::Variable(ExprType::Integer))
            .parse("a(3) = i")
            .compile()
            .expect_instr(0, Instruction::LoadInteger(SymbolKey::from("i"), lc(1, 8)))
            .expect_instr(1, Instruction::IntegerToDouble)
            .expect_instr(2, Instruction::PushInteger(3, lc(1, 3)))
            .expect_instr(3, Instruction::ArrayAssignment(SymbolKey::from("a"), lc(1, 1), 1))
            .check();
    }

    #[test]
    fn test_compile_array_assignment_bad_types() {
        Tester::default()
            .define("a", SymbolPrototype::Array(ExprType::Double, 1))
            .define("i", SymbolPrototype::Variable(ExprType::Integer))
            .parse("a(3) = FALSE")
            .compile()
            .expect_err("1:1: Cannot assign value of type BOOLEAN to array of type DOUBLE")
            .check();
    }

    #[test]
    fn test_compile_array_assignment_bad_dimensions() {
        Tester::default()
            .define("a", SymbolPrototype::Array(ExprType::Double, 1))
            .define("i", SymbolPrototype::Variable(ExprType::Integer))
            .parse("a(3, 5) = 7")
            .compile()
            .expect_err("1:1: Cannot index array with 2 subscripts; need 1")
            .check();
    }

    #[test]
    fn test_compile_array_assignment_not_defined() {
        Tester::default()
            .parse("a(3) = FALSE")
            .compile()
            .expect_err("1:1: Cannot index undefined array a")
            .check();
    }

    #[test]
    fn test_compile_array_assignment_not_an_array() {
        Tester::default()
            .define("a", SymbolPrototype::Variable(ExprType::Integer))
            .parse("a(3) = FALSE")
            .compile()
            .expect_err("1:1: Cannot index non-array a")
            .check();
    }

    #[test]
    fn test_compile_assignment_literal() {
        Tester::default()
            .parse("foo = 5")
            .compile()
            .expect_instr(0, Instruction::PushInteger(5, lc(1, 7)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("foo")))
            .check();
    }

    #[test]
    fn test_compile_assignment_varref_is_evaluated() {
        Tester::default()
            .define("i", SymbolPrototype::Variable(ExprType::Integer))
            .parse("foo = i")
            .compile()
            .expect_instr(0, Instruction::LoadInteger(SymbolKey::from("i"), lc(1, 7)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("foo")))
            .check();
    }

    #[test]
    fn test_compile_assignment_new_var_auto_ref_expr_determines_type() {
        Tester::default()
            .parse("foo = 2.3")
            .compile()
            .expect_instr(0, Instruction::PushDouble(2.3, lc(1, 7)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("foo")))
            .expect_symtable(SymbolKey::from("foo"), SymbolPrototype::Variable(ExprType::Double))
            .check();
    }

    #[test]
    fn test_compile_assignment_new_var_explicit_ref_determines_type() {
        Tester::default()
            .parse("foo# = 2")
            .compile()
            .expect_instr(0, Instruction::PushInteger(2, lc(1, 8)))
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
            .define_callable(CallableMetadataBuilder::new("CMD"))
            .parse("CMD")
            .compile()
            .expect_instr(0, Instruction::BuiltinCall(SymbolKey::from("CMD"), lc(1, 1), 0))
            .check();
    }

    #[test]
    fn test_compile_builtin_call_increments_next_pc() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("CMD").with_syntax(&[(
                &[],
                Some(&RepeatedSyntax {
                    name: Cow::Borrowed("expr"),
                    type_syn: RepeatedTypeSyntax::TypedValue(ExprType::Integer),
                    sep: ArgSepSyntax::Exactly(ArgSep::Long),
                    require_one: false,
                    allow_missing: false,
                }),
            )]))
            .parse("IF TRUE THEN: CMD 1, 2: END IF")
            .compile()
            .expect_instr(0, Instruction::PushBoolean(true, lc(1, 4)))
            .expect_instr(1, Instruction::JumpIfNotTrue(5))
            .expect_instr(2, Instruction::PushInteger(2, lc(1, 22)))
            .expect_instr(3, Instruction::PushInteger(1, lc(1, 19)))
            .expect_instr(4, Instruction::BuiltinCall(SymbolKey::from("CMD"), lc(1, 15), 2))
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
            .expect_instr(
                0,
                Instruction::Dim(DimISpan {
                    name: SymbolKey::from("var"),
                    shared: false,
                    vtype: ExprType::Boolean,
                }),
            )
            .check();
        Tester::default()
            .parse("DIM var AS DOUBLE")
            .compile()
            .expect_instr(
                0,
                Instruction::Dim(DimISpan {
                    name: SymbolKey::from("var"),
                    shared: false,
                    vtype: ExprType::Double,
                }),
            )
            .check();
        Tester::default()
            .parse("DIM var AS INTEGER")
            .compile()
            .expect_instr(
                0,
                Instruction::Dim(DimISpan {
                    name: SymbolKey::from("var"),
                    shared: false,
                    vtype: ExprType::Integer,
                }),
            )
            .check();
        Tester::default()
            .parse("DIM var AS STRING")
            .compile()
            .expect_instr(
                0,
                Instruction::Dim(DimISpan {
                    name: SymbolKey::from("var"),
                    shared: false,
                    vtype: ExprType::Text,
                }),
            )
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
            .define("SomeArray", SymbolPrototype::Array(ExprType::Integer, 3))
            .parse("DIM somearray")
            .compile()
            .expect_err("1:5: Cannot DIM already-defined symbol somearray")
            .check();

        Tester::default()
            .define_callable(
                CallableMetadataBuilder::new("OUT").with_return_type(ExprType::Integer),
            )
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
    fn test_compile_dim_shared_ok() {
        Tester::default()
            .parse("DIM SHARED var AS BOOLEAN")
            .compile()
            .expect_instr(
                0,
                Instruction::Dim(DimISpan {
                    name: SymbolKey::from("var"),
                    shared: true,
                    vtype: ExprType::Boolean,
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_dim_shared_name_overlap_with_local() {
        Tester::default()
            .parse("DIM var AS BOOLEAN: DIM SHARED Var AS BOOLEAN")
            .compile()
            .expect_err("1:32: Cannot DIM already-defined symbol Var")
            .check();

        Tester::default()
            .parse("DIM SHARED var AS BOOLEAN: DIM Var AS BOOLEAN")
            .compile()
            .expect_err("1:32: Cannot DIM already-defined symbol Var")
            .check();
    }

    #[test]
    fn test_compile_dim_array_immediate() {
        Tester::default()
            .parse("DIM var(1) AS INTEGER")
            .compile()
            .expect_instr(0, Instruction::PushInteger(1, lc(1, 9)))
            .expect_instr(
                1,
                Instruction::DimArray(DimArrayISpan {
                    name: SymbolKey::from("var"),
                    name_pos: lc(1, 5),
                    shared: false,
                    dimensions: 1,
                    subtype: ExprType::Integer,
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
            .expect_instr(0, Instruction::PushInteger(3, lc(1, 12)))
            .expect_instr(1, Instruction::PushInteger(4, lc(1, 16)))
            .expect_instr(2, Instruction::AddIntegers(lc(1, 14)))
            .expect_instr(3, Instruction::LoadInteger(SymbolKey::from("i"), lc(1, 9)))
            .expect_instr(
                4,
                Instruction::DimArray(DimArrayISpan {
                    name: SymbolKey::from("var"),
                    name_pos: lc(1, 5),
                    shared: false,
                    dimensions: 2,
                    subtype: ExprType::Integer,
                    subtype_pos: lc(1, 22),
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_dim_array_double_to_integer() {
        Tester::default()
            .parse("DIM var(3.7) AS INTEGER")
            .compile()
            .expect_instr(0, Instruction::PushDouble(3.7, lc(1, 9)))
            .expect_instr(1, Instruction::DoubleToInteger)
            .expect_instr(
                2,
                Instruction::DimArray(DimArrayISpan {
                    name: SymbolKey::from("var"),
                    name_pos: lc(1, 5),
                    shared: false,
                    dimensions: 1,
                    subtype: ExprType::Integer,
                    subtype_pos: lc(1, 17),
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_dim_array_dimension_type_error() {
        Tester::default()
            .parse("DIM var(TRUE) AS INTEGER")
            .compile()
            .expect_err("1:9: BOOLEAN is not a number")
            .check();
    }

    #[test]
    fn test_compile_dim_array_shared_ok() {
        Tester::default()
            .parse("DIM SHARED var(1) AS INTEGER")
            .compile()
            .expect_instr(0, Instruction::PushInteger(1, lc(1, 16)))
            .expect_instr(
                1,
                Instruction::DimArray(DimArrayISpan {
                    name: SymbolKey::from("var"),
                    name_pos: lc(1, 12),
                    shared: true,
                    dimensions: 1,
                    subtype: ExprType::Integer,
                    subtype_pos: lc(1, 22),
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_dim_array_shared_name_overlap_with_local() {
        Tester::default()
            .parse("DIM var(1) AS BOOLEAN: DIM SHARED Var(1) AS BOOLEAN")
            .compile()
            .expect_err("1:35: Cannot DIM already-defined symbol Var")
            .check();

        Tester::default()
            .parse("DIM SHARED var(1) AS BOOLEAN: DIM Var(1) AS BOOLEAN")
            .compile()
            .expect_err("1:35: Cannot DIM already-defined symbol Var")
            .check();
    }

    #[test]
    fn test_compile_do_infinite() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("FOO"))
            .parse("DO\nFOO\nLOOP")
            .compile()
            .expect_instr(0, Instruction::BuiltinCall(SymbolKey::from("FOO"), lc(2, 1), 0))
            .expect_instr(1, Instruction::Jump(JumpISpan { addr: 0 }))
            .check();
    }

    #[test]
    fn test_compile_do_pre_guard() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("FOO"))
            .parse("DO WHILE TRUE\nFOO\nLOOP")
            .compile()
            .expect_instr(0, Instruction::PushBoolean(true, lc(1, 10)))
            .expect_instr(1, Instruction::JumpIfNotTrue(4))
            .expect_instr(2, Instruction::BuiltinCall(SymbolKey::from("FOO"), lc(2, 1), 0))
            .expect_instr(3, Instruction::Jump(JumpISpan { addr: 0 }))
            .check();
    }

    #[test]
    fn test_compile_do_post_guard() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("FOO"))
            .parse("DO\nFOO\nLOOP WHILE TRUE")
            .compile()
            .expect_instr(0, Instruction::BuiltinCall(SymbolKey::from("FOO"), lc(2, 1), 0))
            .expect_instr(1, Instruction::PushBoolean(true, lc(3, 12)))
            .expect_instr(2, Instruction::JumpIfTrue(0))
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
            .expect_instr(0, Instruction::PushInteger(2, lc(1, 5)))
            .expect_instr(1, Instruction::LoadInteger(SymbolKey::from("i"), lc(1, 9)))
            .expect_instr(2, Instruction::AddIntegers(lc(1, 7)))
            .expect_instr(3, Instruction::End(true))
            .check();
    }

    #[test]
    fn test_compile_end_with_exit_code_varref() {
        Tester::default()
            .define("i", SymbolPrototype::Variable(ExprType::Integer))
            .parse("END i")
            .compile()
            .expect_instr(0, Instruction::LoadInteger(SymbolKey::from("i"), lc(1, 5)))
            .expect_instr(1, Instruction::End(true))
            .check();
    }

    #[test]
    fn test_compile_end_with_exit_code_type_error() {
        Tester::default()
            .parse("END TRUE")
            .compile()
            .expect_err("1:5: BOOLEAN is not a number")
            .check();
    }

    #[test]
    fn test_compile_end_with_exit_code_double_to_integer() {
        Tester::default()
            .parse("END 2.3")
            .compile()
            .expect_instr(0, Instruction::PushDouble(2.3, lc(1, 5)))
            .expect_instr(1, Instruction::DoubleToInteger)
            .expect_instr(2, Instruction::End(true))
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
            .expect_instr(0, Instruction::PushBoolean(true, lc(1, 10)))
            .expect_instr(1, Instruction::JumpIfNotTrue(4))
            .expect_instr(2, Instruction::Jump(JumpISpan { addr: 4 }))
            .expect_instr(3, Instruction::Jump(JumpISpan { addr: 0 }))
            .check();
    }

    #[test]
    fn test_compile_exit_do_nested() {
        Tester::default()
            .parse("DO WHILE TRUE\nEXIT DO\nDO UNTIL FALSE\nEXIT DO\nLOOP\nLOOP")
            .compile()
            .expect_instr(0, Instruction::PushBoolean(true, lc(1, 10)))
            .expect_instr(1, Instruction::JumpIfNotTrue(8))
            .expect_instr(2, Instruction::Jump(JumpISpan { addr: 8 }))
            .expect_instr(3, Instruction::PushBoolean(false, lc(3, 10)))
            .expect_instr(4, Instruction::JumpIfTrue(7))
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
            .expect_instr(0, Instruction::PushBoolean(true, lc(1, 10)))
            .expect_instr(1, Instruction::JumpIfNotTrue(4))
            .expect_instr(2, Instruction::Jump(JumpISpan { addr: 4 }))
            .expect_instr(3, Instruction::Jump(JumpISpan { addr: 0 }))
            .expect_instr(4, Instruction::PushBoolean(true, lc(4, 10)))
            .expect_instr(5, Instruction::JumpIfNotTrue(8))
            .expect_instr(6, Instruction::Jump(JumpISpan { addr: 8 }))
            .expect_instr(7, Instruction::Jump(JumpISpan { addr: 4 }))
            .check();
    }

    #[test]
    fn test_compile_exit_do_from_nested_while() {
        Tester::default()
            .parse("DO WHILE TRUE\nEXIT DO\nWHILE FALSE\nEXIT DO\nWEND\nLOOP")
            .compile()
            .expect_instr(0, Instruction::PushBoolean(true, lc(1, 10)))
            .expect_instr(1, Instruction::JumpIfNotTrue(8))
            .expect_instr(2, Instruction::Jump(JumpISpan { addr: 8 }))
            .expect_instr(3, Instruction::PushBoolean(false, lc(3, 7)))
            .expect_instr(4, Instruction::JumpIfNotTrue(7))
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
    fn test_compile_for_simple_literals() {
        Tester::default()
            .parse("FOR iter = 1 TO 5: a = FALSE: NEXT")
            .compile()
            .expect_instr(0, Instruction::PushInteger(1, lc(1, 12)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("iter")))
            .expect_instr(2, Instruction::LoadInteger(SymbolKey::from("iter"), lc(1, 5)))
            .expect_instr(3, Instruction::PushInteger(5, lc(1, 17)))
            .expect_instr(4, Instruction::LessEqualIntegers(lc(1, 14)))
            .expect_instr(5, Instruction::JumpIfNotTrue(13))
            .expect_instr(6, Instruction::PushBoolean(false, lc(1, 24)))
            .expect_instr(7, Instruction::Assign(SymbolKey::from("a")))
            .expect_instr(8, Instruction::LoadInteger(SymbolKey::from("iter"), lc(1, 5)))
            .expect_instr(9, Instruction::PushInteger(1, lc(1, 18)))
            .expect_instr(10, Instruction::AddIntegers(lc(1, 14)))
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
            .expect_instr(0, Instruction::LoadInteger(SymbolKey::from("i"), lc(1, 12)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("iter")))
            .expect_instr(2, Instruction::LoadInteger(SymbolKey::from("iter"), lc(1, 5)))
            .expect_instr(3, Instruction::LoadInteger(SymbolKey::from("j"), lc(1, 17)))
            .expect_instr(4, Instruction::LessEqualIntegers(lc(1, 14)))
            .expect_instr(5, Instruction::JumpIfNotTrue(13))
            .expect_instr(6, Instruction::PushBoolean(false, lc(1, 24)))
            .expect_instr(7, Instruction::Assign(SymbolKey::from("a")))
            .expect_instr(8, Instruction::LoadInteger(SymbolKey::from("iter"), lc(1, 5)))
            .expect_instr(9, Instruction::PushInteger(1, lc(1, 18)))
            .expect_instr(10, Instruction::AddIntegers(lc(1, 14)))
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
            .expect_instr(0, Instruction::LoadInteger(SymbolKey::from("i"), lc(1, 13)))
            .expect_instr(1, Instruction::PushInteger(1, lc(1, 17)))
            .expect_instr(2, Instruction::AddIntegers(lc(1, 15)))
            .expect_instr(3, Instruction::Assign(SymbolKey::from("iter")))
            .expect_instr(4, Instruction::LoadInteger(SymbolKey::from("iter"), lc(1, 5)))
            .expect_instr(5, Instruction::PushInteger(2, lc(1, 24)))
            .expect_instr(6, Instruction::LoadInteger(SymbolKey::from("j"), lc(1, 28)))
            .expect_instr(7, Instruction::AddIntegers(lc(1, 26)))
            .expect_instr(8, Instruction::LessEqualIntegers(lc(1, 20)))
            .expect_instr(9, Instruction::JumpIfNotTrue(17))
            .expect_instr(10, Instruction::PushBoolean(false, lc(1, 36)))
            .expect_instr(11, Instruction::Assign(SymbolKey::from("a")))
            .expect_instr(12, Instruction::LoadInteger(SymbolKey::from("iter"), lc(1, 5)))
            .expect_instr(13, Instruction::PushInteger(1, lc(1, 30)))
            .expect_instr(14, Instruction::AddIntegers(lc(1, 20)))
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
                Instruction::JumpIfDefined(JumpIfDefinedISpan {
                    var: SymbolKey::from("iter"),
                    addr: 2,
                }),
            )
            .expect_instr(
                1,
                Instruction::Dim(DimISpan {
                    name: SymbolKey::from("iter"),
                    shared: false,
                    vtype: ExprType::Double,
                }),
            )
            .expect_instr(2, Instruction::PushInteger(0, lc(1, 12)))
            .expect_instr(3, Instruction::IntegerToDouble)
            .expect_instr(4, Instruction::Assign(SymbolKey::from("iter")))
            .expect_instr(5, Instruction::LoadDouble(SymbolKey::from("iter"), lc(1, 5)))
            .expect_instr(6, Instruction::PushInteger(2, lc(1, 17)))
            .expect_instr(7, Instruction::IntegerToDouble)
            .expect_instr(8, Instruction::LessEqualDoubles(lc(1, 14)))
            .expect_instr(9, Instruction::JumpIfNotTrue(15))
            .expect_instr(10, Instruction::LoadDouble(SymbolKey::from("iter"), lc(1, 5)))
            .expect_instr(11, Instruction::PushDouble(0.1, lc(1, 24)))
            .expect_instr(12, Instruction::AddDoubles(lc(1, 14)))
            .expect_instr(13, Instruction::Assign(SymbolKey::from("iter")))
            .expect_instr(14, Instruction::Jump(JumpISpan { addr: 5 }))
            .check();
    }

    #[test]
    fn test_compile_function_and_nothing_else() {
        Tester::default()
            .parse("FUNCTION foo: a = 3: END FUNCTION")
            .compile()
            .expect_instr(0, Instruction::Jump(JumpISpan { addr: 8 }))
            .expect_instr(1, Instruction::EnterScope)
            .expect_instr(
                2,
                Instruction::Dim(DimISpan {
                    name: SymbolKey::from("0return_foo"),
                    shared: false,
                    vtype: ExprType::Integer,
                }),
            )
            .expect_instr(3, Instruction::PushInteger(3, lc(1, 19)))
            .expect_instr(4, Instruction::Assign(SymbolKey::from("a")))
            .expect_instr(5, Instruction::LoadInteger(SymbolKey::from("0return_foo"), lc(1, 22)))
            .expect_instr(6, Instruction::LeaveScope)
            .expect_instr(7, Instruction::Return(lc(1, 22)))
            .expect_symtable(
                SymbolKey::from("foo"),
                SymbolPrototype::Callable(
                    CallableMetadataBuilder::new("USER DEFINED FUNCTION")
                        .with_syntax(&[(&[], None)])
                        .with_category("User defined")
                        .with_description("User defined function")
                        .build(),
                ),
            )
            .check();
    }

    #[test]
    fn test_compile_function_defined_between_code() {
        Tester::default()
            .parse("before = 1: FUNCTION foo: END FUNCTION: after = 2")
            .compile()
            .expect_instr(0, Instruction::PushInteger(1, lc(1, 10)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("before")))
            .expect_instr(2, Instruction::PushInteger(2, lc(1, 49)))
            .expect_instr(3, Instruction::Assign(SymbolKey::from("after")))
            .expect_instr(4, Instruction::Jump(JumpISpan { addr: 10 }))
            .expect_instr(5, Instruction::EnterScope)
            .expect_instr(
                6,
                Instruction::Dim(DimISpan {
                    name: SymbolKey::from("0return_foo"),
                    shared: false,
                    vtype: ExprType::Integer,
                }),
            )
            .expect_instr(7, Instruction::LoadInteger(SymbolKey::from("0return_foo"), lc(1, 27)))
            .expect_instr(8, Instruction::LeaveScope)
            .expect_instr(9, Instruction::Return(lc(1, 27)))
            .expect_symtable(
                SymbolKey::from("foo"),
                SymbolPrototype::Callable(
                    CallableMetadataBuilder::new("USER DEFINED FUNCTION")
                        .with_syntax(&[(&[], None)])
                        .with_category("User defined")
                        .with_description("User defined function")
                        .build(),
                ),
            )
            .check();
    }

    #[test]
    fn test_compile_function_redefined_was_variable() {
        Tester::default()
            .parse("a = 1: FUNCTION a: END FUNCTION")
            .compile()
            .expect_err("1:17: Cannot define already-defined symbol a%")
            .check();
    }

    #[test]
    fn test_compile_function_redefined_was_function() {
        Tester::default()
            .parse("FUNCTION a: END FUNCTION: FUNCTION A: END FUNCTION")
            .compile()
            .expect_err("1:36: Cannot define already-defined symbol A%")
            .check();
    }

    #[test]
    fn test_compile_function_redefined_was_sub() {
        Tester::default()
            .parse("SUB a: END SUB: FUNCTION A: END FUNCTION")
            .compile()
            .expect_err("1:26: Cannot define already-defined symbol A%")
            .check();
    }

    #[test]
    fn test_compile_sub_redefined_was_variable() {
        Tester::default()
            .parse("a = 1: SUB a: END SUB")
            .compile()
            .expect_err("1:12: Cannot define already-defined symbol a")
            .check();
    }

    #[test]
    fn test_compile_sub_redefined_was_function() {
        Tester::default()
            .parse("FUNCTION a: END FUNCTION: SUB A: END SUB")
            .compile()
            .expect_err("1:31: Cannot define already-defined symbol A")
            .check();
    }

    #[test]
    fn test_compile_sub_redefined_was_sub() {
        Tester::default()
            .parse("SUB a: END SUB: SUB A: END SUB")
            .compile()
            .expect_err("1:21: Cannot define already-defined symbol A")
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
            .define_callable(CallableMetadataBuilder::new("FOO"))
            .parse("@sub\nFOO\nRETURN\nGOSUB @sub")
            .compile()
            .expect_instr(0, Instruction::BuiltinCall(SymbolKey::from("FOO"), lc(2, 1), 0))
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
            .define_callable(CallableMetadataBuilder::new("FOO"))
            .parse("IF FALSE THEN: FOO: END IF")
            .compile()
            .expect_instr(0, Instruction::PushBoolean(false, lc(1, 4)))
            .expect_instr(1, Instruction::JumpIfNotTrue(3))
            .expect_instr(2, Instruction::BuiltinCall(SymbolKey::from("FOO"), lc(1, 16), 0))
            .check();
    }

    #[test]
    fn test_compile_if_many_branches() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("FOO"))
            .define_callable(CallableMetadataBuilder::new("BAR"))
            .define_callable(CallableMetadataBuilder::new("BAZ"))
            .parse("IF FALSE THEN\nFOO\nELSEIF TRUE THEN\nBAR\nELSE\nBAZ\nEND IF")
            .compile()
            .expect_instr(0, Instruction::PushBoolean(false, lc(1, 4)))
            .expect_instr(1, Instruction::JumpIfNotTrue(4))
            .expect_instr(2, Instruction::BuiltinCall(SymbolKey::from("FOO"), lc(2, 1), 0))
            .expect_instr(3, Instruction::Jump(JumpISpan { addr: 11 }))
            .expect_instr(4, Instruction::PushBoolean(true, lc(3, 8)))
            .expect_instr(5, Instruction::JumpIfNotTrue(8))
            .expect_instr(6, Instruction::BuiltinCall(SymbolKey::from("BAR"), lc(4, 1), 0))
            .expect_instr(7, Instruction::Jump(JumpISpan { addr: 11 }))
            .expect_instr(8, Instruction::PushBoolean(true, lc(5, 1)))
            .expect_instr(9, Instruction::JumpIfNotTrue(11))
            .expect_instr(10, Instruction::BuiltinCall(SymbolKey::from("BAZ"), lc(6, 1), 0))
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
            .define_callable(CallableMetadataBuilder::new("FOO"))
            .parse(&format!("SELECT CASE 5\nCASE {}\nFOO\nEND SELECT", guards))
            .compile()
            .expect_instr(0, Instruction::PushInteger(5, lc(1, 13)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("0select1")));
        let mut n = 2;
        for instr in exp_expr_instrs {
            t = t.expect_instr(n, instr);
            n += 1;
        }
        t.expect_instr(n, Instruction::JumpIfNotTrue(n + 2))
            .expect_instr(n + 1, Instruction::BuiltinCall(SymbolKey::from("FOO"), lc(3, 1), 0))
            .expect_instr(
                n + 2,
                Instruction::Unset(UnsetISpan { name: SymbolKey::from("0select1"), pos: lc(4, 1) }),
            )
            .check();
    }

    #[test]
    fn test_compile_case_guards_equals() {
        do_compile_case_guard_test(
            "1 + 2",
            vec![
                Instruction::LoadInteger(SymbolKey::from("0select1"), lc(2, 6)),
                Instruction::PushInteger(1, lc(2, 6)),
                Instruction::PushInteger(2, lc(2, 10)),
                Instruction::AddIntegers(lc(2, 8)),
                Instruction::EqualIntegers(lc(2, 6)),
            ],
        );
    }

    #[test]
    fn test_compile_case_guards_is() {
        do_compile_case_guard_test(
            "IS = 9 + 8",
            vec![
                Instruction::LoadInteger(SymbolKey::from("0select1"), lc(2, 11)),
                Instruction::PushInteger(9, lc(2, 11)),
                Instruction::PushInteger(8, lc(2, 15)),
                Instruction::AddIntegers(lc(2, 13)),
                Instruction::EqualIntegers(lc(2, 11)),
            ],
        );

        do_compile_case_guard_test(
            "IS <> 9",
            vec![
                Instruction::LoadInteger(SymbolKey::from("0select1"), lc(2, 12)),
                Instruction::PushInteger(9, lc(2, 12)),
                Instruction::NotEqualIntegers(lc(2, 12)),
            ],
        );

        do_compile_case_guard_test(
            "IS < 9",
            vec![
                Instruction::LoadInteger(SymbolKey::from("0select1"), lc(2, 11)),
                Instruction::PushInteger(9, lc(2, 11)),
                Instruction::LessIntegers(lc(2, 11)),
            ],
        );

        do_compile_case_guard_test(
            "IS <= 9",
            vec![
                Instruction::LoadInteger(SymbolKey::from("0select1"), lc(2, 12)),
                Instruction::PushInteger(9, lc(2, 12)),
                Instruction::LessEqualIntegers(lc(2, 12)),
            ],
        );

        do_compile_case_guard_test(
            "IS > 9",
            vec![
                Instruction::LoadInteger(SymbolKey::from("0select1"), lc(2, 11)),
                Instruction::PushInteger(9, lc(2, 11)),
                Instruction::GreaterIntegers(lc(2, 11)),
            ],
        );

        do_compile_case_guard_test(
            "IS >= 9",
            vec![
                Instruction::LoadInteger(SymbolKey::from("0select1"), lc(2, 12)),
                Instruction::PushInteger(9, lc(2, 12)),
                Instruction::GreaterEqualIntegers(lc(2, 12)),
            ],
        );
    }

    #[test]
    fn test_compile_case_guards_to() {
        do_compile_case_guard_test(
            "1 TO 2",
            vec![
                Instruction::LoadInteger(SymbolKey::from("0select1"), lc(2, 6)),
                Instruction::PushInteger(1, lc(2, 6)),
                Instruction::GreaterEqualIntegers(lc(2, 6)),
                Instruction::LoadInteger(SymbolKey::from("0select1"), lc(2, 6)),
                Instruction::PushInteger(2, lc(2, 11)),
                Instruction::LessEqualIntegers(lc(2, 11)),
                Instruction::LogicalAnd(lc(2, 6)),
            ],
        );
    }

    #[test]
    fn test_compile_case_guards_many() {
        do_compile_case_guard_test(
            "IS <> 9, 8",
            vec![
                Instruction::LoadInteger(SymbolKey::from("0select1"), lc(2, 12)),
                Instruction::PushInteger(9, lc(2, 12)),
                Instruction::NotEqualIntegers(lc(2, 12)),
                Instruction::LoadInteger(SymbolKey::from("0select1"), lc(2, 15)),
                Instruction::PushInteger(8, lc(2, 15)),
                Instruction::EqualIntegers(lc(2, 15)),
                Instruction::LogicalOr(lc(2, 12)),
            ],
        );
    }

    #[test]
    fn test_compile_select_no_cases() {
        Tester::default()
            .parse("SELECT CASE 5 + 3: END SELECT")
            .compile()
            .expect_instr(0, Instruction::PushInteger(5, lc(1, 13)))
            .expect_instr(1, Instruction::PushInteger(3, lc(1, 17)))
            .expect_instr(2, Instruction::AddIntegers(lc(1, 15)))
            .expect_instr(3, Instruction::Assign(SymbolKey::from("0select1")))
            .expect_instr(
                4,
                Instruction::Unset(UnsetISpan {
                    name: SymbolKey::from("0select1"),
                    pos: lc(1, 20),
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_select_one_case() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("FOO"))
            .parse("SELECT CASE 5\nCASE 7\nFOO\nEND SELECT")
            .compile()
            .expect_instr(0, Instruction::PushInteger(5, lc(1, 13)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("0select1")))
            .expect_instr(2, Instruction::LoadInteger(SymbolKey::from("0select1"), lc(2, 6)))
            .expect_instr(3, Instruction::PushInteger(7, lc(2, 6)))
            .expect_instr(4, Instruction::EqualIntegers(lc(2, 6)))
            .expect_instr(5, Instruction::JumpIfNotTrue(7))
            .expect_instr(6, Instruction::BuiltinCall(SymbolKey::from("FOO"), lc(3, 1), 0))
            .expect_instr(
                7,
                Instruction::Unset(UnsetISpan { name: SymbolKey::from("0select1"), pos: lc(4, 1) }),
            )
            .check();
    }

    #[test]
    fn test_compile_select_one_case_varref_is_evaluated() {
        Tester::default()
            .define("i", SymbolPrototype::Variable(ExprType::Integer))
            .parse("SELECT CASE i: END SELECT")
            .compile()
            .expect_instr(0, Instruction::LoadInteger(SymbolKey::from("i"), lc(1, 13)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("0select1")))
            .expect_instr(
                2,
                Instruction::Unset(UnsetISpan {
                    name: SymbolKey::from("0select1"),
                    pos: lc(1, 16),
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_select_only_case_else() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("FOO"))
            .parse("SELECT CASE 5\nCASE ELSE\nFOO\nEND SELECT")
            .compile()
            .expect_instr(0, Instruction::PushInteger(5, lc(1, 13)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("0select1")))
            .expect_instr(2, Instruction::BuiltinCall(SymbolKey::from("FOO"), lc(3, 1), 0))
            .expect_instr(
                3,
                Instruction::Unset(UnsetISpan { name: SymbolKey::from("0select1"), pos: lc(4, 1) }),
            )
            .check();
    }

    #[test]
    fn test_compile_select_many_cases_without_else() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("FOO"))
            .define_callable(CallableMetadataBuilder::new("BAR"))
            .parse("SELECT CASE 5\nCASE 7\nFOO\nCASE IS <> 8\nBAR\nEND SELECT")
            .compile()
            .expect_instr(0, Instruction::PushInteger(5, lc(1, 13)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("0select1")))
            .expect_instr(2, Instruction::LoadInteger(SymbolKey::from("0select1"), lc(2, 6)))
            .expect_instr(3, Instruction::PushInteger(7, lc(2, 6)))
            .expect_instr(4, Instruction::EqualIntegers(lc(2, 6)))
            .expect_instr(5, Instruction::JumpIfNotTrue(8))
            .expect_instr(6, Instruction::BuiltinCall(SymbolKey::from("FOO"), lc(3, 1), 0))
            .expect_instr(7, Instruction::Jump(JumpISpan { addr: 13 }))
            .expect_instr(8, Instruction::LoadInteger(SymbolKey::from("0select1"), lc(4, 12)))
            .expect_instr(9, Instruction::PushInteger(8, lc(4, 12)))
            .expect_instr(10, Instruction::NotEqualIntegers(lc(4, 12)))
            .expect_instr(11, Instruction::JumpIfNotTrue(13))
            .expect_instr(12, Instruction::BuiltinCall(SymbolKey::from("BAR"), lc(5, 1), 0))
            .expect_instr(
                13,
                Instruction::Unset(UnsetISpan { name: SymbolKey::from("0select1"), pos: lc(6, 1) }),
            )
            .check();
    }

    #[test]
    fn test_compile_select_many_cases_with_else() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("FOO"))
            .define_callable(CallableMetadataBuilder::new("BAR"))
            .parse("SELECT CASE 5\nCASE 7\nFOO\nCASE ELSE\nBAR\nEND SELECT")
            .compile()
            .expect_instr(0, Instruction::PushInteger(5, lc(1, 13)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("0select1")))
            .expect_instr(2, Instruction::LoadInteger(SymbolKey::from("0select1"), lc(2, 6)))
            .expect_instr(3, Instruction::PushInteger(7, lc(2, 6)))
            .expect_instr(4, Instruction::EqualIntegers(lc(2, 6)))
            .expect_instr(5, Instruction::JumpIfNotTrue(8))
            .expect_instr(6, Instruction::BuiltinCall(SymbolKey::from("FOO"), lc(3, 1), 0))
            .expect_instr(7, Instruction::Jump(JumpISpan { addr: 9 }))
            .expect_instr(8, Instruction::BuiltinCall(SymbolKey::from("BAR"), lc(5, 1), 0))
            .expect_instr(
                9,
                Instruction::Unset(UnsetISpan { name: SymbolKey::from("0select1"), pos: lc(6, 1) }),
            )
            .check();
    }

    #[test]
    fn test_compile_select_internal_var_names() {
        Tester::default()
            .parse("SELECT CASE 0: END SELECT\nSELECT CASE 0: END SELECT")
            .compile()
            .expect_instr(0, Instruction::PushInteger(0, lc(1, 13)))
            .expect_instr(1, Instruction::Assign(SymbolKey::from("0select1")))
            .expect_instr(
                2,
                Instruction::Unset(UnsetISpan {
                    name: SymbolKey::from("0select1"),
                    pos: lc(1, 16),
                }),
            )
            .expect_instr(3, Instruction::PushInteger(0, lc(2, 13)))
            .expect_instr(4, Instruction::Assign(SymbolKey::from("0select2")))
            .expect_instr(
                5,
                Instruction::Unset(UnsetISpan {
                    name: SymbolKey::from("0select2"),
                    pos: lc(2, 16),
                }),
            )
            .check();
    }

    #[test]
    fn test_compile_while() {
        Tester::default()
            .define_callable(CallableMetadataBuilder::new("FOO"))
            .parse("WHILE TRUE\nFOO\nWEND")
            .compile()
            .expect_instr(0, Instruction::PushBoolean(true, lc(1, 7)))
            .expect_instr(1, Instruction::JumpIfNotTrue(4))
            .expect_instr(2, Instruction::BuiltinCall(SymbolKey::from("FOO"), lc(2, 1), 0))
            .expect_instr(3, Instruction::Jump(JumpISpan { addr: 0 }))
            .check();
    }
}
