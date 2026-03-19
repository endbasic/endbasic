// EndBASIC
// Copyright 2026 Julio Merino
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

//! Entry point to the compilation, handling top-level definitions.

use crate::ast::{
    ArgSep, AssignmentSpan, CallableSpan, CaseGuardSpan, CaseRelOp, DoGuard, DoSpan, Expr,
    ExprType, ForSpan, IfSpan, OnErrorSpan, SelectSpan, Statement, VarRef, WhileSpan,
};
use crate::bytecode::{self, ErrorHandlerMode, PackedArrayType, Register, RegisterScope};
use crate::callable::{ArgSepSyntax, CallableMetadata, RequiredValueSyntax, SingularArgSyntax};
use crate::compiler::args::{compile_args, define_new_args};
use crate::compiler::codegen::{Codegen, Fixup};
use crate::compiler::exprs::{compile_expr, compile_expr_as_type, compile_integer_exprs};
use crate::compiler::syms::{
    self, GlobalSymtable, LocalSymtable, SymbolKey, SymbolPrototype, TempSymtable,
};
use crate::compiler::{Error, Result};
use crate::image::{GlobalVarInfo, Image};
use crate::mem::ConstantDatum;
use crate::reader::LineCol;
use crate::{Callable, CallableMetadataBuilder, parser};
use std::borrow::Cow;
use std::cmp::max;
use std::collections::HashMap;
use std::io;
use std::iter::Iterator;
use std::rc::Rc;

/// Kind of a user-defined callable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CallableKind {
    /// A function definition.
    Function,

    /// A subroutine definition.
    Sub,
}

/// Bag of state required by various top-level compilation functions.
///
/// This type exists to minimize the number of complex arguments passed across functions.
/// If possible, avoid passing it and instead pass the minimum set of required fields.
#[derive(Default)]
struct Context {
    /// The code generator accumulating bytecode instructions.
    codegen: Codegen,

    /// Collection of user-defined callable definitions to be compiled after the main scope.
    user_callables: Vec<CallableSpan>,

    /// Collection of `DATA` values captured while compiling all statements.
    data: Vec<Option<ConstantDatum>>,

    /// Stack of pending `EXIT DO` jumps for each nested `DO` loop.
    do_exit_stack: Vec<Vec<(usize, LineCol)>>,

    /// Stack of pending `EXIT FOR` jumps for each nested `FOR` loop.
    for_exit_stack: Vec<Vec<(usize, LineCol)>>,

    /// Kind of the callable currently being compiled, if any.
    current_callable: Option<CallableKind>,

    /// List of pending `EXIT FUNCTION` or `EXIT SUB` jumps in the current callable.
    callable_exit_jumps: Vec<(usize, LineCol)>,
}

/// Converts parser-validated `DATA` expressions into image data constants.
fn data_expr_to_constant(expr: Expr) -> ConstantDatum {
    match expr {
        Expr::Boolean(span) => ConstantDatum::Boolean(span.value),
        Expr::Double(span) => ConstantDatum::Double(span.value),
        Expr::Integer(span) => ConstantDatum::Integer(span.value),
        Expr::Text(span) => ConstantDatum::Text(span.value),
        _ => unreachable!("Parser guarantees DATA only contains literal values"),
    }
}

/// Returns a statically-known `END` exit code and its source position, if any.
fn static_end_code(expr: &Expr) -> Option<(i32, LineCol)> {
    match expr {
        Expr::Integer(span) => Some((span.value, span.pos)),
        Expr::Negate(span) => {
            let Expr::Integer(inner) = &span.expr else {
                return None;
            };
            inner.value.checked_neg().map(|value| (value, span.pos))
        }
        _ => None,
    }
}

/// Compiles an assignment statement `span` into the `codegen` block.
fn compile_assignment(
    codegen: &mut Codegen,
    symtable: &mut LocalSymtable<'_, '_, '_, '_>,
    span: AssignmentSpan,
) -> Result<()> {
    let vref_pos = span.vref_pos;

    let (reg, etype) = match symtable.get_local_or_global(&span.vref) {
        Ok((_, SymbolPrototype::Array(_))) => {
            return Err(Error::ArrayUsedAsScalar(vref_pos, span.vref));
        }

        Ok((reg, SymbolPrototype::Scalar(etype))) => (reg, Some(etype)),

        Err(syms::Error::UndefinedSymbol(..)) => {
            let key = SymbolKey::from(span.vref.name.clone());
            if symtable.get_callable(&key).is_some() {
                return Err(Error::from_syms(
                    syms::Error::AlreadyDefined(span.vref.clone()),
                    span.vref_pos,
                ));
            }
            let reg = symtable
                .put_local(
                    key,
                    SymbolPrototype::Scalar(span.vref.ref_type.unwrap_or(ExprType::Integer)),
                )
                .map_err(|e| Error::from_syms(e, span.vref_pos))?;
            match span.vref.ref_type {
                Some(etype) => (reg, Some(etype)),
                None => (reg, None),
            }
        }

        Err(e) => return Err(Error::from_syms(e, vref_pos)),
    };

    if let Some(etype) = etype {
        // The destination variable already exists.  Try to compile the expression into its target
        // type and fail otherwise with a better error message.
        match compile_expr_as_type(codegen, &mut symtable.frozen(), reg, span.expr, etype) {
            Err(Error::TypeMismatch(pos, actual, expected)) => {
                return Err(Error::IncompatibleTypesInAssignment(pos, actual, expected));
            }
            r => return r,
        }
    }

    // The destination variable doesn't exist yet but `symtable.put_local` already inserted it
    // with the default type we gave above as part of assigning it a register.  Use the
    // expression's type to fix up the type in the symbols table.
    let etype = compile_expr(codegen, &mut symtable.frozen(), reg, span.expr)?;
    symtable.fixup_local_type(&span.vref, etype).map_err(|e| Error::from_syms(e, vref_pos))
}

/// Returns the textual name of `relop` for diagnostics.
fn case_relop_name(relop: &CaseRelOp) -> &'static str {
    match relop {
        CaseRelOp::Equal => "=",
        CaseRelOp::NotEqual => "<>",
        CaseRelOp::Less => "<",
        CaseRelOp::LessEqual => "<=",
        CaseRelOp::Greater => ">",
        CaseRelOp::GreaterEqual => ">=",
    }
}

/// Returns the bytecode opcode constructor for `relop` and operands of type `etype`.
fn case_relop_instr(
    relop: &CaseRelOp,
    etype: ExprType,
) -> Option<fn(Register, Register, Register) -> u32> {
    match etype {
        ExprType::Boolean => match relop {
            CaseRelOp::Equal => Some(bytecode::make_equal_boolean),
            CaseRelOp::NotEqual => Some(bytecode::make_not_equal_boolean),
            CaseRelOp::Less
            | CaseRelOp::LessEqual
            | CaseRelOp::Greater
            | CaseRelOp::GreaterEqual => None,
        },

        ExprType::Double => match relop {
            CaseRelOp::Equal => Some(bytecode::make_equal_double),
            CaseRelOp::NotEqual => Some(bytecode::make_not_equal_double),
            CaseRelOp::Less => Some(bytecode::make_less_double),
            CaseRelOp::LessEqual => Some(bytecode::make_less_equal_double),
            CaseRelOp::Greater => Some(bytecode::make_greater_double),
            CaseRelOp::GreaterEqual => Some(bytecode::make_greater_equal_double),
        },

        ExprType::Integer => match relop {
            CaseRelOp::Equal => Some(bytecode::make_equal_integer),
            CaseRelOp::NotEqual => Some(bytecode::make_not_equal_integer),
            CaseRelOp::Less => Some(bytecode::make_less_integer),
            CaseRelOp::LessEqual => Some(bytecode::make_less_equal_integer),
            CaseRelOp::Greater => Some(bytecode::make_greater_integer),
            CaseRelOp::GreaterEqual => Some(bytecode::make_greater_equal_integer),
        },

        ExprType::Text => match relop {
            CaseRelOp::Equal => Some(bytecode::make_equal_text),
            CaseRelOp::NotEqual => Some(bytecode::make_not_equal_text),
            CaseRelOp::Less => Some(bytecode::make_less_text),
            CaseRelOp::LessEqual => Some(bytecode::make_less_equal_text),
            CaseRelOp::Greater => Some(bytecode::make_greater_text),
            CaseRelOp::GreaterEqual => Some(bytecode::make_greater_equal_text),
        },
    }
}

/// Compiles a comparison between `test` and `rhs`, leaving the boolean result in `dest`.
fn compile_case_relop(
    ctx: &mut Context,
    pos: LineCol,
    test: (Register, ExprType),
    rhs: (Register, ExprType),
    relop: CaseRelOp,
    dest: Register,
) -> Result<()> {
    let (test_reg, test_type) = test;
    let (rhs_reg, rhs_type) = rhs;
    let op_name = case_relop_name(&relop);
    let opcode = match (test_type, rhs_type) {
        (ExprType::Double, ExprType::Integer) => {
            ctx.codegen.emit(bytecode::make_integer_to_double(rhs_reg), pos);
            case_relop_instr(&relop, ExprType::Double)
        }

        (ExprType::Integer, ExprType::Double) => {
            ctx.codegen.emit(bytecode::make_integer_to_double(test_reg), pos);
            case_relop_instr(&relop, ExprType::Double)
        }

        (lhs, rhs) if lhs == rhs => case_relop_instr(&relop, lhs),
        _ => None,
    };

    match opcode {
        Some(opcode) => {
            ctx.codegen.emit(opcode(dest, test_reg, rhs_reg), pos);
            Ok(())
        }
        None => Err(Error::BinaryOpType(pos, op_name, test_type, rhs_type)),
    }
}

/// Compiles one `CASE` guard and returns the register and source position of its boolean result.
fn compile_case_guard(
    ctx: &mut Context,
    symtable: &mut TempSymtable<'_, '_, '_, '_, '_>,
    test_reg: Register,
    test_type: ExprType,
    guard: CaseGuardSpan,
) -> Result<(Register, LineCol)> {
    match guard {
        CaseGuardSpan::Is(relop, expr) => {
            let pos = expr.start_pos();

            let mut scope = symtable.temp_scope();
            let lhs_reg = scope.alloc().map_err(|e| Error::from_syms(e, pos))?;
            let rhs_reg = scope.alloc().map_err(|e| Error::from_syms(e, pos))?;
            let cond_reg = scope.alloc().map_err(|e| Error::from_syms(e, pos))?;

            ctx.codegen.emit(bytecode::make_move(lhs_reg, test_reg), pos);
            let rhs_type = compile_expr(&mut ctx.codegen, symtable, rhs_reg, expr)?;
            compile_case_relop(
                ctx,
                pos,
                (lhs_reg, test_type),
                (rhs_reg, rhs_type),
                relop,
                cond_reg,
            )?;

            Ok((cond_reg, pos))
        }

        CaseGuardSpan::To(from_expr, to_expr) => {
            let pos = from_expr.start_pos();

            let mut scope = symtable.temp_scope();
            let lhs_from_reg = scope.alloc().map_err(|e| Error::from_syms(e, pos))?;
            let rhs_from_reg = scope.alloc().map_err(|e| Error::from_syms(e, pos))?;
            let cond_from_reg = scope.alloc().map_err(|e| Error::from_syms(e, pos))?;

            let lhs_to_reg = scope.alloc().map_err(|e| Error::from_syms(e, pos))?;
            let rhs_to_reg = scope.alloc().map_err(|e| Error::from_syms(e, pos))?;
            let cond_to_reg = scope.alloc().map_err(|e| Error::from_syms(e, pos))?;

            let cond_reg = scope.alloc().map_err(|e| Error::from_syms(e, pos))?;

            ctx.codegen.emit(bytecode::make_move(lhs_from_reg, test_reg), pos);
            let rhs_from_type = compile_expr(&mut ctx.codegen, symtable, rhs_from_reg, from_expr)?;
            compile_case_relop(
                ctx,
                pos,
                (lhs_from_reg, test_type),
                (rhs_from_reg, rhs_from_type),
                CaseRelOp::GreaterEqual,
                cond_from_reg,
            )?;

            ctx.codegen.emit(bytecode::make_move(lhs_to_reg, test_reg), pos);
            let rhs_to_type = compile_expr(&mut ctx.codegen, symtable, rhs_to_reg, to_expr)?;
            compile_case_relop(
                ctx,
                pos,
                (lhs_to_reg, test_type),
                (rhs_to_reg, rhs_to_type),
                CaseRelOp::LessEqual,
                cond_to_reg,
            )?;

            ctx.codegen.emit(bytecode::make_bitwise_and(cond_reg, cond_from_reg, cond_to_reg), pos);
            Ok((cond_reg, pos))
        }
    }
}

/// Compiles a `SELECT` statement and emits bytecode into `ctx`.
fn compile_select(
    ctx: &mut Context,
    symtable: &mut LocalSymtable<'_, '_, '_, '_>,
    span: SelectSpan,
) -> Result<()> {
    let end_pos = span.end_pos;
    let ncases = span.cases.len();
    let select_cases = span.cases;
    let select_expr = span.expr;
    let select_expr_pos = select_expr.start_pos();

    /// Captures the data needed to materialize a `CASE` body after dispatch generation.
    struct PendingCase {
        body: Vec<Statement>,
        body_jump_pcs: Vec<(usize, LineCol)>,
        has_next_case: bool,
    }

    let mut pending_cases = Vec::with_capacity(ncases);
    let mut pending_next_case_jump: Option<(usize, LineCol)> = None;

    symtable.with_reserved_temp(
        |e| Error::from_syms(e, select_expr_pos),
        |test_reg, frozen| {
            let test_type = compile_expr(&mut ctx.codegen, frozen, test_reg, select_expr)?;

            for (i, case) in select_cases.into_iter().enumerate() {
                let has_next_case = i < ncases - 1;
                let mut body_jump_pcs = vec![];
                let case_dispatch_addr = ctx.codegen.next_pc();
                if let Some((jump_pc, pos)) = pending_next_case_jump.take() {
                    let target = u16::try_from(case_dispatch_addr)
                        .map_err(|_| Error::TargetTooFar(pos, case_dispatch_addr))?;
                    ctx.codegen.patch(jump_pc, bytecode::make_jump(target));
                }

                if case.guards.is_empty() {
                    let jump_body_pc = ctx.codegen.emit(bytecode::make_nop(), end_pos);
                    body_jump_pcs.push((jump_body_pc, end_pos));
                } else {
                    for guard in case.guards {
                        let (cond_reg, pos) =
                            compile_case_guard(ctx, frozen, test_reg, test_type, guard)?;
                        let jump_next_guard_pc = ctx.codegen.emit(bytecode::make_nop(), pos);
                        let jump_body_pc = ctx.codegen.emit(bytecode::make_nop(), pos);
                        body_jump_pcs.push((jump_body_pc, pos));

                        let next_addr = ctx.codegen.next_pc();
                        let target = u16::try_from(next_addr)
                            .map_err(|_| Error::TargetTooFar(pos, next_addr))?;
                        ctx.codegen.patch(
                            jump_next_guard_pc,
                            bytecode::make_jump_if_false(cond_reg, target),
                        );
                    }

                    let jump_next_case_pc = ctx.codegen.emit(bytecode::make_nop(), end_pos);
                    pending_next_case_jump = Some((jump_next_case_pc, end_pos));
                }

                pending_cases.push(PendingCase { body: case.body, body_jump_pcs, has_next_case });
            }

            Ok(())
        },
    )?;

    let dispatch_end_jump_pc = ctx.codegen.emit(bytecode::make_nop(), end_pos);
    if let Some((jump_pc, pos)) = pending_next_case_jump {
        let target = u16::try_from(dispatch_end_jump_pc)
            .map_err(|_| Error::TargetTooFar(pos, dispatch_end_jump_pc))?;
        ctx.codegen.patch(jump_pc, bytecode::make_jump(target));
    }

    let mut end_jumps = vec![];
    for case in pending_cases {
        let body_addr = ctx.codegen.next_pc();
        for (jump_body_pc, pos) in case.body_jump_pcs {
            let target =
                u16::try_from(body_addr).map_err(|_| Error::TargetTooFar(pos, body_addr))?;
            ctx.codegen.patch(jump_body_pc, bytecode::make_jump(target));
        }

        for stmt in case.body {
            compile_stmt(ctx, symtable, stmt)?;
        }

        if case.has_next_case {
            end_jumps.push(ctx.codegen.emit(bytecode::make_nop(), end_pos));
        }
    }

    let end_addr = ctx.codegen.next_pc();
    let end_target = u16::try_from(end_addr).map_err(|_| Error::TargetTooFar(end_pos, end_addr))?;
    ctx.codegen.patch(dispatch_end_jump_pc, bytecode::make_jump(end_target));
    for end_jump in end_jumps {
        ctx.codegen.patch(end_jump, bytecode::make_jump(end_target));
    }

    Ok(())
}

/// Compiles a `DO` loop and emits bytecode into `ctx`.
fn compile_do(
    ctx: &mut Context,
    symtable: &mut LocalSymtable<'_, '_, '_, '_>,
    span: DoSpan,
) -> Result<()> {
    /// Compiles one loop guard expression to a temporary boolean register.
    fn compile_guard(
        ctx: &mut Context,
        symtable: &mut LocalSymtable<'_, '_, '_, '_>,
        guard: Expr,
    ) -> Result<(Register, LineCol)> {
        let guard_pos = guard.start_pos();
        let mut frozen = symtable.frozen();
        let mut scope = frozen.temp_scope();
        let reg = scope.alloc().map_err(|e| Error::from_syms(e, guard_pos))?;
        compile_expr_as_type(&mut ctx.codegen, &mut frozen, reg, guard, ExprType::Boolean)?;
        Ok((reg, guard_pos))
    }

    ctx.do_exit_stack.push(vec![]);

    let end_addr = match span.guard {
        DoGuard::Infinite => {
            let start_pc = ctx.codegen.next_pc();
            for stmt in span.body {
                compile_stmt(ctx, symtable, stmt)?;
            }
            let end_pos = LineCol { line: 0, col: 0 };
            let target =
                u16::try_from(start_pc).map_err(|_| Error::TargetTooFar(end_pos, start_pc))?;
            ctx.codegen.emit(bytecode::make_jump(target), end_pos);
            ctx.codegen.next_pc()
        }

        DoGuard::PreUntil(guard) => {
            let start_pc = ctx.codegen.next_pc();
            let (cond_reg, guard_pos) = compile_guard(ctx, symtable, guard)?;
            let jump_body_pc = ctx.codegen.emit(bytecode::make_nop(), guard_pos);
            let jump_end_pc = ctx.codegen.emit(bytecode::make_nop(), guard_pos);
            let body_addr = ctx.codegen.next_pc();
            let body_target =
                u16::try_from(body_addr).map_err(|_| Error::TargetTooFar(guard_pos, body_addr))?;
            ctx.codegen.patch(jump_body_pc, bytecode::make_jump_if_false(cond_reg, body_target));

            for stmt in span.body {
                compile_stmt(ctx, symtable, stmt)?;
            }
            let start_target =
                u16::try_from(start_pc).map_err(|_| Error::TargetTooFar(guard_pos, start_pc))?;
            ctx.codegen.emit(bytecode::make_jump(start_target), guard_pos);
            let end_addr = ctx.codegen.next_pc();
            let end_target =
                u16::try_from(end_addr).map_err(|_| Error::TargetTooFar(guard_pos, end_addr))?;
            ctx.codegen.patch(jump_end_pc, bytecode::make_jump(end_target));
            end_addr
        }

        DoGuard::PreWhile(guard) => {
            let start_pc = ctx.codegen.next_pc();
            let (cond_reg, guard_pos) = compile_guard(ctx, symtable, guard)?;
            let jump_end_pc = ctx.codegen.emit(bytecode::make_nop(), guard_pos);

            for stmt in span.body {
                compile_stmt(ctx, symtable, stmt)?;
            }
            let start_target =
                u16::try_from(start_pc).map_err(|_| Error::TargetTooFar(guard_pos, start_pc))?;
            ctx.codegen.emit(bytecode::make_jump(start_target), guard_pos);
            let end_addr = ctx.codegen.next_pc();
            let end_target =
                u16::try_from(end_addr).map_err(|_| Error::TargetTooFar(guard_pos, end_addr))?;
            ctx.codegen.patch(jump_end_pc, bytecode::make_jump_if_false(cond_reg, end_target));
            end_addr
        }

        DoGuard::PostUntil(guard) => {
            let start_pc = ctx.codegen.next_pc();
            for stmt in span.body {
                compile_stmt(ctx, symtable, stmt)?;
            }
            let (cond_reg, guard_pos) = compile_guard(ctx, symtable, guard)?;
            let start_target =
                u16::try_from(start_pc).map_err(|_| Error::TargetTooFar(guard_pos, start_pc))?;
            ctx.codegen.emit(bytecode::make_jump_if_false(cond_reg, start_target), guard_pos);
            ctx.codegen.next_pc()
        }

        DoGuard::PostWhile(guard) => {
            let start_pc = ctx.codegen.next_pc();
            for stmt in span.body {
                compile_stmt(ctx, symtable, stmt)?;
            }
            let (cond_reg, guard_pos) = compile_guard(ctx, symtable, guard)?;
            let jump_end_pc = ctx.codegen.emit(bytecode::make_nop(), guard_pos);
            let start_target =
                u16::try_from(start_pc).map_err(|_| Error::TargetTooFar(guard_pos, start_pc))?;
            ctx.codegen.emit(bytecode::make_jump(start_target), guard_pos);
            let end_addr = ctx.codegen.next_pc();
            let end_target =
                u16::try_from(end_addr).map_err(|_| Error::TargetTooFar(guard_pos, end_addr))?;
            ctx.codegen.patch(jump_end_pc, bytecode::make_jump_if_false(cond_reg, end_target));
            end_addr
        }
    };

    let exit_jumps = ctx.do_exit_stack.pop().expect("Must have a matching DO scope");
    for (addr, pos) in exit_jumps {
        let end_target = u16::try_from(end_addr).map_err(|_| Error::TargetTooFar(pos, end_addr))?;
        ctx.codegen.patch(addr, bytecode::make_jump(end_target));
    }

    Ok(())
}

/// Compiles a `FOR` loop and emits bytecode into `ctx`.
fn compile_for(
    ctx: &mut Context,
    symtable: &mut LocalSymtable<'_, '_, '_, '_>,
    span: ForSpan,
) -> Result<()> {
    if span.iter_double && span.iter.ref_type.is_none() {
        match symtable.get_local_or_global(&span.iter) {
            Ok(..) => {
                // Keep existing iterators as-is.  This mirrors core behavior where implicit
                // widening to DOUBLE only happens when the iterator does not exist yet.
            }

            Err(syms::Error::UndefinedSymbol(..)) => {
                let key = SymbolKey::from(&span.iter.name);
                if symtable.get_callable(&key).is_some() {
                    return Err(Error::from_syms(
                        syms::Error::AlreadyDefined(span.iter.clone()),
                        span.iter_pos,
                    ));
                }
                symtable
                    .put_local(key, SymbolPrototype::Scalar(ExprType::Double))
                    .map_err(|e| Error::from_syms(e, span.iter_pos))?;
            }

            Err(e) => return Err(Error::from_syms(e, span.iter_pos)),
        }
    }

    compile_assignment(
        &mut ctx.codegen,
        symtable,
        AssignmentSpan { vref: span.iter.clone(), vref_pos: span.iter_pos, expr: span.start },
    )?;

    let start_pc = ctx.codegen.next_pc();
    let (jump_end_pc, cond_reg, cond_pos) = {
        let cond_pos = span.end.start_pos();
        let mut frozen = symtable.frozen();
        let mut scope = frozen.temp_scope();
        let reg = scope.alloc().map_err(|e| Error::from_syms(e, cond_pos))?;
        compile_expr_as_type(&mut ctx.codegen, &mut frozen, reg, span.end, ExprType::Boolean)?;
        (ctx.codegen.emit(bytecode::make_nop(), cond_pos), reg, cond_pos)
    };

    ctx.for_exit_stack.push(vec![]);

    for stmt in span.body {
        compile_stmt(ctx, symtable, stmt)?;
    }

    compile_assignment(
        &mut ctx.codegen,
        symtable,
        AssignmentSpan { vref: span.iter, vref_pos: span.iter_pos, expr: span.next },
    )?;

    let start_target =
        u16::try_from(start_pc).map_err(|_| Error::TargetTooFar(cond_pos, start_pc))?;
    ctx.codegen.emit(bytecode::make_jump(start_target), cond_pos);

    let end_addr = ctx.codegen.next_pc();
    let end_target =
        u16::try_from(end_addr).map_err(|_| Error::TargetTooFar(cond_pos, end_addr))?;
    ctx.codegen.patch(jump_end_pc, bytecode::make_jump_if_false(cond_reg, end_target));

    let exit_jumps = ctx.for_exit_stack.pop().expect("Must have a matching FOR scope");
    for (addr, pos) in exit_jumps {
        let end_target = u16::try_from(end_addr).map_err(|_| Error::TargetTooFar(pos, end_addr))?;
        ctx.codegen.patch(addr, bytecode::make_jump(end_target));
    }

    Ok(())
}

/// Compiles an `IF` statement `span` into the `ctx`.
fn compile_if(
    ctx: &mut Context,
    symtable: &mut LocalSymtable<'_, '_, '_, '_>,
    span: IfSpan,
) -> Result<()> {
    let mut end_pcs: Vec<usize> = vec![];
    let nbranches = span.branches.len();

    for (i, branch) in span.branches.into_iter().enumerate() {
        let is_last = i == nbranches - 1;
        let guard_pos = branch.guard.start_pos();

        let (jump_pc, cond_reg) = {
            let mut frozen = symtable.frozen();
            let mut scope = frozen.temp_scope();
            let reg = scope.alloc().map_err(|e| Error::from_syms(e, guard_pos))?;
            compile_expr_as_type(
                &mut ctx.codegen,
                &mut frozen,
                reg,
                branch.guard,
                ExprType::Boolean,
            )?;
            (ctx.codegen.emit(bytecode::make_nop(), guard_pos), reg)
        };

        for stmt in branch.body {
            compile_stmt(ctx, symtable, stmt)?;
        }

        if !is_last {
            let end_pc = ctx.codegen.emit(bytecode::make_nop(), guard_pos);
            end_pcs.push(end_pc);
        }

        let next_addr = ctx.codegen.next_pc();
        let target =
            u16::try_from(next_addr).map_err(|_| Error::TargetTooFar(guard_pos, next_addr))?;
        ctx.codegen.patch(jump_pc, bytecode::make_jump_if_false(cond_reg, target));
    }

    let end_addr = ctx.codegen.next_pc();
    for end_pc in end_pcs {
        let end_target = u16::try_from(end_addr)
            .map_err(|_| Error::TargetTooFar(LineCol { line: 0, col: 0 }, end_addr))?;
        ctx.codegen.patch(end_pc, bytecode::make_jump(end_target));
    }

    Ok(())
}

/// Compiles a `WHILE` loop and emits bytecode into `ctx`.
fn compile_while(
    ctx: &mut Context,
    symtable: &mut LocalSymtable<'_, '_, '_, '_>,
    span: WhileSpan,
) -> Result<()> {
    let start_pc = ctx.codegen.next_pc();

    let (jump_end_pc, cond_reg, guard_pos) = {
        let guard_pos = span.expr.start_pos();
        let mut frozen = symtable.frozen();
        let mut scope = frozen.temp_scope();
        let reg = scope.alloc().map_err(|e| Error::from_syms(e, guard_pos))?;
        compile_expr_as_type(&mut ctx.codegen, &mut frozen, reg, span.expr, ExprType::Boolean)?;
        (ctx.codegen.emit(bytecode::make_nop(), guard_pos), reg, guard_pos)
    };

    for stmt in span.body {
        compile_stmt(ctx, symtable, stmt)?;
    }

    let start_target =
        u16::try_from(start_pc).map_err(|_| Error::TargetTooFar(guard_pos, start_pc))?;
    ctx.codegen.emit(bytecode::make_jump(start_target), guard_pos);

    let end_addr = ctx.codegen.next_pc();
    let end_target =
        u16::try_from(end_addr).map_err(|_| Error::TargetTooFar(guard_pos, end_addr))?;
    ctx.codegen.patch(jump_end_pc, bytecode::make_jump_if_false(cond_reg, end_target));

    Ok(())
}

/// Compiles a single `stmt` into the `ctx`.
fn compile_stmt(
    ctx: &mut Context,
    symtable: &mut LocalSymtable<'_, '_, '_, '_>,
    stmt: Statement,
) -> Result<()> {
    let start_pc = ctx.codegen.next_pc();
    let mut mark_start = true;
    match stmt {
        Statement::ArrayAssignment(span) => {
            let key_pos = span.vref_pos;

            let (arr_reg, info) = match symtable.get_local_or_global(&span.vref) {
                Ok((reg, SymbolPrototype::Array(info))) => (reg, info),

                Ok((_, SymbolPrototype::Scalar(_))) | Err(syms::Error::UndefinedSymbol(..)) => {
                    return Err(Error::NotAnArray(key_pos, span.vref));
                }

                Err(e) => return Err(Error::from_syms(e, key_pos)),
            };

            if span.subscripts.len() != info.ndims {
                return Err(Error::WrongNumberOfSubscripts(
                    key_pos,
                    info.ndims,
                    span.subscripts.len(),
                ));
            }

            let mut symtable = symtable.frozen();
            let mut outer_scope = symtable.temp_scope();

            let val_reg = outer_scope.alloc().map_err(|e| Error::from_syms(e, key_pos))?;
            compile_expr_as_type(
                &mut ctx.codegen,
                &mut symtable,
                val_reg,
                span.expr,
                info.subtype,
            )?;

            let first_sub_reg = compile_integer_exprs(
                &mut ctx.codegen,
                &mut symtable,
                &mut outer_scope,
                key_pos,
                span.subscripts.into_iter(),
            )?;
            ctx.codegen.emit(bytecode::make_store_array(arr_reg, val_reg, first_sub_reg), key_pos);
        }

        Statement::Assignment(span) => {
            compile_assignment(&mut ctx.codegen, symtable, span)?;
        }

        Statement::Call(span) => {
            let key = SymbolKey::from(&span.vref.name);
            let key_pos = span.vref_pos;

            let Some(md) = symtable.get_callable(&key) else {
                return Err(Error::UndefinedSymbol(
                    key_pos,
                    span.vref.clone(),
                    RegisterScope::Global,
                ));
            };
            if md.return_type().is_some() {
                return Err(Error::NotAFunction(span.vref_pos, span.vref));
            }
            let is_user_defined = md.is_user_defined();
            let md = md.clone();

            define_new_args(&span, &md, symtable, &mut ctx.codegen)?;
            let (first_temp, arg_linecols) = {
                let mut symtable = symtable.frozen();
                compile_args(span, md, &mut symtable, &mut ctx.codegen)?
            };

            if is_user_defined {
                let addr = ctx.codegen.emit(bytecode::make_nop(), key_pos);
                ctx.codegen.set_arg_linecols(addr, arg_linecols);
                ctx.codegen.add_fixup(addr, Fixup::Call(first_temp, key));
            } else {
                let upcall = ctx.codegen.get_upcall(key, None, key_pos)?;
                let addr = ctx.codegen.emit(bytecode::make_upcall(upcall, first_temp), key_pos);
                ctx.codegen.set_arg_linecols(addr, arg_linecols);
            }
        }

        Statement::Callable(span) => {
            mark_start = false;
            let mut syntax = vec![];
            for (i, param) in span.params.iter().enumerate() {
                let sep = if i == span.params.len() - 1 {
                    ArgSepSyntax::End
                } else {
                    ArgSepSyntax::Exactly(ArgSep::Long)
                };
                syntax.push(SingularArgSyntax::RequiredValue(
                    RequiredValueSyntax {
                        name: Cow::Owned(param.name.to_owned()),
                        vtype: param.ref_type.unwrap_or(ExprType::Integer),
                    },
                    sep,
                ));
            }

            let mut builder = CallableMetadataBuilder::new_dynamic(span.name.name.to_owned())
                .with_dynamic_syntax(vec![(syntax, None)]);
            if let Some(ctype) = span.name.ref_type {
                builder = builder.with_return_type(ctype);
            }

            symtable
                .define_user_callable(&span.name, builder.build())
                .map_err(|e| Error::from_syms(e, span.name_pos))?;
            ctx.user_callables.push(span);
        }

        Statement::Data(span) => {
            ctx.data.extend(span.values.into_iter().map(|expr| expr.map(data_expr_to_constant)));
        }

        Statement::Dim(span) => {
            let name_pos = span.name_pos;
            let key = SymbolKey::from(&span.name);

            if symtable.get_callable(&key).is_some() {
                return Err(Error::from_syms(
                    syms::Error::AlreadyDefined(VarRef::new(&span.name, None)),
                    name_pos,
                ));
            }

            let reg = if span.shared {
                if symtable.contains_global(&key) {
                    return Err(Error::from_syms(
                        syms::Error::AlreadyDefined(VarRef::new(&span.name, None)),
                        name_pos,
                    ));
                }
                symtable.put_global(key, SymbolPrototype::Scalar(span.vtype))
            } else {
                if symtable.contains_local(&key) {
                    return Err(Error::from_syms(
                        syms::Error::AlreadyDefined(VarRef::new(&span.name, None)),
                        name_pos,
                    ));
                }
                symtable.put_local(key, SymbolPrototype::Scalar(span.vtype))
            }
            .map_err(|e| Error::from_syms(e, name_pos))?;
            ctx.codegen.emit_default(reg, span.vtype, name_pos);
        }

        Statement::DimArray(span) => {
            let name_pos = span.name_pos;
            let key = SymbolKey::from(&span.name);
            let ndims = span.dimensions.len();

            if symtable.get_callable(&key).is_some() {
                return Err(Error::from_syms(
                    syms::Error::AlreadyDefined(VarRef::new(&span.name, None)),
                    name_pos,
                ));
            }

            let info = syms::ArrayInfo { subtype: span.subtype, ndims };
            let reg = if span.shared {
                if symtable.contains_global(&key) {
                    return Err(Error::from_syms(
                        syms::Error::AlreadyDefined(VarRef::new(&span.name, None)),
                        name_pos,
                    ));
                }
                symtable.put_global(key, SymbolPrototype::Array(info))
            } else {
                if symtable.contains_local(&key) {
                    return Err(Error::from_syms(
                        syms::Error::AlreadyDefined(VarRef::new(&span.name, None)),
                        name_pos,
                    ));
                }
                symtable.put_local(key, SymbolPrototype::Array(info))
            }
            .map_err(|e| Error::from_syms(e, name_pos))?;

            let mut symtable = symtable.frozen();
            let mut outer_scope = symtable.temp_scope();

            let first_dim_reg = compile_integer_exprs(
                &mut ctx.codegen,
                &mut symtable,
                &mut outer_scope,
                name_pos,
                span.dimensions.into_iter(),
            )?;
            let packed = PackedArrayType::new(span.subtype, ndims)
                .map_err(|_| Error::TooManyArrayDimensions(span.name_pos, ndims))?;
            ctx.codegen.emit(bytecode::make_alloc_array(reg, packed, first_dim_reg), name_pos);
        }

        Statement::Do(span) => {
            compile_do(ctx, symtable, span)?;
        }

        Statement::End(span) => {
            if let Some(expr) = span.code.as_ref()
                && let Some((code, code_pos)) = static_end_code(expr)
                && let Err(e) = bytecode::ExitCode::try_from(code)
            {
                return Err(Error::from_bytecode_invalid_exit_code(e, code_pos));
            }

            let mut symtable = symtable.frozen();
            let mut scope = symtable.temp_scope();
            let reg = scope.alloc().map_err(|e| Error::from_syms(e, span.pos))?;
            match span.code {
                Some(expr) => {
                    compile_expr_as_type(
                        &mut ctx.codegen,
                        &mut symtable,
                        reg,
                        expr,
                        ExprType::Integer,
                    )?;
                }
                None => {
                    ctx.codegen.emit(bytecode::make_load_integer(reg, 0), span.pos);
                }
            }
            ctx.codegen.emit(bytecode::make_end(reg), span.pos);
        }

        Statement::ExitDo(span) => {
            let Some(exit_stack) = ctx.do_exit_stack.last_mut() else {
                return Err(Error::MisplacedExit(span.pos, "DO"));
            };
            let addr = ctx.codegen.emit(bytecode::make_nop(), span.pos);
            exit_stack.push((addr, span.pos));
        }

        Statement::ExitFor(span) => {
            let Some(exit_stack) = ctx.for_exit_stack.last_mut() else {
                return Err(Error::MisplacedExit(span.pos, "FOR"));
            };
            let addr = ctx.codegen.emit(bytecode::make_nop(), span.pos);
            exit_stack.push((addr, span.pos));
        }

        Statement::ExitFunction(span) => {
            if ctx.current_callable != Some(CallableKind::Function) {
                return Err(Error::MisplacedExit(span.pos, "FUNCTION"));
            }
            let addr = ctx.codegen.emit(bytecode::make_nop(), span.pos);
            ctx.callable_exit_jumps.push((addr, span.pos));
        }

        Statement::ExitSub(span) => {
            if ctx.current_callable != Some(CallableKind::Sub) {
                return Err(Error::MisplacedExit(span.pos, "SUB"));
            }
            let addr = ctx.codegen.emit(bytecode::make_nop(), span.pos);
            ctx.callable_exit_jumps.push((addr, span.pos));
        }

        Statement::For(span) => {
            compile_for(ctx, symtable, span)?;
        }

        Statement::Gosub(span) => {
            let addr = ctx.codegen.emit(bytecode::make_nop(), span.target_pos);
            ctx.codegen.add_fixup(addr, Fixup::Gosub(span.target));
        }

        Statement::Goto(span) => {
            let addr = ctx.codegen.emit(bytecode::make_nop(), span.target_pos);
            ctx.codegen.add_fixup(addr, Fixup::Goto(span.target));
        }

        Statement::Label(span) => {
            mark_start = false;
            if !ctx.codegen.define_label(SymbolKey::from(&span.name), ctx.codegen.next_pc()) {
                return Err(Error::DuplicateLabel(span.name_pos, span.name));
            }
        }

        Statement::Return(span) => {
            ctx.codegen.emit(bytecode::make_return(), span.pos);
        }

        Statement::If(span) => {
            compile_if(ctx, symtable, span)?;
        }

        Statement::OnError(span) => {
            match span {
                OnErrorSpan::Goto(span, pos) => {
                    let addr = ctx.codegen.emit(bytecode::make_nop(), pos);
                    ctx.codegen.add_fixup(addr, Fixup::OnErrorGoto(span.target));
                }
                OnErrorSpan::Reset(pos) => {
                    ctx.codegen
                        .emit(bytecode::make_set_error_handler(ErrorHandlerMode::None, 0), pos);
                }
                OnErrorSpan::ResumeNext(pos) => {
                    ctx.codegen.emit(
                        bytecode::make_set_error_handler(ErrorHandlerMode::ResumeNext, 0),
                        pos,
                    );
                }
            };
        }

        Statement::Select(span) => {
            compile_select(ctx, symtable, span)?;
        }

        Statement::While(span) => {
            compile_while(ctx, symtable, span)?;
        }
    }
    if mark_start && start_pc != ctx.codegen.next_pc() {
        ctx.codegen.mark_statement_start(start_pc);
    }
    Ok(())
}

/// Compiles a sequence of `stmts` that all live in the same `symtable` scope.
fn compile_scope<I>(
    ctx: &mut Context,
    mut symtable: LocalSymtable<'_, '_, '_, '_>,
    stmts: I,
) -> Result<()>
where
    I: Iterator<Item = std::result::Result<Statement, parser::Error>>,
{
    let enter = ctx.codegen.emit(bytecode::make_nop(), LineCol { line: 0, col: 0 });
    for stmt in stmts {
        compile_stmt(ctx, &mut symtable, stmt?)?;
    }
    let nlocals =
        symtable.leave_scope().map_err(|e| Error::from_syms(e, LineCol { line: 0, col: 0 }))?;
    ctx.codegen.add_fixup(enter, Fixup::Enter(nlocals));
    Ok(())
}

/// Compiles all user-defined callables that have been captured in `ctx`.
fn compile_user_callables(ctx: &mut Context, symtable: &mut GlobalSymtable) -> Result<()> {
    let user_callables: Vec<CallableSpan> = ctx.user_callables.drain(..).collect();
    debug_assert!(ctx.user_callables.is_empty());

    for callable in user_callables {
        let start_pc = ctx.codegen.next_pc();

        let key_pos = callable.name_pos;
        let key = SymbolKey::from(callable.name.name);
        ctx.current_callable = Some(if callable.name.ref_type.is_some() {
            CallableKind::Function
        } else {
            CallableKind::Sub
        });
        debug_assert!(ctx.callable_exit_jumps.is_empty());

        let mut symtable = symtable.enter_scope();

        // The call protocol expects the return value to be in the first local variable
        // so allocate it early, and then all arguments follow in order from left to right.
        if let Some(vtype) = callable.name.ref_type {
            let ret_reg = symtable
                .put_local(key.clone(), SymbolPrototype::Scalar(vtype))
                .map_err(|e| Error::from_syms(e, key_pos))?;

            // Set the default value of the function result.  We could instead try to do this
            // at runtime by clearning the return register... but the problem is that we need
            // to handle non-primitive types like strings and the runtime doesn't know the type
            // of the result to properly allocate it.
            let value = match vtype {
                ExprType::Boolean | ExprType::Integer => 0,
                ExprType::Double => {
                    ctx.codegen.get_constant(ConstantDatum::Double(0.0), key_pos)?
                }
                ExprType::Text => {
                    ctx.codegen.get_constant(ConstantDatum::Text(String::new()), key_pos)?
                }
            };
            ctx.codegen.emit(bytecode::make_load_integer(ret_reg, value), key_pos);
        }
        for param in callable.params {
            let key = SymbolKey::from(param.name);
            symtable
                .put_local(
                    key.clone(),
                    SymbolPrototype::Scalar(param.ref_type.unwrap_or(ExprType::Integer)),
                )
                .map_err(|e| Error::from_syms(e, key_pos))?;
        }

        compile_scope(ctx, symtable, callable.body.into_iter().map(Ok))?;
        if let Some(span) = ctx.user_callables.first() {
            return Err(Error::CannotNestUserCallables(span.name_pos));
        }

        let return_addr = ctx.codegen.next_pc();
        ctx.codegen.emit(bytecode::make_return(), callable.end_pos);
        for (addr, pos) in ctx.callable_exit_jumps.drain(..) {
            let target =
                u16::try_from(return_addr).map_err(|_| Error::TargetTooFar(pos, return_addr))?;
            ctx.codegen.patch(addr, bytecode::make_jump(target));
        }
        ctx.current_callable = None;
        ctx.codegen.define_user_callable(key, start_pc);
    }

    Ok(())
}

/// Extracts the metadata of all provided `upcalls`.
pub fn only_metadata(
    upcalls_by_name: &HashMap<SymbolKey, Rc<dyn Callable>>,
) -> HashMap<&SymbolKey, &CallableMetadata> {
    let mut upcalls = HashMap::with_capacity(upcalls_by_name.len());
    for (name, callable) in upcalls_by_name {
        upcalls.insert(name, callable.metadata());
    }
    upcalls
}

/// Descriptor for a single global variable to be pre-defined before compilation.
pub struct GlobalDef {
    /// Name of the variable (case-insensitive, as in EndBASIC).
    pub name: String,

    /// Kind and type information for the variable.
    pub kind: GlobalDefKind,
}

/// Kind of a pre-defined global variable.
pub enum GlobalDefKind {
    /// A scalar (non-array) variable.
    Scalar {
        /// Type of the scalar variable.
        etype: ExprType,

        /// Initial value for the variable.  If `None`, the variable is initialized to its default
        /// value: `0` for numeric types and an empty string for `Text`.  The type of the datum
        /// must match `etype`.
        initial_value: Option<ConstantDatum>,
    },

    /// A multidimensional array with the given element type and fixed dimension sizes.
    ///
    /// Each dimension size must be positive and must fit in a `u16`.
    Array {
        /// Element type of the array.
        subtype: ExprType,

        /// Size of each dimension, in order from outermost to innermost.
        dimensions: Vec<usize>,
    },
}

/// Prepares global variables injected from outside of the compiled program.
///
/// Pre-defined scalar globals are initialized to their default values (0 for numeric types,
/// empty string for text).  Pre-defined array globals are allocated with all elements set to
/// their default values.  The compiled program may read or write any of these globals.
///
/// After execution, use `Vm::get_global*` methods to query the values of these globals (and
/// any globals declared via `DIM SHARED` in the program itself).
fn prepare_globals(
    ctx: &mut Context,
    symtable: &mut GlobalSymtable,
    global_defs: &[GlobalDef],
) -> Result<()> {
    let preamble_pos = LineCol { line: 0, col: 0 };

    // Register all global defs in the symbol table and collect array globals for the preamble.
    let mut max_ndims: u8 = 0;
    let mut array_globals: Vec<(Register, &GlobalDef)> = vec![];
    for def in global_defs {
        let key = SymbolKey::from(&def.name);
        match &def.kind {
            GlobalDefKind::Array { subtype, dimensions } => {
                let ndims =
                    u8::try_from(dimensions.len()).expect("Array must have at most 255 dimensions");
                let info = syms::ArrayInfo { subtype: *subtype, ndims: usize::from(ndims) };
                let reg = symtable
                    .put_global(key, SymbolPrototype::Array(info))
                    .map_err(|e| Error::from_syms(e, preamble_pos))?;
                max_ndims = max(max_ndims, ndims);
                array_globals.push((reg, def));
            }

            GlobalDefKind::Scalar { etype, initial_value } => {
                let reg = symtable
                    .put_global(key, SymbolPrototype::Scalar(*etype))
                    .map_err(|e| Error::from_syms(e, preamble_pos))?;
                match initial_value {
                    Some(datum) => {
                        if datum.etype() != *etype {
                            return Err(Error::TypeMismatch(preamble_pos, datum.etype(), *etype));
                        }
                        ctx.codegen.emit_value(reg, datum.clone(), preamble_pos)?;
                    }
                    None => ctx.codegen.emit_default(reg, *etype, preamble_pos),
                }
            }
        }
    }

    // Emit the array initialization preamble, but only if any arrays were defined.
    //
    // We use a short-lived `ENTER/LEAVE` scope to borrow local registers for the dimension
    // temporaries without permanently consuming global register slots.
    if array_globals.is_empty() {
        return Ok(());
    }
    ctx.codegen.emit(bytecode::make_enter(max_ndims), preamble_pos);
    for (reg, def) in array_globals {
        let GlobalDefKind::Array { subtype, dimensions } = &def.kind else {
            unreachable!("array_globals only contains array defs per the loop above")
        };

        let ndims = u8::try_from(dimensions.len()).unwrap();
        for (i, &dim) in dimensions.iter().enumerate() {
            let dim_u16 =
                u16::try_from(dim).expect("Array dimension must fit in u16 for LOADI instruction");
            let local_reg =
                Register::local(u8::try_from(i).unwrap()).expect("Dimension index fits in u8");
            ctx.codegen.emit(bytecode::make_load_integer(local_reg, dim_u16), preamble_pos);
        }

        let first_dim_reg = Register::local(0).expect("Local register 0 is always valid");
        let packed = PackedArrayType::new(*subtype, usize::from(ndims))
            .map_err(|_| Error::TooManyArrayDimensions(preamble_pos, usize::from(ndims)))?;
        ctx.codegen.emit(bytecode::make_alloc_array(reg, packed, first_dim_reg), preamble_pos);
    }
    ctx.codegen.emit(bytecode::make_leave(), preamble_pos);

    Ok(())
}

/// Compiles the `input` into an `Image` that can be executed by the VM, with `global_defs`
/// pre-defined as global variables visible to the compiled program.
///
/// `upcalls` contains the metadata of all built-in callables that the compiled code can use.
pub fn compile_with_globals(
    input: &mut dyn io::Read,
    upcalls: &HashMap<&SymbolKey, &CallableMetadata>,
    global_defs: &[GlobalDef],
) -> Result<Image> {
    let mut ctx = Context::default();

    let mut symtable = GlobalSymtable::new(upcalls);

    prepare_globals(&mut ctx, &mut symtable, global_defs)?;

    compile_scope(&mut ctx, symtable.enter_scope(), parser::parse(input))?;
    ctx.codegen.emit(bytecode::make_eof(), LineCol { line: 0, col: 0 });

    compile_user_callables(&mut ctx, &mut symtable)?;

    let global_vars = symtable
        .iter_globals()
        .map(|(key, proto, reg)| {
            let (subtype, ndims) = match proto {
                SymbolPrototype::Array(info) => (info.subtype, info.ndims),
                SymbolPrototype::Scalar(etype) => (etype, 0),
            };
            (key.clone(), GlobalVarInfo { reg, subtype, ndims })
        })
        .collect();
    ctx.codegen.build_image(global_vars, ctx.data)
}

/// Compiles the `input` into an `Image` that can be executed by the VM.
///
/// `upcalls` contains the metadata of all built-in callables that the compiled code can use.
pub fn compile(
    input: &mut dyn io::Read,
    upcalls: &HashMap<&SymbolKey, &CallableMetadata>,
) -> Result<Image> {
    compile_with_globals(input, upcalls, &[])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::ExprType;
    use crate::mem::ConstantDatum;
    use crate::vm::{StopReason, Vm};

    fn compile_and_get_global(defs: &[GlobalDef], name: &str) -> ConstantDatum {
        let image = compile_with_globals(&mut "".as_bytes(), &HashMap::default(), defs)
            .expect("compilation should succeed");
        let mut vm = Vm::new(HashMap::default());
        vm.load(image);
        match vm.exec() {
            StopReason::End(code) if code.is_success() => {}
            StopReason::End(code) => panic!("unexpected exit code: {}", code.to_i32()),
            StopReason::Eof => {}
            StopReason::Exception(pos, msg) => panic!("exception at {pos}: {msg}"),
            StopReason::Upcall(_) => panic!("unexpected upcall"),
        }
        vm.get_global(name).expect("get_global failed").expect("global not found")
    }

    #[test]
    fn test_inject_boolean() {
        let defs = vec![GlobalDef {
            name: "b".to_owned(),
            kind: GlobalDefKind::Scalar {
                etype: ExprType::Boolean,
                initial_value: Some(ConstantDatum::Boolean(true)),
            },
        }];
        assert_eq!(ConstantDatum::Boolean(true), compile_and_get_global(&defs, "b"));
    }

    #[test]
    fn test_inject_integer() {
        let defs = vec![GlobalDef {
            name: "n".to_owned(),
            kind: GlobalDefKind::Scalar {
                etype: ExprType::Integer,
                initial_value: Some(ConstantDatum::Integer(42)),
            },
        }];
        assert_eq!(ConstantDatum::Integer(42), compile_and_get_global(&defs, "n"));
    }

    #[test]
    fn test_inject_integer_large() {
        let defs = vec![GlobalDef {
            name: "n".to_owned(),
            kind: GlobalDefKind::Scalar {
                etype: ExprType::Integer,
                initial_value: Some(ConstantDatum::Integer(70000)),
            },
        }];
        assert_eq!(ConstantDatum::Integer(70000), compile_and_get_global(&defs, "n"));
    }

    #[test]
    fn test_inject_double() {
        let defs = vec![GlobalDef {
            name: "d".to_owned(),
            kind: GlobalDefKind::Scalar {
                etype: ExprType::Double,
                initial_value: Some(ConstantDatum::Double(1.5)),
            },
        }];
        assert_eq!(ConstantDatum::Double(1.5), compile_and_get_global(&defs, "d"));
    }

    #[test]
    fn test_inject_text() {
        let defs = vec![GlobalDef {
            name: "s".to_owned(),
            kind: GlobalDefKind::Scalar {
                etype: ExprType::Text,
                initial_value: Some(ConstantDatum::Text("hello".to_owned())),
            },
        }];
        assert_eq!(ConstantDatum::Text("hello".to_owned()), compile_and_get_global(&defs, "s"),);
    }

    #[test]
    fn test_inject_type_mismatch() {
        let defs = vec![GlobalDef {
            name: "n".to_owned(),
            kind: GlobalDefKind::Scalar {
                etype: ExprType::Integer,
                initial_value: Some(ConstantDatum::Double(1.5)),
            },
        }];
        let result = compile_with_globals(&mut "".as_bytes(), &HashMap::default(), &defs);
        assert!(matches!(result, Err(Error::TypeMismatch(..))));
    }
}
