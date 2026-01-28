// EndBASIC
// Copyright 2024 Julio Merino
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

//! Functions to convert expressions into bytecode.

use crate::ast::{Expr, ExprType};
use crate::bytecode::{self, Register, RegisterScope};
use crate::compiler::codegen::{Codegen, Fixup};
use crate::compiler::syms::{SymbolKey, TempSymtable};
use crate::compiler::{Error, Result};
use crate::mem::Datum;
use std::convert::TryFrom;

pub(super) fn compile_expr(
    codegen: &mut Codegen,
    symtable: &mut TempSymtable<'_, '_, '_, '_, '_>,
    reg: Register,
    expr: Expr,
) -> Result<ExprType> {
    match expr {
        Expr::Add(span) => {
            let mut scope = symtable.temp_scope();

            let lpos = span.lhs.start_pos();
            let ltemp = scope.alloc().map_err(|e| Error::from_syms(e, lpos))?;
            let ltype = compile_expr(codegen, symtable, ltemp, span.lhs)?;

            let rpos = span.rhs.start_pos();
            let rtemp = scope.alloc().map_err(|e| Error::from_syms(e, rpos))?;
            let rtype = compile_expr(codegen, symtable, rtemp, span.rhs)?;

            match (ltype, rtype) {
                (ExprType::Integer, ExprType::Integer) => {
                    codegen.emit(bytecode::make_add_integer(reg, ltemp, rtemp), span.pos);
                    Ok(ExprType::Integer)
                }

                (ExprType::Text, ExprType::Text) => {
                    codegen.emit(bytecode::make_concat(reg, ltemp, rtemp), span.pos);
                    Ok(ExprType::Text)
                }

                (_, _) => Err(Error::BinaryOpType(span.pos, "+", ltype, rtype)),
            }
        }

        Expr::Boolean(span) => {
            let value = if span.value { 1 } else { 0 };
            codegen.emit(bytecode::make_load_integer(reg, value), span.pos);
            Ok(ExprType::Boolean)
        }

        Expr::Call(span) => {
            let key = SymbolKey::from(&span.vref.name);
            let etype = match symtable.get_callable(&key) {
                Some(md) => {
                    let Some(etype) = md.return_type() else {
                        return Err(Error::NotAFunction(span.vref_pos, span.vref));
                    };
                    etype
                }
                None => {
                    return Err(Error::UndefinedSymbol(
                        span.vref_pos,
                        span.vref,
                        RegisterScope::Global,
                    ));
                }
            };
            let addr = codegen.emit(bytecode::make_nop(), span.vref_pos);
            codegen.add_fixup(addr, Fixup::Call(reg, key));
            Ok(etype)
        }

        Expr::Double(span) => {
            let index = codegen.get_constant(Datum::Double(span.value), span.pos)?;
            codegen.emit(bytecode::make_load_constant(reg, index), span.pos);
            Ok(ExprType::Double)
        }

        Expr::Integer(span) => {
            match u16::try_from(span.value) {
                Ok(i) => {
                    codegen.emit(bytecode::make_load_integer(reg, i), span.pos);
                }
                Err(_) => {
                    let index = codegen.get_constant(Datum::Integer(span.value), span.pos)?;
                    codegen.emit(bytecode::make_load_constant(reg, index), span.pos);
                }
            }
            Ok(ExprType::Integer)
        }

        Expr::Symbol(span) => {
            let (local, etype) = symtable
                .get_local_or_global(&span.vref)
                .map_err(|e| Error::from_syms(e, span.pos))?;
            codegen.emit(bytecode::make_move(reg, local), span.pos);
            Ok(etype)
        }

        Expr::Text(span) => {
            let index = codegen.get_constant(Datum::Text(span.value), span.pos)?;
            codegen.emit(bytecode::make_load_integer(reg, index), span.pos);
            Ok(ExprType::Text)
        }

        _ => todo!(),
    }
}
