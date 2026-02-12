// EndBASIC
// Copyright 2026 Julio Merino
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

//! Common compilers for callable arguments.

use crate::ast::{ArgSpan, CallSpan};
use crate::bytecode::{self, Register};
use crate::callable::{CallableMetadata, CallableSyntax};
use crate::compiler::codegen::Codegen;
use crate::compiler::exprs::{compile_expr, compile_expr_as_type};
use crate::compiler::syms::TempSymtable;
use crate::compiler::{Error, Result};
use crate::reader::LineCol;
use crate::{ArgSep, ArgSepSyntax, RepeatedTypeSyntax, SingularArgSyntax};

/// Finds the syntax definition that matches the given argument count.
///
/// Returns an error if no syntax matches, and panics if multiple syntaxes match (which would
/// indicate an ambiguous callable definition).
fn find_syntax(md: &CallableMetadata, pos: LineCol, nargs: usize) -> Result<&CallableSyntax> {
    let mut matches = md.syntaxes().iter().filter(|s| s.expected_nargs().contains(&nargs));
    let syntax = matches.next();
    match syntax {
        Some(syntax) => {
            debug_assert!(matches.next().is_none(), "Ambiguous syntax definitions");
            Ok(syntax)
        }
        None => Err(Error::CallableSyntax(pos, md.clone())),
    }
}

/// Compiles an argument separator with any necessary tagging.
///
/// `instrs` is the list of instructions into which insert the separator tag at `sep_tag_pc`
/// when it is needed to disambiguate separators at runtime.
///
/// `syn` contains the details about the separator syntax that is accepted.
///
/// `sep` and `sep_pos` are the details about the separator being compiled.
///
/// `is_last` indicates whether this is the last separator in the command call and is used
/// only for diagnostics purposes.
#[allow(clippy::too_many_arguments)]
fn validate_syn_argsep(
    md: &CallableMetadata,
    pos: LineCol,
    syn: &ArgSepSyntax,
    is_last: bool,
    sep: ArgSep,
) -> Result<()> {
    debug_assert!(
        (!is_last || sep == ArgSep::End) && (is_last || sep != ArgSep::End),
        "Parser can only supply an End separator in the last argument"
    );

    match syn {
        ArgSepSyntax::Exactly(exp_sep) => {
            debug_assert!(*exp_sep != ArgSep::End, "Use ArgSepSyntax::End");
            if sep != ArgSep::End && sep != *exp_sep {
                return Err(Error::CallableSyntax(pos, md.clone()));
            }
            Ok(())
        }

        ArgSepSyntax::OneOf(exp_seps) => {
            let mut found = false;
            for exp_sep in *exp_seps {
                debug_assert!(*exp_sep != ArgSep::End, "Use ArgSepSyntax::End");
                if sep == *exp_sep {
                    found = true;
                    break;
                }
            }
            if !found {
                return Err(Error::CallableSyntax(pos, md.clone()));
            }
            Ok(())
        }

        ArgSepSyntax::End => {
            debug_assert!(is_last);
            Ok(())
        }
    }
}

/// Compiles the arguments of a callable invocation.
///
/// Returns the first register containing the compiled arguments. Arguments are laid out as
/// pairs of type tag and value registers, allowing the callable to interpret them at runtime.
///
/// TODO(jmmv): The `md` metadata is passed by value, not because we want to, but because it's
/// necessary to appease the borrow checker.  The `md` is obtained from the `symtable` in the caller
/// (as a reference) to perform various validations so it is not possible to pass it as input along
/// `symtable`.  An alternative would be to take the symbol `key` as a parameter here and perform
/// another lookup from the symtable.  Or maybe we could make `Metadata` objects static by
/// eliminating the `MetadataBuilder` and pass a static reference here.
pub(super) fn compile_args(
    span: CallSpan,
    md: CallableMetadata,
    symtable: &mut TempSymtable<'_, '_, '_, '_, '_>,
    codegen: &mut Codegen,
) -> Result<Register> {
    let key_pos = span.vref_pos;

    let syntax = find_syntax(&md, key_pos, span.args.len())?;

    let mut scope = symtable.temp_scope();

    let input_nargs = span.args.len();
    let mut arg_iter = span.args.into_iter().peekable();

    for syn in syntax.singular.iter() {
        match syn {
            SingularArgSyntax::RequiredValue(details, exp_sep) => {
                let ArgSpan { expr, sep, sep_pos } =
                    arg_iter.next().expect("Args and their syntax must advance in unison");
                let arg_pos = expr.as_ref().map(|e| e.start_pos()).unwrap_or(sep_pos);

                match expr {
                    None => return Err(Error::CallableSyntax(key_pos, md)),
                    Some(expr) => {
                        let temp_value = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;
                        compile_expr_as_type(codegen, symtable, temp_value, expr, details.vtype)?;
                        validate_syn_argsep(&md, arg_pos, exp_sep, arg_iter.peek().is_none(), sep)?;
                    }
                }
            }

            SingularArgSyntax::RequiredRef(_details, exp_sep) => {
                let ArgSpan { expr, sep, sep_pos } =
                    arg_iter.next().expect("Args and their syntax must advance in unison");
                let arg_pos = expr.as_ref().map(|e| e.start_pos()).unwrap_or(sep_pos);

                match expr {
                    None => return Err(Error::CallableSyntax(key_pos, md)),
                    Some(_expr) => {
                        validate_syn_argsep(&md, arg_pos, exp_sep, arg_iter.peek().is_none(), sep)?;
                        todo!();
                    }
                }
            }

            SingularArgSyntax::OptionalValue(details, exp_sep) => {
                // The `CallSpan` is optimized (for simplicity) to not carry any arguments at all
                // when callables are invoked without arguments.  This leads to a little
                // inconsistency though: a call like `PRINT ;` carries two arguments whereas
                // `PRINT` carries none (instead of one).  Deal with this here.
                let (expr, sep, sep_pos) = match arg_iter.next() {
                    Some(ArgSpan { expr, sep, sep_pos }) => (expr, sep, sep_pos),
                    None => (None, ArgSep::End, key_pos),
                };
                let arg_pos = expr.as_ref().map(|e| e.start_pos()).unwrap_or(sep_pos);

                let temp_tag = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;
                let tag = match expr {
                    None => bytecode::VarArgTag::Missing(sep),
                    Some(expr) => {
                        let temp_value = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;
                        compile_expr_as_type(codegen, symtable, temp_value, expr, details.vtype)?;
                        bytecode::VarArgTag::Immediate(sep, details.vtype)
                    }
                };
                validate_syn_argsep(&md, arg_pos, exp_sep, arg_iter.peek().is_none(), sep)?;
                codegen.emit(bytecode::make_load_integer(temp_tag, tag.make_u16()), arg_pos);
            }

            SingularArgSyntax::AnyValue(details, exp_sep) => {
                // The `CallSpan` is optimized (for simplicity) to not carry any arguments at all
                // when callables are invoked without arguments.  This leads to a little
                // inconsistency though: a call like `PRINT ;` carries two arguments whereas
                // `PRINT` carries none (instead of one).  Deal with this here.
                let (expr, sep, sep_pos) = match arg_iter.next() {
                    Some(ArgSpan { expr, sep, sep_pos }) => (expr, sep, sep_pos),
                    None => {
                        if !details.allow_missing {
                            return Err(Error::CallableSyntax(key_pos, md));
                        }
                        (None, ArgSep::End, key_pos)
                    }
                };
                let arg_pos = expr.as_ref().map(|e| e.start_pos()).unwrap_or(sep_pos);

                let temp_tag = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;
                let tag = match expr {
                    None => bytecode::VarArgTag::Missing(sep),
                    Some(expr) => {
                        let temp_value = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;
                        let etype = compile_expr(codegen, symtable, temp_value, expr)?;
                        bytecode::VarArgTag::Immediate(sep, etype)
                    }
                };
                validate_syn_argsep(&md, arg_pos, exp_sep, arg_iter.peek().is_none(), sep)?;
                codegen.emit(bytecode::make_load_integer(temp_tag, tag.make_u16()), arg_pos);
            }
        };
    }

    // Variable (repeated) arguments are represented as 1 or 2 consecutive registers.
    //
    // The first register always contains a `VarArgTag`, which indicates the type of
    // separator following the argument and, if an argument is present, its type.
    // The second register is only present if there is an argument.
    //
    // The caller must iterate over all tags until it finds `ArgSep::End`.
    if let Some(syn) = syntax.repeated.as_ref() {
        let mut min_nargs = syntax.singular.len();
        if syn.require_one {
            min_nargs += 1;
        }
        if input_nargs < min_nargs {
            return Err(Error::CallableSyntax(key_pos, md));
        }

        while arg_iter.peek().is_some() {
            let ArgSpan { expr, sep, sep_pos } =
                arg_iter.next().expect("Args and their syntax must advance in unison");

            let arg_pos = expr.as_ref().map(|e| e.start_pos()).unwrap_or(sep_pos);
            let temp_tag = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;

            let tag = match expr {
                None => {
                    if !syn.allow_missing {
                        return Err(Error::CallableSyntax(arg_pos, md));
                    }
                    bytecode::VarArgTag::Missing(sep)
                }

                Some(expr) => match syn.type_syn {
                    RepeatedTypeSyntax::AnyValue => {
                        let temp_value = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;
                        let etype = compile_expr(codegen, symtable, temp_value, expr)?;
                        bytecode::VarArgTag::Immediate(sep, etype)
                    }

                    RepeatedTypeSyntax::TypedValue(vtype) => {
                        let temp_value = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;
                        compile_expr_as_type(codegen, symtable, temp_value, expr, vtype)?;
                        bytecode::VarArgTag::Immediate(sep, vtype)
                    }

                    RepeatedTypeSyntax::VariableRef => {
                        todo!();
                    }
                },
            };
            codegen.emit(bytecode::make_load_integer(temp_tag, tag.make_u16()), arg_pos);
        }
    }

    if arg_iter.peek().is_some() {
        debug_assert!(arg_iter.next().is_some(), "Args and their syntax must advance in unison");
        return Err(Error::CallableSyntax(key_pos, md));
    }

    scope.first().map_err(|e| Error::from_syms(e, key_pos))
}
