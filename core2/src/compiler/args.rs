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

//! Common compilers for callable arguments.

use super::SymbolKey;
use super::syms::LocalSymtable;
use crate::ast::{ArgSpan, CallSpan, Expr, VarRef};
use crate::bytecode::{self, Register};
use crate::callable::CallableMetadata;
use crate::compiler::codegen::Codegen;
use crate::compiler::exprs::{compile_expr, compile_expr_as_type};
use crate::compiler::syms::{self, SymbolPrototype, TempSymtable};
use crate::compiler::{Error, Result};
use crate::reader::LineCol;
use crate::{ArgSep, ArgSepSyntax, ExprType, RepeatedTypeSyntax, SingularArgSyntax};
use std::rc::Rc;

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
    md: &Rc<CallableMetadata>,
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
                return Err(Error::CallableSyntax(pos, md.as_ref().clone()));
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
                return Err(Error::CallableSyntax(pos, md.as_ref().clone()));
            }
            Ok(())
        }

        ArgSepSyntax::End => {
            debug_assert!(is_last);
            Ok(())
        }
    }
}

/// Pre-allocates one local variable for a command output argument, setting its to its default
/// value.
fn define_new_arg(
    symtable: &mut LocalSymtable<'_>,
    vref: &VarRef,
    pos: LineCol,
    codegen: &mut Codegen,
) -> Result<()> {
    let key = SymbolKey::from(&vref.name);
    let vtype = vref.ref_type.unwrap_or(ExprType::Integer);
    let reg = symtable
        .put_local(key, SymbolPrototype::Scalar(vtype))
        .map_err(|e| Error::from_syms(e, pos))?;
    codegen.emit_default(reg, vtype, pos);
    Ok(())
}

/// Pre-allocates local variables for command output arguments.
pub(super) fn define_new_args(
    span: &CallSpan,
    md: &Rc<CallableMetadata>,
    symtable: &mut LocalSymtable<'_>,
    codegen: &mut Codegen,
) -> Result<()> {
    let Some(syntax) = md.find_syntax(span.args.len()) else {
        return Err(Error::CallableSyntax(span.vref_pos, md.as_ref().clone()));
    };

    let mut arg_iter = span.args.iter();

    for syn in syntax.singular.iter() {
        match syn {
            SingularArgSyntax::RequiredValue(_details, _exp_sep) => {
                arg_iter.next().expect("Args and their syntax must advance in unison");
            }

            SingularArgSyntax::RequiredRef(details, _exp_sep) => {
                let ArgSpan { expr, .. } =
                    arg_iter.next().expect("Args and their syntax must advance in unison");

                if let Some(Expr::Symbol(span)) = expr
                    && let Err(syms::Error::UndefinedSymbol(..)) =
                        symtable.get_local_or_global(&span.vref)
                    && details.define_undefined
                {
                    define_new_arg(symtable, &span.vref, span.pos, codegen)?;
                }
            }

            SingularArgSyntax::OptionalValue(_details, _exp_sep) => {
                arg_iter.next();
            }

            SingularArgSyntax::AnyValue(_details, _exp_sep) => {
                arg_iter.next();
            }
        };
    }

    if let Some(syn) = syntax.repeated.as_ref()
        && let RepeatedTypeSyntax::VariableRef = syn.type_syn
    {
        for arg in arg_iter {
            let Some(Expr::Symbol(span)) = &arg.expr else {
                continue;
            };

            let Err(syms::Error::UndefinedSymbol(..)) = symtable.get_local_or_global(&span.vref)
            else {
                continue;
            };

            define_new_arg(symtable, &span.vref, span.pos, codegen)?;
        }
    }

    Ok(())
}

/// Compiles the arguments of a callable invocation.
///
/// Returns the first register containing the compiled arguments. Arguments are laid out as
/// pairs of type tag and value registers, allowing the callable to interpret them at runtime.
///
/// The caller *must* invoke `define_new_args` beforehand when compiling arguments for commands.
/// This separate function is necessary to pre-allocate local variables for any output arguments.
///
/// TODO(jmmv): The `md` metadata is passed by value, not because we want to, but because it's
/// necessary to appease the borrow checker.  The `md` is obtained from the `symtable` in the caller
/// (as a reference) to perform various validations so it is not possible to pass it as input along
/// `symtable`.  An alternative would be to take the symbol `key` as a parameter here and perform
/// another lookup from the symtable.  Or maybe we could make `Metadata` objects static by
/// eliminating the `MetadataBuilder` and pass a static reference here.
pub(super) fn compile_args(
    span: CallSpan,
    md: Rc<CallableMetadata>,
    symtable: &mut TempSymtable<'_, '_>,
    codegen: &mut Codegen,
) -> Result<(Register, Vec<LineCol>)> {
    let key_pos = span.vref_pos;

    let Some(syntax) = md.find_syntax(span.args.len()) else {
        return Err(Error::CallableSyntax(key_pos, md.as_ref().clone()));
    };

    let mut scope = symtable.temp_scope();

    // Collects the source position for each register slot allocated below, in allocation order.
    // This is used to populate the UPCALL instruction's arg_linecols metadata so that callables
    // can query the source position of any argument via `Scope::get_pos`.
    let mut arg_linecols: Vec<LineCol> = Vec::new();

    let input_nargs = span.args.len();
    let mut arg_iter = span.args.into_iter().peekable();

    for syn in syntax.singular.iter() {
        match syn {
            SingularArgSyntax::RequiredValue(details, exp_sep) => {
                let ArgSpan { expr, sep, sep_pos } =
                    arg_iter.next().expect("Args and their syntax must advance in unison");
                let arg_pos = expr.as_ref().map(|e| e.start_pos()).unwrap_or(sep_pos);

                match expr {
                    None => return Err(Error::CallableSyntax(key_pos, md.as_ref().clone())),
                    Some(expr) => {
                        let temp_value = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;
                        arg_linecols.push(arg_pos);
                        compile_expr_as_type(codegen, symtable, temp_value, expr, details.vtype)?;
                        validate_syn_argsep(&md, arg_pos, exp_sep, arg_iter.peek().is_none(), sep)?;
                    }
                }
            }

            SingularArgSyntax::RequiredRef(details, exp_sep) => {
                let ArgSpan { expr, sep, sep_pos } =
                    arg_iter.next().expect("Args and their syntax must advance in unison");
                let arg_pos = expr.as_ref().map(|e| e.start_pos()).unwrap_or(sep_pos);

                match expr {
                    None => return Err(Error::CallableSyntax(key_pos, md.as_ref().clone())),
                    Some(Expr::Symbol(span)) => {
                        let (reg, vtype) = match symtable.get_local_or_global(&span.vref) {
                            Ok((reg, SymbolPrototype::Scalar(vtype))) => (reg, vtype),
                            Ok((_, SymbolPrototype::Array(_))) => {
                                return Err(Error::CallableSyntax(span.pos, md.as_ref().clone()));
                            }
                            Err(e @ syms::Error::UndefinedSymbol(..)) => {
                                if !details.define_undefined {
                                    return Err(Error::from_syms(e, span.pos));
                                }
                                unreachable!("Caller must use define_new_args first for commands");
                            }
                            Err(e) => return Err(Error::from_syms(e, span.pos)),
                        };
                        let temp = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;
                        arg_linecols.push(arg_pos);
                        codegen.emit(bytecode::make_load_register_ptr(temp, vtype, reg), arg_pos);
                        validate_syn_argsep(&md, arg_pos, exp_sep, arg_iter.peek().is_none(), sep)?;
                    }
                    Some(expr) => {
                        return Err(Error::CallableSyntax(expr.start_pos(), md.as_ref().clone()));
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
                arg_linecols.push(arg_pos);
                let tag = match expr {
                    None => bytecode::VarArgTag::Missing(sep),
                    Some(expr) => {
                        let temp_value = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;
                        arg_linecols.push(arg_pos);
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
                            return Err(Error::CallableSyntax(key_pos, md.as_ref().clone()));
                        }
                        (None, ArgSep::End, key_pos)
                    }
                };
                let arg_pos = expr.as_ref().map(|e| e.start_pos()).unwrap_or(sep_pos);

                let temp_tag = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;
                arg_linecols.push(arg_pos);
                let tag = match expr {
                    None => bytecode::VarArgTag::Missing(sep),
                    Some(expr) => {
                        let temp_value = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;
                        arg_linecols.push(arg_pos);
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
            return Err(Error::CallableSyntax(key_pos, md.as_ref().clone()));
        }

        if arg_iter.peek().is_none() {
            let temp_tag = scope.alloc().map_err(|e| Error::from_syms(e, key_pos))?;
            arg_linecols.push(key_pos);
            let tag = bytecode::VarArgTag::Missing(ArgSep::End);
            codegen.emit(bytecode::make_load_integer(temp_tag, tag.make_u16()), key_pos);
        }

        while arg_iter.peek().is_some() {
            let ArgSpan { expr, sep, sep_pos } =
                arg_iter.next().expect("Args and their syntax must advance in unison");

            let arg_pos = expr.as_ref().map(|e| e.start_pos()).unwrap_or(sep_pos);
            let temp_tag = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;
            arg_linecols.push(arg_pos);

            let tag = match expr {
                None => {
                    if !syn.allow_missing {
                        return Err(Error::CallableSyntax(arg_pos, md.as_ref().clone()));
                    }
                    bytecode::VarArgTag::Missing(sep)
                }

                Some(expr) => match syn.type_syn {
                    RepeatedTypeSyntax::AnyValue => {
                        let temp_value = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;
                        arg_linecols.push(arg_pos);
                        let etype = compile_expr(codegen, symtable, temp_value, expr)?;
                        bytecode::VarArgTag::Immediate(sep, etype)
                    }

                    RepeatedTypeSyntax::TypedValue(vtype) => {
                        let temp_value = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;
                        arg_linecols.push(arg_pos);
                        compile_expr_as_type(codegen, symtable, temp_value, expr, vtype)?;
                        bytecode::VarArgTag::Immediate(sep, vtype)
                    }

                    RepeatedTypeSyntax::VariableRef => {
                        let Expr::Symbol(span) = expr else {
                            return Err(Error::CallableSyntax(arg_pos, md.as_ref().clone()));
                        };

                        let (reg, vtype) = match symtable.get_local_or_global(&span.vref) {
                            Ok((reg, SymbolPrototype::Scalar(vtype))) => (reg, vtype),
                            Ok((_, SymbolPrototype::Array(_))) => {
                                return Err(Error::CallableSyntax(arg_pos, md.as_ref().clone()));
                            }
                            Err(syms::Error::UndefinedSymbol(..)) => {
                                unreachable!("Caller must use define_new_args first for commands");
                            }
                            Err(e) => return Err(Error::from_syms(e, span.pos)),
                        };
                        let temp = scope.alloc().map_err(|e| Error::from_syms(e, arg_pos))?;
                        arg_linecols.push(arg_pos);
                        codegen.emit(bytecode::make_load_register_ptr(temp, vtype, reg), arg_pos);
                        bytecode::VarArgTag::Pointer(sep)
                    }
                },
            };
            codegen.emit(bytecode::make_load_integer(temp_tag, tag.make_u16()), arg_pos);
        }
    }

    if arg_iter.peek().is_some() {
        debug_assert!(arg_iter.next().is_some(), "Args and their syntax must advance in unison");
        return Err(Error::CallableSyntax(key_pos, md.as_ref().clone()));
    }

    let first_reg = scope.first().map_err(|e| Error::from_syms(e, key_pos))?;
    Ok((first_reg, arg_linecols))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CallableMetadataBuilder;
    use crate::callable::RepeatedSyntax;
    use crate::compiler::syms::GlobalSymtable;
    use std::borrow::Cow;
    use std::collections::HashMap;

    #[test]
    fn test_compile_args_materializes_missing_repeated_tag() -> Result<()> {
        let pos = LineCol { line: 1, col: 1 };
        let md = CallableMetadataBuilder::new("OUT")
            .with_syntax(&[(
                &[],
                Some(&RepeatedSyntax {
                    name: Cow::Borrowed("arg"),
                    type_syn: RepeatedTypeSyntax::AnyValue,
                    sep: ArgSepSyntax::Exactly(ArgSep::Short),
                    require_one: false,
                    allow_missing: false,
                }),
            )])
            .test_build();

        let mut codegen = Codegen::default();

        let upcalls = HashMap::default();
        let mut global = GlobalSymtable::new(upcalls);
        let mut local = global.enter_scope();
        let (first_reg, arg_linecols) = {
            let mut symtable = local.frozen();
            compile_args(
                CallSpan { vref: VarRef::new("OUT", None), vref_pos: pos, args: vec![] },
                md,
                &mut symtable,
                &mut codegen,
            )?
        };
        assert_eq!(Register::local(0).unwrap(), first_reg);
        assert_eq!(vec![pos], arg_linecols);

        let upcall = codegen.get_upcall(SymbolKey::from("OUT"), None, pos)?;
        let addr = codegen.emit(bytecode::make_upcall(upcall, first_reg), pos);
        codegen.set_arg_linecols(addr, arg_linecols);
        codegen.emit(bytecode::make_eof(), LineCol { line: 0, col: 0 });

        let image = codegen.build_image(HashMap::default(), vec![])?;
        assert_eq!(
            vec![
                "0000:   LOADI       R64, 0              ; 1:1".to_owned(),
                "0001:   UPCALL      0, R64              ; 1:1, OUT".to_owned(),
                "0002:   EOF                             ; 0:0".to_owned(),
            ],
            image.disasm()
        );
        Ok(())
    }
}
