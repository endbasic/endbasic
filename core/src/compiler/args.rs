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

//! Common compilers for callable arguments.

use crate::ast::*;
use crate::bytecode::*;
use crate::compiler::exprs::{compile_expr, compile_expr_as_type};
use crate::compiler::{ExprType, SymbolPrototype, SymbolsTable};
use crate::exec::ValueTag;
use crate::reader::LineCol;
use crate::syms::{CallError, SymbolKey};
use std::ops::RangeInclusive;

/// Result for argument compilation return values.
type Result<T> = std::result::Result<T, CallError>;

/// Details to compile a required scalar parameter.
#[derive(Debug)]
pub struct RequiredValueSyntax {
    /// The name of the parameter for help purposes.
    pub name: &'static str,

    /// The type of the expected parameter.
    pub vtype: ExprType,
}

/// Details to compile a required reference parameter.
#[derive(Debug)]
pub struct RequiredRefSyntax {
    /// The name of the parameter for help purposes.
    pub name: &'static str,

    /// If true, require an array reference; if false, a variable reference.
    pub require_array: bool,

    /// If true, allow references to undefined variables because the command will define them when
    /// missing.  Can only be set to true for commands, not functions, and `require_array` must be
    /// false.
    pub define_undefined: bool,
}

/// Details to compile an optional scalar parameter.
///
/// Optional parameters are only supported in commands.
#[derive(Debug)]
pub struct OptionalValueSyntax {
    /// The name of the parameter for help purposes.
    pub name: &'static str,

    /// The type of the expected parameter.
    pub vtype: ExprType,

    /// Value to push onto the stack when the parameter is missing.
    pub missing_value: i32,

    /// Value to push onto the stack when the parameter is present, after which the stack contains
    /// the parameter value.
    pub present_value: i32,
}

/// Details to describe the type of a repeated parameter.
#[derive(Debug)]
pub enum RepeatedTypeSyntax {
    /// Allows any value type, including empty arguments.  The values pushed onto the stack have
    /// the same semantics as those pushed by `AnyValueSyntax`.
    AnyValue,

    /// Expects a value of the given type.
    TypedValue(ExprType),

    /// Expects a reference to a variable (not an array) and allows the variables to not be defined.
    VariableRef,
}

/// Details to compile a repeated parameter.
///
/// The repeated parameter must appear after all singular positional parameters.
#[derive(Debug)]
pub struct RepeatedSyntax {
    /// The name of the parameter for help purposes.
    pub name: &'static str,

    /// The type of the expected parameters.
    pub type_syn: RepeatedTypeSyntax,

    /// The separator to expect between the repeated parameters.  For functions, this must be the
    /// long separator (the comma).
    pub sep: ArgSepSyntax,

    /// Whether the repeated parameter must at least have one element or not.
    pub require_one: bool,

    /// Whether to allow any parameter to not be present or not.  Can only be true for commands.
    pub allow_missing: bool,
}

impl RepeatedSyntax {
    /// Formats the repeated argument syntax for help purposes into `output`.
    ///
    /// `last_singular_sep` contains the separator of the last singular argument syntax, if any,
    /// which we need to place inside of the optional group.
    fn describe(&self, output: &mut String, last_singular_sep: Option<&ArgSepSyntax>) {
        if !self.require_one {
            output.push('[');
        }

        if let Some(sep) = last_singular_sep {
            sep.describe(output);
        }

        output.push_str(self.name);
        output.push('1');
        if let RepeatedTypeSyntax::TypedValue(vtype) = self.type_syn {
            output.push(vtype.annotation());
        }

        if self.require_one {
            output.push('[');
        }

        self.sep.describe(output);
        output.push_str("..");
        self.sep.describe(output);

        output.push_str(self.name);
        output.push('N');
        if let RepeatedTypeSyntax::TypedValue(vtype) = self.type_syn {
            output.push(vtype.annotation());
        }

        output.push(']');
    }
}

/// Details to compile a parameter of any scalar type.
#[derive(Debug)]
pub struct AnyValueSyntax {
    /// The name of the parameter for help purposes.
    pub name: &'static str,

    /// Whether to allow the parameter to not be present or not.  Can only be true for commands.
    pub allow_missing: bool,
}

/// Details to process an argument separator.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum ArgSepSyntax {
    /// The argument separator must exactly be the one give.
    Exactly(ArgSep),

    /// The argument separator may be any of the ones given.
    OneOf(ArgSep, ArgSep),

    /// The argument separator is the end of the call.
    End,
}

impl ArgSepSyntax {
    /// Formats the argument separator for help purposes into `output`.
    fn describe(&self, output: &mut String) {
        match self {
            ArgSepSyntax::Exactly(sep) => {
                let (text, needs_space) = sep.describe();

                if !text.is_empty() && needs_space {
                    output.push(' ');
                }
                output.push_str(text);
                if !text.is_empty() {
                    output.push(' ');
                }
            }

            ArgSepSyntax::OneOf(sep1, sep2) => {
                let (text1, _needs_space1) = sep1.describe();
                let (text2, _needs_space2) = sep2.describe();

                output.push(' ');
                output.push_str(&format!("<{}|{}>", text1, text2));
                output.push(' ');
            }

            ArgSepSyntax::End => (),
        };
    }
}

/// Details to process a non-repeated argument.
///
/// Every item in this enum is composed of a struct that provides the details on the parameter and
/// a struct that provides the details on how this parameter is separated from the next.
#[derive(Debug)]
pub enum SingularArgSyntax {
    /// A required scalar value.
    RequiredValue(RequiredValueSyntax, ArgSepSyntax),

    /// A required reference.
    RequiredRef(RequiredRefSyntax, ArgSepSyntax),

    /// An optional scalar value.
    OptionalValue(OptionalValueSyntax, ArgSepSyntax),

    /// A required scalar value of any type.
    AnyValue(AnyValueSyntax, ArgSepSyntax),
}

/// Details to process the arguments of a callable.
///
/// Note that the description of function arguments is more restricted than that of commands.
/// The arguments compiler panics when these preconditions aren't met with the rationale that
/// builtin functions must never be ill-defined.
// TODO(jmmv): It might be nice to try to express these restrictions in the type system, but
// things are already too verbose as they are...
#[derive(Clone, Debug)]
pub(crate) struct CallableSyntax {
    /// Ordered list of singular arguments that appear before repeated arguments.
    singular: &'static [SingularArgSyntax],

    /// Details on the repeated argument allowed after singular arguments.
    repeated: Option<&'static RepeatedSyntax>,
}

impl CallableSyntax {
    /// Creates a new callable arguments definition from its parts.
    pub(crate) fn new(
        singular: &'static [SingularArgSyntax],
        repeated: Option<&'static RepeatedSyntax>,
    ) -> Self {
        Self { singular, repeated }
    }

    /// Computes the range of the expected number of parameters for this syntax.
    fn expected_nargs(&self) -> RangeInclusive<usize> {
        let mut min = self.singular.len();
        let mut max = self.singular.len();
        if let Some(syn) = self.repeated.as_ref() {
            if syn.require_one {
                min += 1;
            }
            max = usize::MAX;
        }
        min..=max
    }

    /// Produces a user-friendly description of this callable syntax.
    pub(crate) fn describe(&self) -> String {
        let mut description = String::new();
        let mut last_singular_sep = None;
        for (i, s) in self.singular.iter().enumerate() {
            let sep = match s {
                SingularArgSyntax::RequiredValue(details, sep) => {
                    description.push_str(details.name);
                    description.push(details.vtype.annotation());
                    sep
                }

                SingularArgSyntax::RequiredRef(details, sep) => {
                    description.push_str(details.name);
                    sep
                }

                SingularArgSyntax::OptionalValue(details, sep) => {
                    description.push('[');
                    description.push_str(details.name);
                    description.push(details.vtype.annotation());
                    description.push(']');
                    sep
                }

                SingularArgSyntax::AnyValue(details, sep) => {
                    if details.allow_missing {
                        description.push('[');
                    }
                    description.push_str(details.name);
                    if details.allow_missing {
                        description.push(']');
                    }
                    sep
                }
            };

            if self.repeated.is_none() || i < self.singular.len() - 1 {
                sep.describe(&mut description);
            }
            if i == self.singular.len() - 1 {
                last_singular_sep = Some(sep);
            }
        }

        if let Some(syn) = self.repeated {
            syn.describe(&mut description, last_singular_sep);
        }

        description
    }
}

/// Compiles an argument that requires a reference.
///
/// If the reference does not exist and the syntax allowed undefined symbols, returns the details
/// for the symbol to insert into the symbols table, which the caller must handle because we do
/// not have mutable access to the `symtable` here.
fn compile_required_ref(
    instrs: &mut Vec<Instruction>,
    symtable: &SymbolsTable,
    require_array: bool,
    define_undefined: bool,
    expr: Option<Expr>,
) -> Result<Option<(SymbolKey, SymbolPrototype)>> {
    match expr {
        Some(Expr::Symbol(span)) => {
            let key = SymbolKey::from(span.vref.name());
            match symtable.get(&key) {
                None => {
                    if !define_undefined {
                        let message = if require_array {
                            format!("Undefined array {}", span.vref.name())
                        } else {
                            format!("Undefined variable {}", span.vref.name())
                        };
                        return Err(CallError::ArgumentError(span.pos, message));
                    }
                    debug_assert!(!require_array);

                    let vtype = ExprType::from_vartype(span.vref.ref_type(), ExprType::Integer);

                    if !span.vref.accepts(vtype) {
                        return Err(CallError::ArgumentError(
                            span.pos,
                            format!("Incompatible type annotation in {} reference", span.vref),
                        ));
                    }

                    instrs.push(Instruction::LoadRef(key.clone(), vtype, span.pos));
                    Ok(Some((key, SymbolPrototype::Variable(vtype))))
                }

                Some(SymbolPrototype::Array(vtype, _)) => {
                    let vtype = *vtype;

                    if !span.vref.accepts(vtype) {
                        return Err(CallError::ArgumentError(
                            span.pos,
                            format!("Incompatible type annotation in {} reference", span.vref),
                        ));
                    }

                    if !require_array {
                        return Err(CallError::ArgumentError(
                            span.pos,
                            format!("{} is not a variable reference", span.vref),
                        ));
                    }

                    instrs.push(Instruction::LoadRef(key, vtype, span.pos));
                    Ok(None)
                }

                Some(SymbolPrototype::Variable(vtype)) => {
                    let vtype = *vtype;

                    if !span.vref.accepts(vtype) {
                        return Err(CallError::ArgumentError(
                            span.pos,
                            format!("Incompatible type annotation in {} reference", span.vref),
                        ));
                    }

                    if require_array {
                        return Err(CallError::ArgumentError(
                            span.pos,
                            format!("{} is not an array reference", span.vref),
                        ));
                    }

                    instrs.push(Instruction::LoadRef(key, vtype, span.pos));
                    Ok(None)
                }

                Some(SymbolPrototype::Callable(md)) => {
                    if !span.vref.accepts_callable(md.return_type()) {
                        return Err(CallError::ArgumentError(
                            span.pos,
                            format!("Incompatible type annotation in {} reference", span.vref),
                        ));
                    }

                    Err(CallError::ArgumentError(
                        span.pos,
                        format!("{} is not an array nor a function", span.vref.name()),
                    ))
                }
            }
        }

        Some(expr) => {
            let message = if require_array {
                "Requires an array reference, not a value"
            } else {
                "Requires a variable reference, not a value"
            };
            Err(CallError::ArgumentError(expr.start_pos(), message.to_owned()))
        }

        None => Err(CallError::SyntaxError),
    }
}

/// Locates the syntax definition that can parse the given number of arguments.
///
/// Panics if more than one syntax definition applies.
fn find_syntax(syntaxes: &[CallableSyntax], nargs: usize) -> Result<&CallableSyntax> {
    let mut matches = syntaxes.iter().filter(|s| s.expected_nargs().contains(&nargs));
    let syntax = matches.next();
    debug_assert!(matches.next().is_none(), "Ambiguous syntax definitions");
    match syntax {
        Some(syntax) => Ok(syntax),
        None => Err(CallError::SyntaxError),
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
fn compile_syn_argsep(
    instrs: &mut Vec<Instruction>,
    syn: &ArgSepSyntax,
    is_last: bool,
    sep: ArgSep,
    sep_pos: LineCol,
    sep_tag_pc: Address,
) -> Result<usize> {
    debug_assert!(
        (!is_last || sep == ArgSep::End) && (is_last || sep != ArgSep::End),
        "Parser can only supply an End separator in the last argument"
    );

    match syn {
        ArgSepSyntax::Exactly(exp_sep) => {
            debug_assert!(*exp_sep != ArgSep::End, "Use ArgSepSyntax::End");
            if sep != ArgSep::End && sep != *exp_sep {
                return Err(CallError::SyntaxError);
            }
            Ok(0)
        }

        ArgSepSyntax::OneOf(exp_sep1, exp_sep2) => {
            debug_assert!(*exp_sep1 != ArgSep::End, "Use ArgSepSyntax::End");
            debug_assert!(*exp_sep2 != ArgSep::End, "Use ArgSepSyntax::End");
            if sep == ArgSep::End {
                Ok(0)
            } else {
                if sep != *exp_sep1 && sep != *exp_sep2 {
                    return Err(CallError::SyntaxError);
                }
                instrs.insert(sep_tag_pc, Instruction::PushInteger(sep as i32, sep_pos));
                Ok(1)
            }
        }

        ArgSepSyntax::End => {
            debug_assert!(is_last);
            Ok(0)
        }
    }
}

/// Compiles a single expression, expecting it to be of a `target` type.  Applies casts if
/// possible.
fn compile_arg_expr(
    instrs: &mut Vec<Instruction>,
    symtable: &SymbolsTable,
    expr: Expr,
    target: ExprType,
) -> Result<()> {
    match compile_expr_as_type(instrs, symtable, expr, target) {
        Ok(()) => Ok(()),
        Err(e) => Err(CallError::ArgumentError(e.pos, e.message)),
    }
}

/// Parses the arguments to a command or a function and generates expressions to compute them.
///
/// Returns the number of arguments that the instructions added to `instrs` will push into the
/// stack and returns the list of new symbols that need to be inserted into `symtable`.
fn compile_args(
    syntaxes: &[CallableSyntax],
    instrs: &mut Vec<Instruction>,
    symtable: &SymbolsTable,
    _pos: LineCol,
    args: Vec<ArgSpan>,
) -> Result<(usize, Vec<(SymbolKey, SymbolPrototype)>)> {
    let syntax = find_syntax(syntaxes, args.len())?;

    let input_nargs = args.len();
    let mut aiter = args.into_iter().rev();

    let mut nargs = 0;
    let mut to_insert = vec![];

    let mut remaining;
    if let Some(syn) = syntax.repeated.as_ref() {
        let mut min_nargs = syntax.singular.len();
        if syn.require_one {
            min_nargs += 1;
        }
        if input_nargs < min_nargs {
            return Err(CallError::SyntaxError);
        }

        let need_tags = syn.allow_missing || matches!(syn.type_syn, RepeatedTypeSyntax::AnyValue);

        remaining = input_nargs;
        while remaining > syntax.singular.len() {
            let span = aiter.next().expect("Args and their syntax must advance in unison");

            let sep_tag_pc = instrs.len();

            match span.expr {
                Some(expr) => {
                    let pos = expr.start_pos();
                    match syn.type_syn {
                        RepeatedTypeSyntax::AnyValue => {
                            debug_assert!(need_tags);
                            let etype = compile_expr(instrs, symtable, expr, false)?;
                            instrs
                                .push(Instruction::PushInteger(ValueTag::from(etype) as i32, pos));
                            nargs += 2;
                        }

                        RepeatedTypeSyntax::VariableRef => {
                            let to_insert_one =
                                compile_required_ref(instrs, symtable, false, true, Some(expr))?;
                            if let Some(to_insert_one) = to_insert_one {
                                to_insert.push(to_insert_one);
                            }
                            nargs += 1;
                        }

                        RepeatedTypeSyntax::TypedValue(vtype) => {
                            compile_arg_expr(instrs, symtable, expr, vtype)?;
                            if need_tags {
                                instrs.push(Instruction::PushInteger(
                                    ValueTag::from(vtype) as i32,
                                    pos,
                                ));
                                nargs += 2;
                            } else {
                                nargs += 1;
                            }
                        }
                    }
                }
                None => {
                    if !syn.allow_missing {
                        return Err(CallError::SyntaxError);
                    }
                    instrs.push(Instruction::PushInteger(ValueTag::Missing as i32, span.sep_pos));
                    nargs += 1;
                }
            }

            nargs += compile_syn_argsep(
                instrs,
                &syn.sep,
                input_nargs == remaining,
                span.sep,
                span.sep_pos,
                sep_tag_pc,
            )?;

            remaining -= 1;
        }
    } else {
        remaining = syntax.singular.len();
    }

    for syn in syntax.singular.iter().rev() {
        let span = aiter.next().expect("Args and their syntax must advance in unison");

        let sep_tag_pc = instrs.len();

        let exp_sep = match syn {
            SingularArgSyntax::RequiredValue(details, sep) => {
                match span.expr {
                    Some(expr) => {
                        compile_arg_expr(instrs, symtable, expr, details.vtype)?;
                        nargs += 1;
                    }
                    None => return Err(CallError::SyntaxError),
                }
                sep
            }

            SingularArgSyntax::RequiredRef(details, sep) => {
                let to_insert_one = compile_required_ref(
                    instrs,
                    symtable,
                    details.require_array,
                    details.define_undefined,
                    span.expr,
                )?;
                if let Some(to_insert_one) = to_insert_one {
                    to_insert.push(to_insert_one);
                }
                nargs += 1;
                sep
            }

            SingularArgSyntax::OptionalValue(details, sep) => {
                let (tag, pos) = match span.expr {
                    Some(expr) => {
                        let pos = expr.start_pos();
                        compile_arg_expr(instrs, symtable, expr, details.vtype)?;
                        nargs += 1;
                        (details.present_value, pos)
                    }
                    None => (details.missing_value, span.sep_pos),
                };
                instrs.push(Instruction::PushInteger(tag, pos));
                nargs += 1;
                sep
            }

            SingularArgSyntax::AnyValue(details, sep) => {
                let (tag, pos) = match span.expr {
                    Some(expr) => {
                        let pos = expr.start_pos();
                        let etype = compile_expr(instrs, symtable, expr, false)?;
                        nargs += 2;
                        (ValueTag::from(etype), pos)
                    }
                    None => {
                        if !details.allow_missing {
                            return Err(CallError::ArgumentError(
                                span.sep_pos,
                                "Missing expression before separator".to_owned(),
                            ));
                        }
                        nargs += 1;
                        (ValueTag::Missing, span.sep_pos)
                    }
                };
                instrs.push(Instruction::PushInteger(tag as i32, pos));
                sep
            }
        };

        nargs += compile_syn_argsep(
            instrs,
            exp_sep,
            input_nargs == remaining,
            span.sep,
            span.sep_pos,
            sep_tag_pc,
        )?;

        remaining -= 1;
    }

    Ok((nargs, to_insert))
}

/// Parses the arguments to a buitin command and generates expressions to compute them.
///
/// This can be used to help the runtime by doing type checking during compilation and then
/// allowing the runtime to assume that the values on the stack are correctly typed.
pub(super) fn compile_command_args(
    syntaxes: &[CallableSyntax],
    instrs: &mut Vec<Instruction>,
    symtable: &mut SymbolsTable,
    pos: LineCol,
    args: Vec<ArgSpan>,
) -> Result<usize> {
    let (nargs, to_insert) = compile_args(syntaxes, instrs, symtable, pos, args)?;
    for (key, proto) in to_insert {
        if !symtable.contains_key(&key) {
            symtable.insert(key, proto);
        }
    }
    Ok(nargs)
}

/// Parses the arguments to a function and generates expressions to compute them.
///
/// This can be used to help the runtime by doing type checking during compilation and then
/// allowing the runtime to assume that the values on the stack are correctly typed.
pub(super) fn compile_function_args(
    syntaxes: &[CallableSyntax],
    instrs: &mut Vec<Instruction>,
    symtable: &SymbolsTable,
    pos: LineCol,
    args: Vec<ArgSpan>,
) -> Result<usize> {
    let (nargs, to_insert) = compile_args(syntaxes, instrs, symtable, pos, args)?;
    debug_assert!(to_insert.is_empty());
    Ok(nargs)
}

#[cfg(test)]
mod testutils {
    use super::*;
    use std::collections::HashMap;

    /// Syntactic sugar to instantiate a `LineCol` for tests.
    pub(super) fn lc(line: usize, col: usize) -> LineCol {
        LineCol { line, col }
    }

    /// Builder pattern to instantiate a test scenario.
    #[derive(Default)]
    #[must_use]
    pub(super) struct Tester {
        syntaxes: Vec<CallableSyntax>,
        symtable: SymbolsTable,
    }

    impl Tester {
        /// Registers a syntax definition in the arguments compiler.
        pub(super) fn syntax(
            mut self,
            singular: &'static [SingularArgSyntax],
            repeated: Option<&'static RepeatedSyntax>,
        ) -> Self {
            self.syntaxes.push(CallableSyntax::new(singular, repeated));
            self
        }

        /// Registers a pre-existing symbol in the symbols table.
        pub(super) fn symbol(mut self, key: &str, proto: SymbolPrototype) -> Self {
            self.symtable.insert(SymbolKey::from(key), proto);
            self
        }

        /// Feeds command `args` into the arguments compiler and returns a checker to validate
        /// expectations.
        pub(super) fn compile_command<A: Into<Vec<ArgSpan>>>(mut self, args: A) -> Checker {
            let args = args.into();
            let mut instrs = vec![
                // Start with one instruction to validate that the args compiler doesn't touch it.
                Instruction::Nop,
            ];
            let result = compile_command_args(
                &self.syntaxes,
                &mut instrs,
                &mut self.symtable,
                lc(1000, 2000),
                args,
            );
            Checker {
                result,
                instrs,
                symtable: self.symtable,
                exp_result: Ok(0),
                exp_instrs: vec![Instruction::Nop],
                exp_vars: HashMap::default(),
            }
        }
    }

    /// Builder pattern to validate expectations in a test scenario.
    #[must_use]
    pub(super) struct Checker {
        result: Result<usize>,
        instrs: Vec<Instruction>,
        symtable: SymbolsTable,
        exp_result: Result<usize>,
        exp_instrs: Vec<Instruction>,
        exp_vars: HashMap<SymbolKey, ExprType>,
    }

    impl Checker {
        /// Expects the compilation to succeeded and produce `nargs` arguments.
        pub(super) fn exp_nargs(mut self, nargs: usize) -> Self {
            self.exp_result = Ok(nargs);
            self
        }

        /// Expects the compilation to fail with the given `error`.
        pub(super) fn exp_error(mut self, error: CallError) -> Self {
            self.exp_result = Err(error);
            self
        }

        /// Adds the given instruction to the expected instructions on success.
        pub(super) fn exp_instr(mut self, instr: Instruction) -> Self {
            self.exp_instrs.push(instr);
            self
        }

        /// Expects the compilation to define a new variable `key` of type `etype`.
        pub(super) fn exp_symbol<K: AsRef<str>>(mut self, key: K, etype: ExprType) -> Self {
            self.exp_vars.insert(SymbolKey::from(key), etype);
            self
        }

        /// Formats a `CallError` as a string to simplify comparisons.
        fn format_call_error(e: CallError) -> String {
            match e {
                CallError::ArgumentError(pos, e) => format!("{}:{}: {}", pos.line, pos.col, e),
                CallError::EvalError(pos, e) => format!("{}:{}: {}", pos.line, pos.col, e),
                CallError::InternalError(_pos, e) => panic!("Must not happen here: {}", e),
                CallError::IoError(e) => panic!("Must not happen here: {}", e),
                CallError::NestedError(e) => panic!("Must not happen here: {}", e),
                CallError::SyntaxError => "Syntax error".to_owned(),
            }
        }

        /// Checks that the compilation ended with the configured expectations.
        pub(super) fn check(self) {
            let is_ok = self.result.is_ok();
            assert_eq!(
                self.exp_result.map_err(Self::format_call_error),
                self.result.map_err(Self::format_call_error),
            );

            if !is_ok {
                return;
            }

            assert_eq!(self.exp_instrs, self.instrs);

            let mut exp_keys = self.symtable.keys();
            for (key, exp_etype) in &self.exp_vars {
                match self.symtable.get(key) {
                    Some(SymbolPrototype::Variable(etype)) => {
                        assert_eq!(
                            exp_etype, etype,
                            "Variable {} was defined with the wrong type",
                            key
                        );
                    }
                    Some(_) => panic!("Symbol {} was defined but not as a variable", key),
                    None => panic!("Symbol {} was not defined", key),
                }
                exp_keys.insert(key);
            }

            assert_eq!(exp_keys, self.symtable.keys(), "Unexpected variables defined");
        }
    }
}

#[cfg(test)]
mod description_tests {
    use super::*;

    #[test]
    fn test_no_args() {
        assert_eq!("", CallableSyntax::new(&[], None).describe());
    }

    #[test]
    fn test_singular_required_value() {
        assert_eq!(
            "the-arg%",
            CallableSyntax::new(
                &[SingularArgSyntax::RequiredValue(
                    RequiredValueSyntax { name: "the-arg", vtype: ExprType::Integer },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .describe(),
        );
    }

    #[test]
    fn test_singular_required_ref() {
        assert_eq!(
            "the-arg",
            CallableSyntax::new(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax {
                        name: "the-arg",
                        require_array: false,
                        define_undefined: false
                    },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .describe()
        );
    }

    #[test]
    fn test_singular_optional_value() {
        assert_eq!(
            "[the-arg%]",
            CallableSyntax::new(
                &[SingularArgSyntax::OptionalValue(
                    OptionalValueSyntax {
                        name: "the-arg",
                        vtype: ExprType::Integer,
                        missing_value: 0,
                        present_value: 1,
                    },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .describe()
        );
    }

    #[test]
    fn test_singular_any_value_required() {
        assert_eq!(
            "the-arg",
            CallableSyntax::new(
                &[SingularArgSyntax::AnyValue(
                    AnyValueSyntax { name: "the-arg", allow_missing: false },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .describe()
        );
    }

    #[test]
    fn test_singular_any_value_optional() {
        assert_eq!(
            "[the-arg]",
            CallableSyntax::new(
                &[SingularArgSyntax::AnyValue(
                    AnyValueSyntax { name: "the-arg", allow_missing: true },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .describe()
        );
    }

    #[test]
    fn test_singular_exactly_separators() {
        assert_eq!(
            "a; b AS c, d",
            CallableSyntax::new(
                &[
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "a", allow_missing: false },
                        ArgSepSyntax::Exactly(ArgSep::Short),
                    ),
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "b", allow_missing: false },
                        ArgSepSyntax::Exactly(ArgSep::As),
                    ),
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "c", allow_missing: false },
                        ArgSepSyntax::Exactly(ArgSep::Long),
                    ),
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "d", allow_missing: false },
                        ArgSepSyntax::Exactly(ArgSep::End),
                    ),
                ],
                None,
            )
            .describe()
        );
    }

    #[test]
    fn test_singular_oneof_separators() {
        assert_eq!(
            "a <;|,> b <AS|,> c",
            CallableSyntax::new(
                &[
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "a", allow_missing: false },
                        ArgSepSyntax::OneOf(ArgSep::Short, ArgSep::Long),
                    ),
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "b", allow_missing: false },
                        ArgSepSyntax::OneOf(ArgSep::As, ArgSep::Long),
                    ),
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "c", allow_missing: false },
                        ArgSepSyntax::Exactly(ArgSep::End),
                    ),
                ],
                None,
            )
            .describe()
        );
    }

    #[test]
    fn test_repeated_require_one() {
        assert_eq!(
            "rep1[; ..; repN]",
            CallableSyntax::new(
                &[],
                Some(&RepeatedSyntax {
                    name: "rep",
                    type_syn: RepeatedTypeSyntax::AnyValue,
                    sep: ArgSepSyntax::Exactly(ArgSep::Short),
                    require_one: true,
                    allow_missing: false,
                }),
            )
            .describe()
        );
    }

    #[test]
    fn test_repeated_allow_missing() {
        assert_eq!(
            "[rep1, .., repN]",
            CallableSyntax::new(
                &[],
                Some(&RepeatedSyntax {
                    name: "rep",
                    type_syn: RepeatedTypeSyntax::AnyValue,
                    sep: ArgSepSyntax::Exactly(ArgSep::Long),
                    require_one: false,
                    allow_missing: true,
                }),
            )
            .describe()
        );
    }

    #[test]
    fn test_repeated_value() {
        assert_eq!(
            "rep1$[ AS .. AS repN$]",
            CallableSyntax::new(
                &[],
                Some(&RepeatedSyntax {
                    name: "rep",
                    type_syn: RepeatedTypeSyntax::TypedValue(ExprType::Text),
                    sep: ArgSepSyntax::Exactly(ArgSep::As),
                    require_one: true,
                    allow_missing: false,
                }),
            )
            .describe()
        );
    }

    #[test]
    fn test_repeated_ref() {
        assert_eq!(
            "rep1[ AS .. AS repN]",
            CallableSyntax::new(
                &[],
                Some(&RepeatedSyntax {
                    name: "rep",
                    type_syn: RepeatedTypeSyntax::VariableRef,
                    sep: ArgSepSyntax::Exactly(ArgSep::As),
                    require_one: true,
                    allow_missing: false,
                }),
            )
            .describe()
        );
    }

    #[test]
    fn test_singular_and_repeated() {
        assert_eq!(
            "arg%[, rep1 <;|,> .. <;|,> repN]",
            CallableSyntax::new(
                &[SingularArgSyntax::RequiredValue(
                    RequiredValueSyntax { name: "arg", vtype: ExprType::Integer },
                    ArgSepSyntax::Exactly(ArgSep::Long),
                )],
                Some(&RepeatedSyntax {
                    name: "rep",
                    type_syn: RepeatedTypeSyntax::AnyValue,
                    sep: ArgSepSyntax::OneOf(ArgSep::Short, ArgSep::Long),
                    require_one: false,
                    allow_missing: false,
                }),
            )
            .describe()
        );
    }
}

#[cfg(test)]
mod compile_tests {
    use super::testutils::*;
    use super::*;

    #[test]
    fn test_no_syntaxes_yields_error() {
        Tester::default().compile_command([]).exp_error(CallError::SyntaxError).check();
    }

    #[test]
    fn test_no_args_ok() {
        Tester::default().syntax(&[], None).compile_command([]).check();
    }

    #[test]
    fn test_no_args_mismatch() {
        Tester::default()
            .syntax(&[], None)
            .compile_command([ArgSpan {
                expr: Some(Expr::Integer(IntegerSpan { value: 3, pos: lc(1, 2) })),
                sep: ArgSep::End,
                sep_pos: lc(1, 3),
            }])
            .exp_error(CallError::SyntaxError)
            .check();
    }

    #[test]
    fn test_one_required_value_ok() {
        Tester::default()
            .syntax(
                &[SingularArgSyntax::RequiredValue(
                    RequiredValueSyntax { name: "arg1", vtype: ExprType::Integer },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Integer(IntegerSpan { value: 3, pos: lc(1, 2) })),
                sep: ArgSep::End,
                sep_pos: lc(1, 3),
            }])
            .exp_instr(Instruction::PushInteger(3, lc(1, 2)))
            .exp_nargs(1)
            .check();
    }

    #[test]
    fn test_one_required_value_type_promotion() {
        Tester::default()
            .syntax(
                &[SingularArgSyntax::RequiredValue(
                    RequiredValueSyntax { name: "arg1", vtype: ExprType::Integer },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Double(DoubleSpan { value: 3.0, pos: lc(1, 2) })),
                sep: ArgSep::End,
                sep_pos: lc(1, 5),
            }])
            .exp_instr(Instruction::PushDouble(3.0, lc(1, 2)))
            .exp_instr(Instruction::DoubleToInteger)
            .exp_nargs(1)
            .check();
    }

    #[test]
    fn test_one_required_ref_variable_ok() {
        Tester::default()
            .symbol("foo", SymbolPrototype::Variable(ExprType::Text))
            .syntax(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax {
                        name: "ref",
                        require_array: false,
                        define_undefined: false,
                    },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Symbol(SymbolSpan {
                    vref: VarRef::new("foo", VarType::Auto),
                    pos: lc(1, 2),
                })),
                sep: ArgSep::End,
                sep_pos: lc(1, 5),
            }])
            .exp_instr(Instruction::LoadRef(SymbolKey::from("foo"), ExprType::Text, lc(1, 2)))
            .exp_nargs(1)
            .check();
    }

    #[test]
    fn test_one_required_ref_variable_not_defined() {
        Tester::default()
            .syntax(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax {
                        name: "ref",
                        require_array: false,
                        define_undefined: false,
                    },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Symbol(SymbolSpan {
                    vref: VarRef::new("foo", VarType::Auto),
                    pos: lc(1, 2),
                })),
                sep: ArgSep::End,
                sep_pos: lc(1, 5),
            }])
            .exp_error(CallError::ArgumentError(lc(1, 2), "Undefined variable foo".to_owned()))
            .check();
    }

    #[test]
    fn test_one_required_ref_variable_disallow_value() {
        Tester::default()
            .syntax(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax {
                        name: "ref",
                        require_array: false,
                        define_undefined: false,
                    },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Integer(IntegerSpan { value: 5, pos: lc(1, 2) })),
                sep: ArgSep::End,
                sep_pos: lc(1, 5),
            }])
            .exp_error(CallError::ArgumentError(
                lc(1, 2),
                "Requires a variable reference, not a value".to_owned(),
            ))
            .check();
    }

    #[test]
    fn test_one_required_ref_variable_wrong_type() {
        Tester::default()
            .symbol("foo", SymbolPrototype::Array(ExprType::Text, 1))
            .syntax(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax {
                        name: "ref",
                        require_array: false,
                        define_undefined: false,
                    },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Symbol(SymbolSpan {
                    vref: VarRef::new("foo", VarType::Auto),
                    pos: lc(1, 2),
                })),
                sep: ArgSep::End,
                sep_pos: lc(1, 5),
            }])
            .exp_error(CallError::ArgumentError(
                lc(1, 2),
                "foo is not a variable reference".to_owned(),
            ))
            .check();
    }

    #[test]
    fn test_one_required_ref_variable_wrong_annotation() {
        Tester::default()
            .symbol("foo", SymbolPrototype::Variable(ExprType::Text))
            .syntax(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax {
                        name: "ref",
                        require_array: false,
                        define_undefined: false,
                    },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Symbol(SymbolSpan {
                    vref: VarRef::new("foo", VarType::Integer),
                    pos: lc(1, 2),
                })),
                sep: ArgSep::End,
                sep_pos: lc(1, 5),
            }])
            .exp_error(CallError::ArgumentError(
                lc(1, 2),
                "Incompatible type annotation in foo% reference".to_owned(),
            ))
            .check();
    }

    #[test]
    fn test_one_required_ref_variable_define_undefined_default_type() {
        Tester::default()
            .syntax(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax { name: "ref", require_array: false, define_undefined: true },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Symbol(SymbolSpan {
                    vref: VarRef::new("foo", VarType::Auto),
                    pos: lc(1, 2),
                })),
                sep: ArgSep::End,
                sep_pos: lc(1, 5),
            }])
            .exp_instr(Instruction::LoadRef(SymbolKey::from("foo"), ExprType::Integer, lc(1, 2)))
            .exp_nargs(1)
            .exp_symbol("foo", ExprType::Integer)
            .check();
    }

    #[test]
    fn test_one_required_ref_variable_define_undefined_explicit_type() {
        Tester::default()
            .syntax(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax { name: "ref", require_array: false, define_undefined: true },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Symbol(SymbolSpan {
                    vref: VarRef::new("foo", VarType::Text),
                    pos: lc(1, 2),
                })),
                sep: ArgSep::End,
                sep_pos: lc(1, 6),
            }])
            .exp_instr(Instruction::LoadRef(SymbolKey::from("foo"), ExprType::Text, lc(1, 2)))
            .exp_nargs(1)
            .exp_symbol("foo", ExprType::Text)
            .check();
    }

    #[test]
    fn test_multiple_required_ref_variable_define_undefined_repeated_ok() {
        Tester::default()
            .syntax(
                &[
                    SingularArgSyntax::RequiredRef(
                        RequiredRefSyntax {
                            name: "ref1",
                            require_array: false,
                            define_undefined: true,
                        },
                        ArgSepSyntax::Exactly(ArgSep::Long),
                    ),
                    SingularArgSyntax::RequiredRef(
                        RequiredRefSyntax {
                            name: "ref2",
                            require_array: false,
                            define_undefined: true,
                        },
                        ArgSepSyntax::End,
                    ),
                ],
                None,
            )
            .compile_command([
                ArgSpan {
                    expr: Some(Expr::Symbol(SymbolSpan {
                        vref: VarRef::new("foo", VarType::Auto),
                        pos: lc(1, 2),
                    })),
                    sep: ArgSep::Long,
                    sep_pos: lc(1, 5),
                },
                ArgSpan {
                    expr: Some(Expr::Symbol(SymbolSpan {
                        vref: VarRef::new("foo", VarType::Auto),
                        pos: lc(1, 2),
                    })),
                    sep: ArgSep::End,
                    sep_pos: lc(1, 5),
                },
            ])
            .exp_instr(Instruction::LoadRef(SymbolKey::from("foo"), ExprType::Integer, lc(1, 2)))
            .exp_instr(Instruction::LoadRef(SymbolKey::from("foo"), ExprType::Integer, lc(1, 2)))
            .exp_nargs(2)
            .exp_symbol("foo", ExprType::Integer)
            .check();
    }

    #[test]
    fn test_one_required_ref_array_ok() {
        Tester::default()
            .symbol("foo", SymbolPrototype::Array(ExprType::Text, 0))
            .syntax(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax { name: "ref", require_array: true, define_undefined: false },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Symbol(SymbolSpan {
                    vref: VarRef::new("foo", VarType::Auto),
                    pos: lc(1, 2),
                })),
                sep: ArgSep::End,
                sep_pos: lc(1, 5),
            }])
            .exp_instr(Instruction::LoadRef(SymbolKey::from("foo"), ExprType::Text, lc(1, 2)))
            .exp_nargs(1)
            .check();
    }

    #[test]
    fn test_one_required_ref_array_not_defined() {
        Tester::default()
            .syntax(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax { name: "ref", require_array: true, define_undefined: false },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Symbol(SymbolSpan {
                    vref: VarRef::new("foo", VarType::Auto),
                    pos: lc(1, 2),
                })),
                sep: ArgSep::End,
                sep_pos: lc(1, 5),
            }])
            .exp_error(CallError::ArgumentError(lc(1, 2), "Undefined array foo".to_owned()))
            .check();
    }

    #[test]
    fn test_one_required_ref_array_disallow_value() {
        Tester::default()
            .syntax(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax { name: "ref", require_array: true, define_undefined: false },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Integer(IntegerSpan { value: 5, pos: lc(1, 2) })),
                sep: ArgSep::End,
                sep_pos: lc(1, 5),
            }])
            .exp_error(CallError::ArgumentError(
                lc(1, 2),
                "Requires an array reference, not a value".to_owned(),
            ))
            .check();
    }

    #[test]
    fn test_one_required_ref_array_wrong_type() {
        Tester::default()
            .symbol("foo", SymbolPrototype::Variable(ExprType::Text))
            .syntax(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax { name: "ref", require_array: true, define_undefined: false },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Symbol(SymbolSpan {
                    vref: VarRef::new("foo", VarType::Auto),
                    pos: lc(1, 2),
                })),
                sep: ArgSep::End,
                sep_pos: lc(1, 5),
            }])
            .exp_error(CallError::ArgumentError(
                lc(1, 2),
                "foo is not an array reference".to_owned(),
            ))
            .check();
    }

    #[test]
    fn test_one_required_ref_array_wrong_annotation() {
        Tester::default()
            .symbol("foo", SymbolPrototype::Array(ExprType::Text, 0))
            .syntax(
                &[SingularArgSyntax::RequiredRef(
                    RequiredRefSyntax { name: "ref", require_array: true, define_undefined: false },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Symbol(SymbolSpan {
                    vref: VarRef::new("foo", VarType::Integer),
                    pos: lc(1, 2),
                })),
                sep: ArgSep::End,
                sep_pos: lc(1, 5),
            }])
            .exp_error(CallError::ArgumentError(
                lc(1, 2),
                "Incompatible type annotation in foo% reference".to_owned(),
            ))
            .check();
    }

    #[test]
    fn test_one_optional_value_ok_is_present() {
        Tester::default()
            .syntax(
                &[SingularArgSyntax::OptionalValue(
                    OptionalValueSyntax {
                        name: "ref",
                        vtype: ExprType::Double,
                        missing_value: 10,
                        present_value: 20,
                    },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Double(DoubleSpan { value: 3.0, pos: lc(1, 2) })),
                sep: ArgSep::End,
                sep_pos: lc(1, 5),
            }])
            .exp_instr(Instruction::PushDouble(3.0, lc(1, 2)))
            .exp_instr(Instruction::PushInteger(20, lc(1, 2)))
            .exp_nargs(2)
            .check();
    }

    #[test]
    fn test_one_optional_value_ok_is_missing() {
        Tester::default()
            .syntax(
                &[SingularArgSyntax::OptionalValue(
                    OptionalValueSyntax {
                        name: "ref",
                        vtype: ExprType::Double,
                        missing_value: 10,
                        present_value: 20,
                    },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan { expr: None, sep: ArgSep::End, sep_pos: lc(1, 2) }])
            .exp_instr(Instruction::PushInteger(10, lc(1, 2)))
            .exp_nargs(1)
            .check();
    }

    #[test]
    fn test_multiple_any_value_ok() {
        Tester::default()
            .syntax(
                &[
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "arg1", allow_missing: false },
                        ArgSepSyntax::Exactly(ArgSep::Long),
                    ),
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "arg2", allow_missing: false },
                        ArgSepSyntax::Exactly(ArgSep::Long),
                    ),
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "arg3", allow_missing: false },
                        ArgSepSyntax::Exactly(ArgSep::Long),
                    ),
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "arg4", allow_missing: false },
                        ArgSepSyntax::End,
                    ),
                ],
                None,
            )
            .compile_command([
                ArgSpan {
                    expr: Some(Expr::Boolean(BooleanSpan { value: false, pos: lc(1, 2) })),
                    sep: ArgSep::Long,
                    sep_pos: lc(1, 3),
                },
                ArgSpan {
                    expr: Some(Expr::Double(DoubleSpan { value: 2.0, pos: lc(1, 4) })),
                    sep: ArgSep::Long,
                    sep_pos: lc(1, 5),
                },
                ArgSpan {
                    expr: Some(Expr::Integer(IntegerSpan { value: 3, pos: lc(1, 6) })),
                    sep: ArgSep::Long,
                    sep_pos: lc(1, 7),
                },
                ArgSpan {
                    expr: Some(Expr::Text(TextSpan { value: "foo".to_owned(), pos: lc(1, 8) })),
                    sep: ArgSep::End,
                    sep_pos: lc(1, 9),
                },
            ])
            .exp_instr(Instruction::PushString("foo".to_owned(), lc(1, 8)))
            .exp_instr(Instruction::PushInteger(ValueTag::Text as i32, lc(1, 8)))
            .exp_instr(Instruction::PushInteger(3, lc(1, 6)))
            .exp_instr(Instruction::PushInteger(ValueTag::Integer as i32, lc(1, 6)))
            .exp_instr(Instruction::PushDouble(2.0, lc(1, 4)))
            .exp_instr(Instruction::PushInteger(ValueTag::Double as i32, lc(1, 4)))
            .exp_instr(Instruction::PushBoolean(false, lc(1, 2)))
            .exp_instr(Instruction::PushInteger(ValueTag::Boolean as i32, lc(1, 2)))
            .exp_nargs(8)
            .check();
    }

    #[test]
    fn test_one_any_value_expr_error() {
        Tester::default()
            .symbol("foo", SymbolPrototype::Variable(ExprType::Double))
            .syntax(
                &[SingularArgSyntax::AnyValue(
                    AnyValueSyntax { name: "arg1", allow_missing: false },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Symbol(SymbolSpan {
                    vref: VarRef::new("foo", VarType::Boolean),
                    pos: lc(1, 2),
                })),
                sep: ArgSep::End,
                sep_pos: lc(1, 3),
            }])
            .exp_error(CallError::ArgumentError(
                lc(1, 2),
                "Incompatible type annotation in foo? reference".to_owned(),
            ))
            .check();
    }

    #[test]
    fn test_one_any_value_disallow_missing() {
        Tester::default()
            .symbol("foo", SymbolPrototype::Variable(ExprType::Double))
            .syntax(
                &[SingularArgSyntax::AnyValue(
                    AnyValueSyntax { name: "arg1", allow_missing: false },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan { expr: None, sep: ArgSep::End, sep_pos: lc(1, 3) }])
            .exp_error(CallError::ArgumentError(
                lc(1, 3),
                "Missing expression before separator".to_owned(),
            ))
            .check();
    }

    #[test]
    fn test_one_any_value_allow_missing() {
        Tester::default()
            .syntax(
                &[SingularArgSyntax::AnyValue(
                    AnyValueSyntax { name: "arg1", allow_missing: true },
                    ArgSepSyntax::End,
                )],
                None,
            )
            .compile_command([ArgSpan { expr: None, sep: ArgSep::End, sep_pos: lc(1, 3) }])
            .exp_instr(Instruction::PushInteger(ValueTag::Missing as i32, lc(1, 3)))
            .exp_nargs(1)
            .check();
    }

    #[test]
    fn test_multiple_separator_types_ok() {
        Tester::default()
            .syntax(
                &[
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "arg1", allow_missing: true },
                        ArgSepSyntax::Exactly(ArgSep::As),
                    ),
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "arg2", allow_missing: true },
                        ArgSepSyntax::OneOf(ArgSep::Long, ArgSep::Short),
                    ),
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "arg3", allow_missing: true },
                        ArgSepSyntax::OneOf(ArgSep::Long, ArgSep::Short),
                    ),
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "arg4", allow_missing: true },
                        ArgSepSyntax::End,
                    ),
                ],
                None,
            )
            .compile_command([
                ArgSpan { expr: None, sep: ArgSep::As, sep_pos: lc(1, 1) },
                ArgSpan { expr: None, sep: ArgSep::Long, sep_pos: lc(1, 2) },
                ArgSpan { expr: None, sep: ArgSep::Short, sep_pos: lc(1, 3) },
                ArgSpan { expr: None, sep: ArgSep::End, sep_pos: lc(1, 4) },
            ])
            .exp_instr(Instruction::PushInteger(ValueTag::Missing as i32, lc(1, 4)))
            .exp_instr(Instruction::PushInteger(ArgSep::Short as i32, lc(1, 3)))
            .exp_instr(Instruction::PushInteger(ValueTag::Missing as i32, lc(1, 3)))
            .exp_instr(Instruction::PushInteger(ArgSep::Long as i32, lc(1, 2)))
            .exp_instr(Instruction::PushInteger(ValueTag::Missing as i32, lc(1, 2)))
            .exp_instr(Instruction::PushInteger(ValueTag::Missing as i32, lc(1, 1)))
            .exp_nargs(6)
            .check();
    }

    #[test]
    fn test_multiple_separator_exactly_mismatch() {
        Tester::default()
            .syntax(
                &[
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "arg1", allow_missing: true },
                        ArgSepSyntax::Exactly(ArgSep::As),
                    ),
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "arg2", allow_missing: true },
                        ArgSepSyntax::End,
                    ),
                ],
                None,
            )
            .compile_command([
                ArgSpan { expr: None, sep: ArgSep::Short, sep_pos: lc(1, 1) },
                ArgSpan { expr: None, sep: ArgSep::End, sep_pos: lc(1, 4) },
            ])
            .exp_error(CallError::SyntaxError)
            .check();
    }

    #[test]
    fn test_multiple_separator_oneof_mismatch() {
        Tester::default()
            .syntax(
                &[
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "arg1", allow_missing: true },
                        ArgSepSyntax::OneOf(ArgSep::Short, ArgSep::Long),
                    ),
                    SingularArgSyntax::AnyValue(
                        AnyValueSyntax { name: "arg2", allow_missing: true },
                        ArgSepSyntax::End,
                    ),
                ],
                None,
            )
            .compile_command([
                ArgSpan { expr: None, sep: ArgSep::As, sep_pos: lc(1, 1) },
                ArgSpan { expr: None, sep: ArgSep::End, sep_pos: lc(1, 4) },
            ])
            .exp_error(CallError::SyntaxError)
            .check();
    }

    #[test]
    fn test_repeated_none() {
        Tester::default()
            .syntax(
                &[],
                Some(&RepeatedSyntax {
                    name: "arg",
                    type_syn: RepeatedTypeSyntax::TypedValue(ExprType::Integer),
                    sep: ArgSepSyntax::Exactly(ArgSep::Long),
                    allow_missing: false,
                    require_one: false,
                }),
            )
            .compile_command([])
            .exp_nargs(0)
            .check();
    }

    #[test]
    fn test_repeated_multiple_and_cast() {
        Tester::default()
            .syntax(
                &[],
                Some(&RepeatedSyntax {
                    name: "arg",
                    type_syn: RepeatedTypeSyntax::TypedValue(ExprType::Integer),
                    sep: ArgSepSyntax::Exactly(ArgSep::Long),
                    allow_missing: false,
                    require_one: false,
                }),
            )
            .compile_command([
                ArgSpan {
                    expr: Some(Expr::Double(DoubleSpan { value: 3.0, pos: lc(1, 2) })),
                    sep: ArgSep::Long,
                    sep_pos: lc(1, 2),
                },
                ArgSpan {
                    expr: Some(Expr::Integer(IntegerSpan { value: 5, pos: lc(1, 4) })),
                    sep: ArgSep::End,
                    sep_pos: lc(1, 3),
                },
            ])
            .exp_instr(Instruction::PushInteger(5, lc(1, 4)))
            .exp_instr(Instruction::PushDouble(3.0, lc(1, 2)))
            .exp_instr(Instruction::DoubleToInteger)
            .exp_nargs(2)
            .check();
    }

    #[test]
    fn test_repeated_require_one_just_one() {
        Tester::default()
            .syntax(
                &[],
                Some(&RepeatedSyntax {
                    name: "arg",
                    type_syn: RepeatedTypeSyntax::TypedValue(ExprType::Integer),
                    sep: ArgSepSyntax::Exactly(ArgSep::Long),
                    allow_missing: false,
                    require_one: true,
                }),
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Integer(IntegerSpan { value: 5, pos: lc(1, 2) })),
                sep: ArgSep::End,
                sep_pos: lc(1, 2),
            }])
            .exp_instr(Instruction::PushInteger(5, lc(1, 2)))
            .exp_nargs(1)
            .check();
    }

    #[test]
    fn test_repeated_require_one_missing() {
        Tester::default()
            .syntax(
                &[],
                Some(&RepeatedSyntax {
                    name: "arg",
                    type_syn: RepeatedTypeSyntax::TypedValue(ExprType::Integer),
                    sep: ArgSepSyntax::Exactly(ArgSep::Long),
                    allow_missing: false,
                    require_one: true,
                }),
            )
            .compile_command([])
            .exp_error(CallError::SyntaxError)
            .check();
    }

    #[test]
    fn test_repeated_require_one_ref_ok() {
        Tester::default()
            .syntax(
                &[],
                Some(&RepeatedSyntax {
                    name: "arg",
                    type_syn: RepeatedTypeSyntax::VariableRef,
                    sep: ArgSepSyntax::Exactly(ArgSep::Long),
                    allow_missing: false,
                    require_one: true,
                }),
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Symbol(SymbolSpan {
                    vref: VarRef::new("foo", VarType::Text),
                    pos: lc(1, 2),
                })),
                sep: ArgSep::End,
                sep_pos: lc(1, 2),
            }])
            .exp_instr(Instruction::LoadRef(SymbolKey::from("foo"), ExprType::Text, lc(1, 2)))
            .exp_nargs(1)
            .check();
    }

    #[test]
    fn test_repeated_require_one_ref_error() {
        Tester::default()
            .syntax(
                &[],
                Some(&RepeatedSyntax {
                    name: "arg",
                    type_syn: RepeatedTypeSyntax::VariableRef,
                    sep: ArgSepSyntax::Exactly(ArgSep::Long),
                    allow_missing: false,
                    require_one: true,
                }),
            )
            .compile_command([ArgSpan {
                expr: Some(Expr::Integer(IntegerSpan { value: 5, pos: lc(1, 2) })),
                sep: ArgSep::End,
                sep_pos: lc(1, 2),
            }])
            .exp_error(CallError::ArgumentError(
                lc(1, 2),
                "Requires a variable reference, not a value".to_owned(),
            ))
            .check();
    }

    #[test]
    fn test_repeated_oneof_separator() {
        Tester::default()
            .syntax(
                &[],
                Some(&RepeatedSyntax {
                    name: "arg",
                    type_syn: RepeatedTypeSyntax::TypedValue(ExprType::Double),
                    sep: ArgSepSyntax::OneOf(ArgSep::Long, ArgSep::Short),
                    allow_missing: false,
                    require_one: false,
                }),
            )
            .compile_command([
                ArgSpan {
                    expr: Some(Expr::Double(DoubleSpan { value: 3.0, pos: lc(1, 2) })),
                    sep: ArgSep::Short,
                    sep_pos: lc(1, 3),
                },
                ArgSpan {
                    expr: Some(Expr::Double(DoubleSpan { value: 5.0, pos: lc(1, 4) })),
                    sep: ArgSep::Long,
                    sep_pos: lc(1, 5),
                },
                ArgSpan {
                    expr: Some(Expr::Double(DoubleSpan { value: 2.0, pos: lc(1, 6) })),
                    sep: ArgSep::End,
                    sep_pos: lc(1, 7),
                },
            ])
            .exp_instr(Instruction::PushDouble(2.0, lc(1, 6)))
            .exp_instr(Instruction::PushInteger(ArgSep::Long as i32, lc(1, 5)))
            .exp_instr(Instruction::PushDouble(5.0, lc(1, 4)))
            .exp_instr(Instruction::PushInteger(ArgSep::Short as i32, lc(1, 3)))
            .exp_instr(Instruction::PushDouble(3.0, lc(1, 2)))
            .exp_nargs(5)
            .check();
    }

    #[test]
    fn test_repeated_oneof_separator_and_missing_in_last_position() {
        Tester::default()
            .syntax(
                &[],
                Some(&RepeatedSyntax {
                    name: "arg",
                    type_syn: RepeatedTypeSyntax::TypedValue(ExprType::Double),
                    sep: ArgSepSyntax::OneOf(ArgSep::Long, ArgSep::Short),
                    allow_missing: true,
                    require_one: false,
                }),
            )
            .compile_command([
                ArgSpan {
                    expr: Some(Expr::Double(DoubleSpan { value: 3.0, pos: lc(1, 2) })),
                    sep: ArgSep::Short,
                    sep_pos: lc(1, 3),
                },
                ArgSpan { expr: None, sep: ArgSep::End, sep_pos: lc(1, 4) },
            ])
            .exp_instr(Instruction::PushInteger(ValueTag::Missing as i32, lc(1, 4)))
            .exp_instr(Instruction::PushInteger(ArgSep::Short as i32, lc(1, 3)))
            .exp_instr(Instruction::PushDouble(3.0, lc(1, 2)))
            .exp_instr(Instruction::PushInteger(ValueTag::Double as i32, lc(1, 2)))
            .exp_nargs(4)
            .check();
    }

    #[test]
    fn test_repeated_any_value() {
        Tester::default()
            .syntax(
                &[],
                Some(&RepeatedSyntax {
                    name: "arg",
                    type_syn: RepeatedTypeSyntax::AnyValue,
                    sep: ArgSepSyntax::Exactly(ArgSep::Long),
                    allow_missing: true,
                    require_one: false,
                }),
            )
            .compile_command([
                ArgSpan {
                    expr: Some(Expr::Boolean(BooleanSpan { value: false, pos: lc(1, 2) })),
                    sep: ArgSep::Long,
                    sep_pos: lc(1, 3),
                },
                ArgSpan {
                    expr: Some(Expr::Double(DoubleSpan { value: 2.0, pos: lc(1, 4) })),
                    sep: ArgSep::Long,
                    sep_pos: lc(1, 5),
                },
                ArgSpan {
                    expr: Some(Expr::Integer(IntegerSpan { value: 3, pos: lc(1, 6) })),
                    sep: ArgSep::Long,
                    sep_pos: lc(1, 7),
                },
                ArgSpan {
                    expr: Some(Expr::Text(TextSpan { value: "foo".to_owned(), pos: lc(1, 8) })),
                    sep: ArgSep::Long,
                    sep_pos: lc(1, 9),
                },
                ArgSpan { expr: None, sep: ArgSep::End, sep_pos: lc(1, 10) },
            ])
            .exp_instr(Instruction::PushInteger(ValueTag::Missing as i32, lc(1, 10)))
            .exp_instr(Instruction::PushString("foo".to_owned(), lc(1, 8)))
            .exp_instr(Instruction::PushInteger(ValueTag::Text as i32, lc(1, 8)))
            .exp_instr(Instruction::PushInteger(3, lc(1, 6)))
            .exp_instr(Instruction::PushInteger(ValueTag::Integer as i32, lc(1, 6)))
            .exp_instr(Instruction::PushDouble(2.0, lc(1, 4)))
            .exp_instr(Instruction::PushInteger(ValueTag::Double as i32, lc(1, 4)))
            .exp_instr(Instruction::PushBoolean(false, lc(1, 2)))
            .exp_instr(Instruction::PushInteger(ValueTag::Boolean as i32, lc(1, 2)))
            .exp_nargs(9)
            .check();
    }

    #[test]
    fn test_singular_and_repeated() {
        Tester::default()
            .syntax(
                &[SingularArgSyntax::RequiredValue(
                    RequiredValueSyntax { name: "arg", vtype: ExprType::Double },
                    ArgSepSyntax::Exactly(ArgSep::Short),
                )],
                Some(&RepeatedSyntax {
                    name: "rep",
                    type_syn: RepeatedTypeSyntax::TypedValue(ExprType::Integer),
                    sep: ArgSepSyntax::Exactly(ArgSep::Long),
                    allow_missing: false,
                    require_one: false,
                }),
            )
            .compile_command([
                ArgSpan {
                    expr: Some(Expr::Double(DoubleSpan { value: 4.0, pos: lc(1, 2) })),
                    sep: ArgSep::Short,
                    sep_pos: lc(1, 2),
                },
                ArgSpan {
                    expr: Some(Expr::Integer(IntegerSpan { value: 5, pos: lc(1, 5) })),
                    sep: ArgSep::Long,
                    sep_pos: lc(1, 2),
                },
                ArgSpan {
                    expr: Some(Expr::Integer(IntegerSpan { value: 6, pos: lc(1, 7) })),
                    sep: ArgSep::End,
                    sep_pos: lc(1, 2),
                },
            ])
            .exp_nargs(3)
            .exp_instr(Instruction::PushInteger(6, lc(1, 7)))
            .exp_instr(Instruction::PushInteger(5, lc(1, 5)))
            .exp_instr(Instruction::PushDouble(4.0, lc(1, 2)))
            .check();
    }
}
