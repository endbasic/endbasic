// EndBASIC
// Copyright 2021 Julio Merino
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

//! Symbol definitions and symbols table representation.

use crate::ast::ArgSep;
use crate::ast::ExprType;
use crate::bytecode::VarArgTag;
use crate::mem::{Datum, Pointer};
use async_trait::async_trait;
use std::borrow::Cow;
use std::ops::RangeInclusive;
use std::str::Lines;

/// Error types for callable execution.
#[derive(Debug, thiserror::Error)]
pub enum CallError {
    /// Generic error with a static message.
    #[error("{0}")]
    Other(&'static str),
}

/// Result type for callable execution.
pub type CallResult<T> = Result<T, CallError>;

/// Syntax specification for a required scalar parameter.
#[derive(Clone, Debug)]
pub struct RequiredValueSyntax {
    /// The name of the parameter for help purposes.
    pub name: Cow<'static, str>,

    /// The type of the expected parameter.
    pub vtype: ExprType,
}

/// Syntax specification for a required reference parameter.
#[derive(Clone, Debug)]
pub struct RequiredRefSyntax {
    /// The name of the parameter for help purposes.
    pub name: Cow<'static, str>,

    /// If true, require an array reference; if false, a variable reference.
    pub require_array: bool,

    /// If true, allow references to undefined variables because the command will define them when
    /// missing.  Can only be set to true for commands, not functions, and `require_array` must be
    /// false.
    pub define_undefined: bool,
}

/// Syntax specification for an optional scalar parameter.
///
/// Optional parameters are only supported in commands.
#[derive(Clone, Debug)]
pub struct OptionalValueSyntax {
    /// The name of the parameter for help purposes.
    pub name: Cow<'static, str>,

    /// The type of the expected parameter.
    pub vtype: ExprType,

    /// Value to push onto the stack when the parameter is missing.
    pub missing_value: i32,

    /// Value to push onto the stack when the parameter is present, after which the stack contains
    /// the parameter value.
    pub present_value: i32,
}

/// Specifies the type constraints for a repeated parameter.
#[derive(Clone, Debug)]
pub enum RepeatedTypeSyntax {
    /// Allows any value type, including empty arguments.  The values pushed onto the stack have
    /// the same semantics as those pushed by `AnyValueSyntax`.
    AnyValue,

    /// Expects a value of the given type.
    TypedValue(ExprType),

    /// Expects a reference to a variable (not an array) and allows the variables to not be defined.
    VariableRef,
}

/// Syntax specification for a repeated parameter.
///
/// The repeated parameter must appear after all singular positional parameters.
#[derive(Clone, Debug)]
pub struct RepeatedSyntax {
    /// The name of the parameter for help purposes.
    pub name: Cow<'static, str>,

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

        output.push_str(&self.name);
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

        output.push_str(&self.name);
        output.push('N');
        if let RepeatedTypeSyntax::TypedValue(vtype) = self.type_syn {
            output.push(vtype.annotation());
        }

        output.push(']');
    }
}

/// Syntax specification for a parameter that accepts any scalar type.
#[derive(Clone, Debug)]
pub struct AnyValueSyntax {
    /// The name of the parameter for help purposes.
    pub name: Cow<'static, str>,

    /// Whether to allow the parameter to not be present or not.  Can only be true for commands.
    pub allow_missing: bool,
}

/// Specifies the expected argument separator in a callable's syntax.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum ArgSepSyntax {
    /// The argument separator must exactly be the one given.
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

/// Syntax specification for a non-repeated argument.
///
/// Every item in this enum is composed of a struct that provides the details on the parameter and
/// a struct that provides the details on how this parameter is separated from the next.
#[derive(Clone, Debug)]
pub enum SingularArgSyntax {
    /// A required scalar value with the syntax details and the separator that follows.
    RequiredValue(RequiredValueSyntax, ArgSepSyntax),

    /// A required reference with the syntax details and the separator that follows.
    RequiredRef(RequiredRefSyntax, ArgSepSyntax),

    /// An optional scalar value with the syntax details and the separator that follows.
    OptionalValue(OptionalValueSyntax, ArgSepSyntax),

    /// A required scalar value of any type with the syntax details and the separator that follows.
    AnyValue(AnyValueSyntax, ArgSepSyntax),
}

/// Complete syntax specification for a callable's arguments.
///
/// Note that the description of function arguments is more restricted than that of commands.
/// The arguments compiler panics when these preconditions aren't met with the rationale that
/// builtin functions must never be ill-defined.
// TODO(jmmv): It might be nice to try to express these restrictions in the type system, but
// things are already too verbose as they are...
#[derive(Clone, Debug)]
pub(crate) struct CallableSyntax {
    /// Ordered list of singular arguments that appear before repeated arguments.
    singular: Cow<'static, [SingularArgSyntax]>,

    /// Details on the repeated argument allowed after singular arguments, if any.
    repeated: Option<Cow<'static, RepeatedSyntax>>,
}

impl CallableSyntax {
    /// Creates a new callable arguments definition from its parts defined statically in the
    /// code.
    pub(crate) fn new_static(
        singular: &'static [SingularArgSyntax],
        repeated: Option<&'static RepeatedSyntax>,
    ) -> Self {
        Self { singular: Cow::Borrowed(singular), repeated: repeated.map(Cow::Borrowed) }
    }

    /// Creates a new callable arguments definition from its parts defined dynamically at
    /// runtime.
    pub(crate) fn new_dynamic(
        singular: Vec<SingularArgSyntax>,
        repeated: Option<RepeatedSyntax>,
    ) -> Self {
        Self { singular: Cow::Owned(singular), repeated: repeated.map(Cow::Owned) }
    }

    /// Computes the range of the expected number of parameters for this syntax.
    pub(crate) fn expected_nargs(&self) -> RangeInclusive<usize> {
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

    /// Returns true if this syntax represents "no arguments".
    pub(crate) fn is_empty(&self) -> bool {
        self.singular.is_empty() && self.repeated.is_none()
    }

    /// Produces a user-friendly description of this callable syntax.
    pub(crate) fn describe(&self) -> String {
        let mut description = String::new();
        let mut last_singular_sep = None;
        for (i, s) in self.singular.iter().enumerate() {
            let sep = match s {
                SingularArgSyntax::RequiredValue(details, sep) => {
                    description.push_str(&details.name);
                    description.push(details.vtype.annotation());
                    sep
                }

                SingularArgSyntax::RequiredRef(details, sep) => {
                    description.push_str(&details.name);
                    sep
                }

                SingularArgSyntax::OptionalValue(details, sep) => {
                    description.push('[');
                    description.push_str(&details.name);
                    description.push(details.vtype.annotation());
                    description.push(']');
                    sep
                }

                SingularArgSyntax::AnyValue(details, sep) => {
                    if details.allow_missing {
                        description.push('[');
                    }
                    description.push_str(&details.name);
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

        if let Some(syn) = &self.repeated {
            syn.describe(&mut description, last_singular_sep);
        }

        description
    }
}

/// Builder pattern for constructing a callable's metadata.
pub struct CallableMetadataBuilder {
    /// Name of the callable, stored in uppercase.
    name: Cow<'static, str>,

    /// Return type of the callable, or `None` for commands/subroutines.
    return_type: Option<ExprType>,

    /// Category for grouping related callables in help messages.
    category: Option<&'static str>,

    /// Syntax specifications for the callable's arguments.
    syntaxes: Vec<CallableSyntax>,

    /// Description of the callable for documentation purposes.
    description: Option<&'static str>,
}

impl CallableMetadataBuilder {
    /// Constructs a new metadata builder with the minimum information necessary.
    ///
    /// All code except tests must populate the whole builder with details.  This is enforced at
    /// construction time, where we only allow some fields to be missing under the test
    /// configuration.
    pub fn new(name: &'static str) -> Self {
        assert!(name == name.to_ascii_uppercase(), "Callable name must be in uppercase");

        Self {
            name: Cow::Borrowed(name),
            return_type: None,
            syntaxes: vec![],
            category: None,
            description: None,
        }
    }

    /// Constructs a new metadata builder with the minimum information necessary.
    ///
    /// This is the same as `new` but using a dynamically-allocated name, which is necessary for
    /// user-defined symbols.
    pub fn new_dynamic<S: Into<String>>(name: S) -> Self {
        Self {
            name: Cow::Owned(name.into().to_ascii_uppercase()),
            return_type: None,
            syntaxes: vec![],
            category: Some("User defined"),
            description: Some("User defined symbol."),
        }
    }

    /// Sets the return type of the callable.
    pub fn with_return_type(mut self, return_type: ExprType) -> Self {
        self.return_type = Some(return_type);
        self
    }

    /// Sets the syntax specifications for this callable.
    pub fn with_syntax(
        mut self,
        syntaxes: &'static [(&'static [SingularArgSyntax], Option<&'static RepeatedSyntax>)],
    ) -> Self {
        self.syntaxes = syntaxes
            .iter()
            .map(|s| CallableSyntax::new_static(s.0, s.1))
            .collect::<Vec<CallableSyntax>>();
        self
    }

    /// Sets the syntax specifications for this callable.
    pub(crate) fn with_syntaxes<S: Into<Vec<CallableSyntax>>>(mut self, syntaxes: S) -> Self {
        self.syntaxes = syntaxes.into();
        self
    }

    /// Sets the syntax specifications for this callable.
    pub(crate) fn with_dynamic_syntax(
        self,
        syntaxes: Vec<(Vec<SingularArgSyntax>, Option<RepeatedSyntax>)>,
    ) -> Self {
        let syntaxes = syntaxes
            .into_iter()
            .map(|s| CallableSyntax::new_dynamic(s.0, s.1))
            .collect::<Vec<CallableSyntax>>();
        self.with_syntaxes(syntaxes)
    }

    /// Sets the category for this callable.  All callables with the same category name will be
    /// grouped together in help messages.
    pub fn with_category(mut self, category: &'static str) -> Self {
        self.category = Some(category);
        self
    }

    /// Sets the description for this callable.  The `description` is a collection of paragraphs
    /// separated by a single newline character, where the first paragraph is taken as the summary
    /// of the description.  The summary must be a short sentence that is descriptive enough to be
    /// understood without further details.  Empty lines (paragraphs) are not allowed.
    pub fn with_description(mut self, description: &'static str) -> Self {
        for l in description.lines() {
            assert!(!l.is_empty(), "Description cannot contain empty lines");
        }
        self.description = Some(description);
        self
    }

    /// Generates the final `CallableMetadata` object, ensuring all values are present.
    pub fn build(self) -> CallableMetadata {
        assert!(!self.syntaxes.is_empty(), "All callables must specify a syntax");
        CallableMetadata {
            name: self.name,
            return_type: self.return_type,
            syntaxes: self.syntaxes,
            category: self.category.expect("All callables must specify a category"),
            description: self.description.expect("All callables must specify a description"),
        }
    }

    /// Generates the final `CallableMetadata` object, ensuring the minimal set of values are
    /// present.  Only useful for testing.
    pub fn test_build(mut self) -> CallableMetadata {
        if self.syntaxes.is_empty() {
            self.syntaxes.push(CallableSyntax::new_static(&[], None));
        }
        CallableMetadata {
            name: self.name,
            return_type: self.return_type,
            syntaxes: self.syntaxes,
            category: self.category.unwrap_or(""),
            description: self.description.unwrap_or(""),
        }
    }
}

/// Representation of a callable's metadata.
///
/// The callable is expected to hold onto an instance of this object within its struct to make
/// queries fast.
#[derive(Clone, Debug)]
pub struct CallableMetadata {
    /// Name of the callable, stored in uppercase.
    name: Cow<'static, str>,

    /// Return type of the callable, or `None` for commands/subroutines.
    return_type: Option<ExprType>,

    /// Syntax specifications for the callable's arguments.
    syntaxes: Vec<CallableSyntax>,

    /// Category for grouping related callables in help messages.
    category: &'static str,

    /// Description of the callable for documentation purposes.
    description: &'static str,
}

impl CallableMetadata {
    /// Gets the callable's name, all in uppercase.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Gets the callable's return type.
    pub(crate) fn return_type(&self) -> Option<ExprType> {
        self.return_type
    }

    /// Gets the callable's syntax specification.
    pub(crate) fn syntax(&self) -> String {
        fn format_one(cs: &CallableSyntax) -> String {
            let mut syntax = cs.describe();
            if syntax.is_empty() {
                syntax.push_str("no arguments");
            }
            syntax
        }

        match self.syntaxes.as_slice() {
            [] => panic!("Callables without syntaxes are not allowed at construction time"),
            [one] => format_one(one),
            many => many
                .iter()
                .map(|syn| format!("<{}>", syn.describe()))
                .collect::<Vec<String>>()
                .join(" | "),
        }
    }

    /// Returns the callable's syntax definitions.
    pub(crate) fn syntaxes(&self) -> &[CallableSyntax] {
        &self.syntaxes
    }

    /// Gets the callable's category as a collection of lines.  The first line is the title of the
    /// category, and any extra lines are additional information for it.
    #[allow(unused)]
    pub(crate) fn category(&self) -> &'static str {
        self.category
    }

    /// Gets the callable's textual description as a collection of lines.  The first line is the
    /// summary of the callable's purpose.
    #[allow(unused)]
    pub(crate) fn description(&self) -> Lines<'static> {
        self.description.lines()
    }

    /// Returns true if this is a callable that takes no arguments.
    #[allow(unused)]
    pub(crate) fn is_argless(&self) -> bool {
        self.syntaxes.is_empty() || (self.syntaxes.len() == 1 && self.syntaxes[0].is_empty())
    }

    /// Returns true if this callable is a function (not a command).
    #[allow(unused)]
    pub(crate) fn is_function(&self) -> bool {
        self.return_type.is_some()
    }

    /// Returns true if this callable is user-defined.
    pub(crate) fn is_user_defined(&self) -> bool {
        self.category == "User defined"
    }
}

/// Arguments provided to a callable during its execution.
pub struct Scope<'a> {
    /// Slice of register values containing the callable's arguments.
    pub(crate) regs: &'a [u64],

    /// Reference to the constants pool for resolving constant pointers.
    pub(crate) constants: &'a [Datum],

    /// Reference to the heap for resolving heap pointers.
    pub(crate) heap: &'a [Datum],
}

impl<'a> Scope<'a> {
    /// Gets the type tag of the argument at `arg`.
    pub fn get_type(&self, arg: u8) -> VarArgTag {
        VarArgTag::parse_u64(self.regs[arg as usize]).unwrap()
    }

    /// Gets the boolean value of the argument at `arg`.
    pub fn get_boolean(&self, arg: u8) -> bool {
        self.regs[arg as usize] != 0
    }

    /// Gets the double value of the argument at `arg`.
    pub fn get_double(&self, arg: u8) -> f64 {
        f64::from_bits(self.regs[arg as usize])
    }

    /// Gets the integer value of the argument at `arg`.
    pub fn get_integer(&self, arg: u8) -> i32 {
        self.regs[arg as usize] as i32
    }

    /// Gets the string value of the argument at `arg`.
    pub fn get_string(&self, arg: u8) -> &str {
        let index = self.regs[arg as usize];
        let ptr = Pointer::from(index);
        match ptr.resolve(self.constants, self.heap) {
            Datum::Text(s) => s,
            _ => panic!("Mismatched constant type"),
        }
    }
}

/// A trait to define a callable that is executed by a `Machine`.
///
/// The callable themselves are immutable but they can reference mutable state.  Given that
/// EndBASIC is not threaded, it is sufficient for those references to be behind a `RefCell`
/// and/or an `Rc`.
///
/// Idiomatically, these objects need to provide a `new()` method that returns an `Rc<Callable>`, as
/// that's the type used throughout the execution engine.
#[async_trait(?Send)]
pub trait Callable {
    /// Returns the metadata for this function.
    ///
    /// The return value takes the form of a reference to force the callable to store the metadata
    /// as a struct field so that calls to this function are guaranteed to be cheap.
    fn metadata(&self) -> &CallableMetadata;

    /// Executes the function.
    ///
    /// `args` contains the arguments to the function call.
    ///
    /// `machine` provides mutable access to the current state of the machine invoking the function.
    async fn exec(&self, scope: Scope<'_>) -> CallResult<()>;
}
