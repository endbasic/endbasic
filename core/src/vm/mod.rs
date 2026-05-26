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

//! Virtual machine for EndBASIC execution.

#[cfg(test)]
use crate::CallError;
use crate::UpcallError;
use crate::bytecode::{ExitCode, Register};
use crate::callable::{Callable, Scope};
use crate::compiler::SymbolKey;
use crate::image::{GlobalVarInfo, Image};
use crate::mem::{ConstantDatum, DatumPtr, Heap, HeapDatum};
use crate::num::U24;
use crate::reader::LineCol;
use std::collections::HashMap;
use std::rc::Rc;

mod context;
use context::{Context, ErrorHandler, InternalStopReason};

/// Default maximum number of call stack frames.
const DEFAULT_MAX_CALL_STACK: usize = 4096;

/// Limits for VM execution resources.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Limits {
    /// Maximum number of frames the call stack can contain.
    pub max_call_stack: usize,

    /// Maximum number of entries the heap can contain.
    pub max_heap_entries: U24,
}

impl Default for Limits {
    fn default() -> Self {
        Self { max_call_stack: DEFAULT_MAX_CALL_STACK, max_heap_entries: U24::MAX }
    }
}

/// Error returned when a global variable access encounters a type or shape mismatch.
///
/// This is distinct from a missing variable, which is represented by `None` in the
/// return value of `get_global` and `get_global_array`.
#[derive(Debug, thiserror::Error)]
pub enum GetGlobalError {
    /// The variable exists but is an array; use `get_global_array` instead.
    #[error("'{0}' is an array variable; use get_global_array to access it")]
    IsArray(String),

    /// The variable exists but is a scalar; use `get_global` instead.
    #[error("'{0}' is a scalar variable; use get_global to access it")]
    IsScalar(String),

    /// The array subscripts are out of bounds or invalid.
    #[error("{0}")]
    SubscriptOutOfBounds(String),
}

/// Result type for global variable access operations.
pub type GetGlobalResult<T> = Result<T, GetGlobalError>;

/// Opaque handle to invoke a pending upcall.
pub struct UpcallHandler<'a> {
    vm: &'a mut Vm,
    image: &'a Image,
}

impl<'a> UpcallHandler<'a> {
    /// Invokes the pending upcall.
    pub async fn invoke(self) -> Result<(), UpcallError> {
        let vm = self.vm;
        let image = self.image;
        let (index, first_reg, upcall_pc) = vm
            .pending_upcall
            .take()
            .expect("This is only reachable when the VM has a pending upcall");
        let (upcall, scope) = vm.prepare_upcall(image, index, first_reg, upcall_pc);
        let result = upcall.async_exec(scope).await;
        match vm.handle_upcall_result(image, upcall_pc, result) {
            Ok(()) => Ok(()),
            Err(e) => {
                vm.park_at_eof(image);
                Err(e)
            }
        }
    }
}

/// Representation of termination states from program execution.
pub enum StopReason<'a> {
    /// Execution terminated due to an `END` instruction.
    End(ExitCode),

    /// Execution terminated due to natural fallthrough.
    Eof,

    /// Execution stopped due to an instruction-level exception.
    Exception(LineCol, String),

    /// Execution stopped due to an asynchronous upcall that requires service from the caller.
    UpcallAsync(UpcallHandler<'a>),

    /// Execution stopped to yield control back to the caller.
    Yield,
}

/// Virtual machine for EndBASIC program execution.
pub struct Vm {
    /// Mapping of all available upcall names to their handlers.
    upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>>,

    /// Upcall names already resolved into `upcalls`.
    upcall_names: Vec<SymbolKey>,

    /// Upcalls used by the current image in index order.
    upcalls: Vec<Rc<dyn Callable>>,

    /// Heap memory for dynamic allocations.
    heap: Heap,

    /// Processor context for execution.
    context: Context,

    /// Last error seen by the VM, if any.
    last_error: Option<(LineCol, String)>,

    /// Details about the pending upcall that has to be handled by the caller.
    ///
    /// The tuple contains the upcall index, the first argument register, and the PC of the
    /// upcall instruction (for arg position lookup in `DebugInfo`).
    pending_upcall: Option<(u16, Register, usize)>,
}

impl Vm {
    /// Resolves upcall metadata and builds an execution scope for invocation.
    fn prepare_upcall<'a>(
        &'a mut self,
        image: &'a Image,
        index: u16,
        first_reg: Register,
        upcall_pc: usize,
    ) -> (Rc<dyn Callable>, Scope<'a>) {
        let upcall = self.upcalls[usize::from(index)].clone();
        let is_function = upcall.metadata().return_type().is_some();
        let scope = self.upcall_scope(image, first_reg, is_function, upcall_pc);
        (upcall, scope)
    }

    /// Handles the result of an upcall invocation.
    ///
    /// Returns `Ok(())` if invocation succeeded or if an exception handler consumed the
    /// failure.  Returns `Err` only if execution must stop with an uncaught exception.
    fn handle_upcall_result(
        &mut self,
        image: &Image,
        upcall_pc: usize,
        result: crate::callable::CallResult<()>,
    ) -> Result<(), UpcallError> {
        match result {
            Ok(()) => Ok(()),
            Err(e) => {
                let default_pos = image.debug_info.instrs[upcall_pc].linecol;
                let upcall_error = e.to_upcall_error(default_pos);
                let (pos, message) = upcall_error.parts();
                if self.handle_exception(image, upcall_pc, pos, message) {
                    Ok(())
                } else {
                    Err(upcall_error)
                }
            }
        }
    }

    /// Returns the scalar value named `key` from `vars`, decoding values from `read_raw`.
    fn get_scalar_var(
        &self,
        image: &Image,
        key: &SymbolKey,
        vars: &HashMap<SymbolKey, GlobalVarInfo>,
        read_raw: fn(&Context, u8) -> u64,
    ) -> GetGlobalResult<Option<ConstantDatum>> {
        let Some(info) = vars.get(key) else {
            return Ok(None);
        };
        if info.ndims != 0 {
            return Err(GetGlobalError::IsArray(key.to_string()));
        }
        let raw = read_raw(&self.context, info.reg);
        Ok(Some(ConstantDatum::from_raw(raw, info.subtype, &image.constants, &self.heap)))
    }

    /// Returns the array element named `key` from `vars`, decoding values from `read_raw`.
    fn get_array_var(
        &self,
        image: &Image,
        key: &SymbolKey,
        vars: &HashMap<SymbolKey, GlobalVarInfo>,
        subscripts: &[i32],
        read_raw: fn(&Context, u8) -> u64,
    ) -> GetGlobalResult<Option<ConstantDatum>> {
        let Some(info) = vars.get(key) else {
            return Ok(None);
        };
        if info.ndims == 0 {
            return Err(GetGlobalError::IsScalar(key.to_string()));
        }
        let raw = read_raw(&self.context, info.reg);
        let ptr = DatumPtr::from(raw);
        let heap_idx = ptr.heap_index();
        let HeapDatum::Array(a) = self.heap.get(heap_idx) else {
            panic!("Array variable does not point to an array on the heap");
        };
        let flat_idx = a.flat_index(subscripts).map_err(GetGlobalError::SubscriptOutOfBounds)?;
        let v = a.values[flat_idx];
        Ok(Some(ConstantDatum::from_raw(v, info.subtype, &image.constants, &self.heap)))
    }

    /// Creates a new VM with the given `upcalls_by_name` as the available built-in callables.
    pub fn new(upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>>) -> Self {
        Self::new_with_limits(upcalls_by_name, Limits::default())
    }

    /// Creates a new VM with the given `upcalls_by_name` and resource `limits`.
    pub fn new_with_limits(
        upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>>,
        limits: Limits,
    ) -> Self {
        Self {
            upcalls_by_name,
            upcall_names: vec![],
            upcalls: vec![],
            heap: Heap::new(limits.max_heap_entries),
            context: Context::new(limits.max_call_stack),
            last_error: None,
            pending_upcall: None,
        }
    }

    /// Resets any existing execution state, including upcall caches and the program counter.
    pub fn reset(&mut self) {
        self.upcall_names.clear();
        self.upcalls.clear();
        self.heap.clear();
        self.context.clear_runtime_state();
        self.last_error = None;
        self.pending_upcall = None;
    }

    /// Resets runtime state (registers, heap, last error, call stack, program counter) but preserves
    /// upcall caches so the same image can continue to be executed.
    ///
    /// Note: because the program counter is also reset, callers need to either re-set it to a
    /// specific location or replace the image with one that resumes from the start.
    pub fn clear(&mut self) {
        self.heap.clear();
        self.context.clear_runtime_state();
        self.last_error = None;
        self.pending_upcall = None;
    }

    /// Clears the current error handler without affecting execution state or captured errors.
    pub fn clear_error_handler(&mut self) {
        self.context.clear_error_handler();
    }

    /// Synchronizes cached upcall handlers with the externally-owned `image`.
    fn sync_upcalls(&mut self, image: &Image) {
        debug_assert!(
            image.upcalls.starts_with(self.upcall_names.as_slice()),
            "Vm::reset() is required before executing a different image",
        );

        for key in &image.upcalls[self.upcalls.len()..] {
            self.upcalls.push(
                self.upcalls_by_name
                    .get(key)
                    .expect("All upcalls exposed during compilation must be present at runtime")
                    .clone(),
            );
            self.upcall_names.push(key.clone());
        }
    }

    /// Parks execution at the current EOF instruction so later appended code can resume.
    fn park_at_eof(&mut self, image: &Image) {
        debug_assert!(!image.code.is_empty());
        self.context.set_pc(image.code.len() - 1);
    }

    /// Constructs a `Scope` for an upcall with arguments starting at `reg`.
    ///
    /// `upcall_pc` is the address of the UPCALL instruction in the image, used to look up
    /// per-argument source locations from `DebugInfo`.  `is_function` indicates whether the
    /// upcall is a function (with a return value slot) so that `Scope::arg_offset` can be set
    /// appropriately.
    fn upcall_scope<'a>(
        &'a mut self,
        image: &'a Image,
        reg: Register,
        is_function: bool,
        upcall_pc: usize,
    ) -> Scope<'a> {
        let arg_linecols = image
            .debug_info
            .instrs
            .get(upcall_pc)
            .map(|m| m.arg_linecols.as_slice())
            .unwrap_or(&[]);
        self.context.upcall_scope(
            reg,
            is_function,
            image.constants.as_slice(),
            &mut self.heap,
            arg_linecols,
            &self.last_error,
            image.data.as_slice(),
        )
    }

    /// Handles an exception raised at `pc`, corresponding to `pos`, with `message`.  Returns true if the error was handled.
    fn handle_exception(
        &mut self,
        image: &Image,
        pc: usize,
        pos: LineCol,
        message: String,
    ) -> bool {
        self.last_error = Some((pos, message));

        match self.context.error_handler() {
            ErrorHandler::None => false,
            ErrorHandler::Jump { active: true, .. } => false,
            ErrorHandler::Jump { active: false, addr } => {
                self.context.set_error_handler_active();
                self.context.set_pc(addr);
                true
            }
            ErrorHandler::ResumeNext => {
                let mut next_pc = image.code.len();
                for (idx, meta) in image.debug_info.instrs.iter().enumerate().skip(pc + 1) {
                    if meta.is_stmt_start {
                        next_pc = idx;
                        break;
                    }
                }
                self.context.set_pc(next_pc);
                true
            }
        }
    }

    /// Returns the value of the global scalar variable `key` as a `ConstantDatum`.
    ///
    /// Returns `Ok(None)` if the variable is not defined (no image is loaded or the
    /// variable was not declared).  Returns `Err` if the variable exists but is an
    /// array; in that case, use `get_global_array` instead.
    pub fn get_global(
        &self,
        image: &Image,
        key: &SymbolKey,
    ) -> GetGlobalResult<Option<ConstantDatum>> {
        self.get_scalar_var(image, key, &image.debug_info.global_vars, Context::get_global_reg_raw)
    }

    /// Returns the value of an element in the global array variable `key` at the given
    /// `subscripts` as a `ConstantDatum`.
    ///
    /// Returns `Ok(None)` if the variable is not defined (no image is loaded or the
    /// variable was not declared).  Returns `Err` if the variable exists but is a scalar
    /// (use `get_global` instead), or if the subscripts are out of bounds.
    pub fn get_global_array(
        &self,
        image: &Image,
        key: &SymbolKey,
        subscripts: &[i32],
    ) -> GetGlobalResult<Option<ConstantDatum>> {
        self.get_array_var(
            image,
            key,
            &image.debug_info.global_vars,
            subscripts,
            Context::get_global_reg_raw,
        )
    }

    /// Returns the value of the program-scope scalar variable `key` as a `ConstantDatum`.
    ///
    /// Returns `Ok(None)` if the variable is not defined (no image is loaded or the
    /// variable was not declared).  Returns `Err` if the variable exists but is an
    /// array; in that case, use `get_program_array` instead.
    pub fn get_program(
        &self,
        image: &Image,
        key: &SymbolKey,
    ) -> GetGlobalResult<Option<ConstantDatum>> {
        self.get_scalar_var(
            image,
            key,
            &image.debug_info.program_vars,
            Context::get_program_reg_raw,
        )
    }

    /// Returns the value of an element in the program-scope array variable `key` at the
    /// given `subscripts` as a `ConstantDatum`.
    ///
    /// Returns `Ok(None)` if the variable is not defined (no image is loaded or the
    /// variable was not declared).  Returns `Err` if the variable exists but is a scalar
    /// (use `get_program` instead), or if the subscripts are out of bounds.
    pub fn get_program_array(
        &self,
        image: &Image,
        key: &SymbolKey,
        subscripts: &[i32],
    ) -> GetGlobalResult<Option<ConstantDatum>> {
        self.get_array_var(
            image,
            key,
            &image.debug_info.program_vars,
            subscripts,
            Context::get_program_reg_raw,
        )
    }

    /// Starts or resumes execution of `image`.
    ///
    /// Returns a `StopReason` indicating why execution stopped, which may be due to program
    /// termination, an exception, or a pending upcall that requires caller handling.
    pub fn exec<'a>(&'a mut self, image: &'a Image) -> StopReason<'a> {
        self.sync_upcalls(image);

        loop {
            if self.pending_upcall.is_some() {
                return StopReason::UpcallAsync(UpcallHandler { vm: self, image });
            }

            match self.context.exec(image, &mut self.heap) {
                InternalStopReason::End(code) => {
                    self.park_at_eof(image);
                    return StopReason::End(code);
                }
                InternalStopReason::Eof => return StopReason::Eof,
                InternalStopReason::Exception(pc, e) => {
                    let pos = image.debug_info.instrs[pc].linecol;
                    if !self.handle_exception(image, pc, pos, e.clone()) {
                        self.park_at_eof(image);
                        return StopReason::Exception(pos, e);
                    }
                }
                InternalStopReason::Upcall(index, first_reg, upcall_pc) => {
                    let (upcall, scope) = self.prepare_upcall(image, index, first_reg, upcall_pc);
                    let result = upcall.exec(scope);
                    if let Err(upcall_error) = self.handle_upcall_result(image, upcall_pc, result) {
                        let (pos, message) = upcall_error.parts();
                        self.park_at_eof(image);
                        return StopReason::Exception(pos, message);
                    }
                }

                InternalStopReason::UpcallAsync(index, first_reg, upcall_pc) => {
                    self.pending_upcall = Some((index, first_reg, upcall_pc));
                    return StopReason::UpcallAsync(UpcallHandler { vm: self, image });
                }

                InternalStopReason::Yield => return StopReason::Yield,
            }
        }
    }

    /// Stops execution of `image` so that the next call to `exec` starts at EOF.
    ///
    /// This is useful when external events interrupt execution and the caller wants
    /// to avoid resuming a partially-run image by mistake.
    pub fn interrupt(&mut self, image: &Image) {
        self.pending_upcall = None;
        self.park_at_eof(image);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Compiler;
    use crate::ast::{ArgSep, ExprType};
    use crate::callable::{
        ArgSepSyntax, CallResult, CallableMetadata, CallableMetadataBuilder, RequiredValueSyntax,
        SingularArgSyntax,
    };
    use crate::compiler::SymbolKey;
    use crate::image::Image;
    use crate::reader::LineCol;
    use crate::testutils::OutCommand;
    use async_trait::async_trait;
    use futures_lite::future::yield_now;
    use std::borrow::Cow;
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::io;
    use std::rc::Rc;

    /// A test callable that captures the source positions of argument register slots.
    ///
    /// On each invocation, records the result of `scope.get_pos(n)` for `0..nargs` into
    /// `positions`.
    struct PosCapture {
        metadata: Rc<CallableMetadata>,
        nargs: u8,
        positions: Rc<RefCell<Vec<LineCol>>>,
    }

    impl PosCapture {
        /// Creates a new `PosCapture` callable named `POS_CAPTURE` that expects
        /// `nargs` required integer arguments separated by commas.
        fn new(nargs: u8, positions: Rc<RefCell<Vec<LineCol>>>) -> Rc<Self> {
            let singular: Vec<SingularArgSyntax> = (0..nargs)
                .map(|i| {
                    let sep = if i == nargs - 1 {
                        ArgSepSyntax::End
                    } else {
                        ArgSepSyntax::Exactly(ArgSep::Long)
                    };
                    SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax {
                            name: Cow::Borrowed("arg"),
                            vtype: ExprType::Integer,
                        },
                        sep,
                    )
                })
                .collect();
            let md = CallableMetadataBuilder::new("POS_CAPTURE")
                .with_dynamic_syntax(vec![(singular, None)])
                .test_build();
            Rc::from(Self { metadata: md, nargs, positions })
        }
    }

    impl Callable for PosCapture {
        fn metadata(&self) -> Rc<CallableMetadata> {
            self.metadata.clone()
        }

        fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
            let mut positions = self.positions.borrow_mut();
            for i in 0..self.nargs {
                positions.push(scope.get_pos(i));
            }
            Ok(())
        }
    }

    struct ReturnFortyTwoFunction {
        metadata: Rc<CallableMetadata>,
    }

    impl ReturnFortyTwoFunction {
        fn new() -> Rc<Self> {
            let md = CallableMetadataBuilder::new("RET42")
                .with_return_type(ExprType::Integer)
                .with_syntax(&[(&[], None)])
                .test_build();
            Rc::from(Self { metadata: md })
        }
    }

    impl Callable for ReturnFortyTwoFunction {
        fn metadata(&self) -> Rc<CallableMetadata> {
            self.metadata.clone()
        }

        fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
            scope.return_integer(42)
        }
    }

    struct IoErrorCommand {
        metadata: Rc<CallableMetadata>,
    }

    impl IoErrorCommand {
        fn new() -> Rc<Self> {
            let md = CallableMetadataBuilder::new("IOFAIL")
                .with_dynamic_syntax(vec![(vec![], None)])
                .test_build();
            Rc::from(Self { metadata: md })
        }
    }

    struct AsyncIncrementFunction {
        metadata: Rc<CallableMetadata>,
    }

    impl AsyncIncrementFunction {
        fn new() -> Rc<Self> {
            let md = CallableMetadataBuilder::new("ASYNC_INCREMENT")
                .with_return_type(ExprType::Integer)
                .with_async(true)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax {
                            name: Cow::Borrowed("value"),
                            vtype: ExprType::Integer,
                        },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .test_build();
            Rc::from(Self { metadata: md })
        }
    }

    #[async_trait(?Send)]
    impl Callable for AsyncIncrementFunction {
        fn metadata(&self) -> Rc<CallableMetadata> {
            self.metadata.clone()
        }

        async fn async_exec(&self, scope: Scope<'_>) -> CallResult<()> {
            let value = scope.get_integer(0) + 1;
            yield_now().await;
            scope.return_integer(value)
        }
    }

    struct AsyncIoErrorCommand {
        metadata: Rc<CallableMetadata>,
    }

    impl AsyncIoErrorCommand {
        fn new() -> Rc<Self> {
            let md = CallableMetadataBuilder::new("ASYNC_IOFAIL")
                .with_async(true)
                .with_dynamic_syntax(vec![(vec![], None)])
                .test_build();
            Rc::from(Self { metadata: md })
        }
    }

    #[async_trait(?Send)]
    impl Callable for AsyncIoErrorCommand {
        fn metadata(&self) -> Rc<CallableMetadata> {
            self.metadata.clone()
        }

        async fn async_exec(&self, _scope: Scope<'_>) -> CallResult<()> {
            yield_now().await;
            Err(CallError::from(io::Error::other("mock async I/O error")))
        }
    }

    #[async_trait(?Send)]
    impl Callable for IoErrorCommand {
        fn metadata(&self) -> Rc<CallableMetadata> {
            self.metadata.clone()
        }

        fn exec(&self, _scope: Scope<'_>) -> CallResult<()> {
            Err(CallError::from(io::Error::other("mock I/O error")))
        }
    }

    /// Runs the VM to completion, invoking every upcall as it is encountered.
    async fn run_to_end(vm: &mut Vm, image: &Image) {
        loop {
            match vm.exec(image) {
                StopReason::End(_) => break,
                StopReason::Eof => break,
                StopReason::Exception(_, msg) => panic!("Unexpected exception: {}", msg),
                StopReason::UpcallAsync(handler) => handler.invoke().await.unwrap(),
                StopReason::Yield => (),
            }
        }
    }

    #[test]
    fn test_exec_without_load_is_eof() {
        let mut vm = Vm::new(HashMap::default());
        let image = Image::default();
        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Unexpected stop reason"),
        }
    }

    #[test]
    fn test_exec_empty_image_is_eof() {
        let mut vm = Vm::new(HashMap::default());
        let image = Image::default();
        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Unexpected stop reason"),
        }
    }

    #[test]
    fn test_exec_empty_compilation_is_eof() {
        let mut vm = Vm::new(HashMap::default());
        let compiler = Compiler::new(&HashMap::default(), &[]).unwrap();
        let image = compiler.compile(&mut b"".as_slice()).unwrap();
        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Unexpected stop reason"),
        }
    }

    #[tokio::test]
    async fn test_exec_upcall_flow() {
        let data = Rc::from(RefCell::from(vec![]));
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("OUT"), OutCommand::new(data.clone()));

        let compiler = Compiler::new(&upcalls_by_name, &[]).unwrap();
        let image = compiler.compile(&mut b"OUT 30: OUT 20".as_slice()).unwrap();

        let mut vm = Vm::new(upcalls_by_name);

        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should stop at EOF"),
        }
        assert_eq!(["30", "20"], *data.borrow().as_slice());
    }

    #[tokio::test]
    async fn test_exec_async_upcall_flow() {
        let data = Rc::from(RefCell::from(vec![]));
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("ASYNC_INCREMENT"), AsyncIncrementFunction::new());
        upcalls_by_name.insert(SymbolKey::from("OUT"), OutCommand::new(data.clone()));

        let compiler = Compiler::new(&upcalls_by_name, &[]).unwrap();
        let image = compiler.compile(&mut b"OUT ASYNC_INCREMENT(123): OUT 5".as_slice()).unwrap();
        let mut vm = Vm::new(upcalls_by_name);

        match vm.exec(&image) {
            StopReason::UpcallAsync(handler) => handler.invoke().await.unwrap(),
            _ => panic!("Execution should stop at ASYNC_INCREMENT upcall"),
        }

        assert!(data.borrow().is_empty());

        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should stop at EOF"),
        }

        assert_eq!(["124", "5"], *data.borrow().as_slice());
    }

    #[tokio::test]
    async fn test_exec_async_upcall_error_can_resume_after_append() {
        let data = Rc::from(RefCell::from(vec![]));
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("ASYNC_IOFAIL"), AsyncIoErrorCommand::new());
        upcalls_by_name.insert(SymbolKey::from("OUT"), OutCommand::new(data.clone()));

        let mut compiler = Compiler::new(&upcalls_by_name, &[]).unwrap();
        let mut image = Image::default();
        compiler.compile_more(&mut image, &mut b"ASYNC_IOFAIL".as_slice()).unwrap();

        let mut vm = Vm::new(upcalls_by_name);
        match vm.exec(&image) {
            StopReason::UpcallAsync(handler) => {
                let error = handler.invoke().await.unwrap_err();
                let (pos, message) = error.parts();
                assert_eq!(LineCol { line: 1, col: 1 }, pos);
                assert_eq!("mock async I/O error", message);
            }
            _ => panic!("Execution should stop at ASYNC_IOFAIL upcall"),
        }

        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should park at EOF after an ASYNC_IOFAIL exception"),
        }

        compiler.compile_more(&mut image, &mut b"OUT 2".as_slice()).unwrap();
        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should resume at newly appended code"),
        }
        assert_eq!(["2"], *data.borrow().as_slice());

        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should stop at EOF after appended code"),
        }
    }

    #[tokio::test]
    async fn test_interrupt_cancels_pending_async_upcall() {
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("ASYNC_INCREMENT"), AsyncIncrementFunction::new());

        let compiler = Compiler::new(&upcalls_by_name, &[]).unwrap();
        let image = compiler.compile(&mut b"x = ASYNC_INCREMENT(123)".as_slice()).unwrap();
        let mut vm = Vm::new(upcalls_by_name);

        match vm.exec(&image) {
            StopReason::UpcallAsync(_) => (),
            _ => panic!("Execution should stop at ASYNC_INCREMENT upcall"),
        }

        vm.interrupt(&image);
        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should stop at EOF after interrupting a pending upcall"),
        }
    }

    #[tokio::test]
    async fn test_interrupt_after_pending_async_upcall_can_resume_after_append() {
        let data = Rc::from(RefCell::from(vec![]));
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("ASYNC_INCREMENT"), AsyncIncrementFunction::new());
        upcalls_by_name.insert(SymbolKey::from("OUT"), OutCommand::new(data.clone()));

        let mut compiler = Compiler::new(&upcalls_by_name, &[]).unwrap();
        let mut image = Image::default();
        compiler.compile_more(&mut image, &mut b"x = ASYNC_INCREMENT(123)".as_slice()).unwrap();

        let mut vm = Vm::new(upcalls_by_name);
        match vm.exec(&image) {
            StopReason::UpcallAsync(_) => (),
            _ => panic!("Execution should stop at ASYNC_INCREMENT upcall"),
        }

        vm.interrupt(&image);
        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should stop at EOF after interrupting a pending upcall"),
        }

        compiler.compile_more(&mut image, &mut b"OUT 2".as_slice()).unwrap();
        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should resume at newly appended code"),
        }
        assert_eq!(["2"], *data.borrow().as_slice());

        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should stop at EOF after appended code"),
        }
    }

    #[tokio::test]
    async fn test_exec_end_code_default() {
        let mut vm = Vm::new(HashMap::default());
        let compiler = Compiler::new(&HashMap::default(), &[]).unwrap();
        let image = compiler.compile(&mut b"END".as_slice()).unwrap();
        match vm.exec(&image) {
            StopReason::End(code) if code.is_success() => (),
            _ => panic!("Unexpected stop reason"),
        }
    }

    #[tokio::test]
    async fn test_exec_end_code_explicit() {
        let mut vm = Vm::new(HashMap::default());
        let compiler = Compiler::new(&HashMap::default(), &[]).unwrap();
        let image = compiler.compile(&mut b"END 3".as_slice()).unwrap();
        match vm.exec(&image) {
            StopReason::End(code) if code.to_i32() == 3 => (),
            _ => panic!("Unexpected stop reason"),
        }
    }

    #[tokio::test]
    async fn test_exec_end_can_resume_after_append() {
        let data = Rc::from(RefCell::from(vec![]));
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("OUT"), OutCommand::new(data.clone()));

        let mut compiler = Compiler::new(&upcalls_by_name, &[]).unwrap();
        let mut image = Image::default();
        compiler.compile_more(&mut image, &mut b"END 3".as_slice()).unwrap();

        let mut vm = Vm::new(upcalls_by_name);
        match vm.exec(&image) {
            StopReason::End(code) if code.to_i32() == 3 => (),
            _ => panic!("Unexpected stop reason"),
        }
        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should park at EOF after END"),
        }

        compiler.compile_more(&mut image, &mut b"OUT 2".as_slice()).unwrap();
        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should resume at newly appended code"),
        }
        assert_eq!(["2"], *data.borrow().as_slice());

        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should stop at EOF after appended code"),
        }
    }

    #[tokio::test]
    async fn test_exec_exception_can_resume_after_append() {
        let data = Rc::from(RefCell::from(vec![]));
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("OUT"), OutCommand::new(data.clone()));

        let mut compiler = Compiler::new(&upcalls_by_name, &[]).unwrap();
        let mut image = Image::default();
        compiler.compile_more(&mut image, &mut b"a = 1 / 0".as_slice()).unwrap();

        let mut vm = Vm::new(upcalls_by_name);
        match vm.exec(&image) {
            StopReason::Exception(_, msg) if msg == "Division by zero" => (),
            _ => panic!("Unexpected stop reason"),
        }
        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should park at EOF after an exception"),
        }

        compiler.compile_more(&mut image, &mut b"OUT 2".as_slice()).unwrap();
        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should resume at newly appended code"),
        }
        assert_eq!(["2"], *data.borrow().as_slice());

        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should stop at EOF after appended code"),
        }
    }

    #[tokio::test]
    async fn test_exec_upcall_can_return_with_scope_helper() {
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("RET42"), ReturnFortyTwoFunction::new());

        let compiler = Compiler::new(&upcalls_by_name, &[]).unwrap();
        let image = compiler.compile(&mut b"x = RET42".as_slice()).unwrap();
        let mut vm = Vm::new(upcalls_by_name);
        run_to_end(&mut vm, &image).await;

        assert_eq!(
            Some(ConstantDatum::Integer(42)),
            vm.get_program(&image, &SymbolKey::from("x")).unwrap()
        );
    }

    #[tokio::test]
    async fn test_exec_upcall_io_error_is_reported() {
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("IOFAIL"), IoErrorCommand::new());

        let compiler = Compiler::new(&upcalls_by_name, &[]).unwrap();
        let image = compiler.compile(&mut b"IOFAIL".as_slice()).unwrap();
        let mut vm = Vm::new(upcalls_by_name);

        match vm.exec(&image) {
            StopReason::Exception(_, msg) if msg == "mock I/O error" => (),
            _ => panic!("Execution should stop at an IOFAIL exception"),
        };

        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should stop at EOF after serving error"),
        }
    }

    #[tokio::test]
    async fn test_exec_upcall_io_error_can_be_caught() {
        let data = Rc::from(RefCell::from(vec![]));
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("IOFAIL"), IoErrorCommand::new());
        upcalls_by_name.insert(SymbolKey::from("OUT"), OutCommand::new(data.clone()));

        let compiler = Compiler::new(&upcalls_by_name, &[]).unwrap();
        let image = compiler
            .compile(
                &mut br#"
                    ON ERROR GOTO @recover
                    IOFAIL
                    END 5
                    @recover
                    OUT "ok"
                "#
                .as_slice(),
            )
            .unwrap();
        let mut vm = Vm::new(upcalls_by_name);

        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should complete after handling IOFAIL"),
        };

        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should have reached EOF after OUT"),
        }

        assert_eq!(["ok"], *data.borrow().as_slice());
        assert_eq!(
            Some((LineCol { line: 3, col: 21 }, "mock I/O error".to_owned())),
            vm.last_error
        );
    }

    #[tokio::test]
    async fn test_exec_yields_on_backward_jump() {
        let compiler = Compiler::new(&HashMap::default(), &[]).unwrap();
        let image = compiler.compile(&mut b"x = 0: DO: x = x + 1: LOOP".as_slice()).unwrap();
        let mut vm = Vm::new(HashMap::default());

        match vm.exec(&image) {
            StopReason::Yield => (),
            _ => panic!("Execution should yield in a loop"),
        }
        assert_eq!(
            Some(ConstantDatum::Integer(1)),
            vm.get_program(&image, &SymbolKey::from("x")).unwrap()
        );

        match vm.exec(&image) {
            StopReason::Yield => (),
            _ => panic!("Execution should continue yielding in a loop"),
        }
        assert_eq!(
            Some(ConstantDatum::Integer(2)),
            vm.get_program(&image, &SymbolKey::from("x")).unwrap()
        );

        vm.interrupt(&image);
        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should stop at EOF after interrupt"),
        }
    }

    #[tokio::test]
    async fn test_exec_yields_after_gosub_return() {
        let compiler = Compiler::new(&HashMap::default(), &[]).unwrap();
        let image =
            compiler.compile(&mut b"GOSUB @foo: END\n@foo: x = x + 1: RETURN".as_slice()).unwrap();
        let mut vm = Vm::new(HashMap::default());

        match vm.exec(&image) {
            StopReason::Yield => (),
            _ => panic!("Execution should yield after returning from GOSUB"),
        }
        assert_eq!(
            Some(ConstantDatum::Integer(1)),
            vm.get_program(&image, &SymbolKey::from("x")).unwrap()
        );

        match vm.exec(&image) {
            StopReason::End(code) if code.is_success() => (),
            _ => panic!("Execution should continue after yield"),
        }
    }

    #[tokio::test]
    async fn test_interrupt_parks_execution_at_eof() {
        let data = Rc::from(RefCell::from(vec![]));
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("OUT"), OutCommand::new(data.clone()));

        let compiler = Compiler::new(&upcalls_by_name, &[]).unwrap();
        let image = compiler.compile(&mut b"OUT 1: OUT 2".as_slice()).unwrap();
        let mut vm = Vm::new(upcalls_by_name);

        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should stop at EOF"),
        }
        assert_eq!(["1", "2"], *data.borrow().as_slice());

        vm.interrupt(&image);
        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should be parked at EOF after interruption"),
        }
        assert_eq!(["1", "2"], *data.borrow().as_slice());
    }

    #[tokio::test]
    async fn test_clear_resets_runtime_state() {
        let compiler = Compiler::new(&HashMap::default(), &[]).unwrap();
        let image = compiler.compile(&mut b"x = 7".as_slice()).unwrap();
        let mut vm = Vm::new(HashMap::default());
        run_to_end(&mut vm, &image).await;

        assert_eq!(
            Some(ConstantDatum::Integer(7)),
            vm.get_program(&image, &SymbolKey::from("x")).unwrap()
        );

        vm.clear();

        assert_eq!(
            Some(ConstantDatum::Integer(0)),
            vm.get_program(&image, &SymbolKey::from("x")).unwrap()
        );
    }

    #[tokio::test]
    async fn test_clear_preserves_upcall_caches() {
        let data = Rc::from(RefCell::from(vec![]));
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("OUT"), OutCommand::new(data.clone()));

        let compiler = Compiler::new(&upcalls_by_name, &[]).unwrap();
        let image = compiler.compile(&mut b"OUT 3".as_slice()).unwrap();
        let mut vm = Vm::new(upcalls_by_name);

        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should stop at EOF"),
        }
        assert_eq!(["3"], *data.borrow().as_slice());

        vm.clear();

        match vm.exec(&image) {
            StopReason::Eof => (),
            _ => panic!("Execution should still stop at EOF after clear"),
        }
        assert_eq!(["3", "3"], *data.borrow().as_slice());
    }

    #[tokio::test]
    async fn test_reset_preserves_call_stack_limit() {
        let compiler = Compiler::new(&HashMap::default(), &[]).unwrap();
        let image = compiler
            .compile(
                &mut br#"
                    SUB recurse(n%)
                        IF n < 20 THEN
                            recurse n + 1
                        END IF
                    END SUB

                    recurse 0
                "#
                .as_slice(),
            )
            .unwrap();
        let mut vm = Vm::new_with_limits(
            HashMap::default(),
            Limits { max_call_stack: 8, max_heap_entries: U24::MAX },
        );

        match vm.exec(&image) {
            StopReason::Exception(_, msg) if msg == "Out of call stack space" => (),
            _ => panic!("Execution should stop when the call stack limit is reached"),
        }

        vm.reset();

        match vm.exec(&image) {
            StopReason::Exception(_, msg) if msg == "Out of call stack space" => (),
            _ => panic!("Execution should preserve the configured call stack limit after reset"),
        }
    }

    #[tokio::test]
    async fn test_scope_get_pos_no_args() {
        let positions: Rc<RefCell<Vec<LineCol>>> = Rc::default();
        let cmd = PosCapture::new(0, positions.clone());
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("POS_CAPTURE"), cmd);

        let compiler = Compiler::new(&upcalls_by_name, &[]).unwrap();
        let image = compiler.compile(&mut b"POS_CAPTURE".as_slice()).unwrap();
        let mut vm = Vm::new(upcalls_by_name);
        run_to_end(&mut vm, &image).await;

        let pos = positions.borrow();
        assert_eq!(&[] as &[LineCol], pos.as_slice());
    }

    #[tokio::test]
    async fn test_scope_get_pos_single_arg() {
        let positions: Rc<RefCell<Vec<LineCol>>> = Rc::default();
        let cmd = PosCapture::new(1, positions.clone());
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("POS_CAPTURE"), cmd);

        let compiler = Compiler::new(&upcalls_by_name, &[]).unwrap();
        let image = compiler.compile(&mut b"POS_CAPTURE 42".as_slice()).unwrap();
        let mut vm = Vm::new(upcalls_by_name);
        run_to_end(&mut vm, &image).await;

        let pos = positions.borrow();
        assert_eq!(&[LineCol { line: 1, col: 13 }], pos.as_slice());
    }

    #[tokio::test]
    async fn test_scope_get_pos_multiple_args() {
        let positions: Rc<RefCell<Vec<LineCol>>> = Rc::default();
        let cmd = PosCapture::new(3, positions.clone());
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("POS_CAPTURE"), cmd);

        let compiler = Compiler::new(&upcalls_by_name, &[]).unwrap();
        let image = compiler.compile(&mut b"POS_CAPTURE 1, 2, 3".as_slice()).unwrap();
        let mut vm = Vm::new(upcalls_by_name);
        run_to_end(&mut vm, &image).await;

        let pos = positions.borrow();
        assert_eq!(
            &[
                LineCol { line: 1, col: 13 },
                LineCol { line: 1, col: 16 },
                LineCol { line: 1, col: 19 }
            ],
            pos.as_slice()
        );
    }

    #[tokio::test]
    async fn test_scope_get_pos_expression_arg() {
        let positions: Rc<RefCell<Vec<LineCol>>> = Rc::default();
        let cmd = PosCapture::new(1, positions.clone());
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("POS_CAPTURE"), cmd);

        let compiler = Compiler::new(&upcalls_by_name, &[]).unwrap();
        let image = compiler.compile(&mut b"POS_CAPTURE 1 + 2".as_slice()).unwrap();
        let mut vm = Vm::new(upcalls_by_name);
        run_to_end(&mut vm, &image).await;

        let pos = positions.borrow();
        assert_eq!(&[LineCol { line: 1, col: 13 }], pos.as_slice());
    }

    #[tokio::test]
    async fn test_get_program_scalar() {
        let compiler = Compiler::new(&HashMap::default(), &[]).unwrap();
        let image = compiler.compile(&mut b"x = 123".as_slice()).unwrap();
        let mut vm = Vm::new(HashMap::default());
        run_to_end(&mut vm, &image).await;

        assert_eq!(
            Some(ConstantDatum::Integer(123)),
            vm.get_program(&image, &SymbolKey::from("x")).unwrap()
        );
        assert_eq!(None, vm.get_program(&image, &SymbolKey::from("missing")).unwrap());
    }

    #[tokio::test]
    async fn test_get_program_array() {
        let compiler = Compiler::new(&HashMap::default(), &[]).unwrap();
        let image =
            compiler.compile(&mut b"DIM arr(2) AS INTEGER: arr(1) = 45".as_slice()).unwrap();
        let mut vm = Vm::new(HashMap::default());
        run_to_end(&mut vm, &image).await;

        assert_eq!(
            Some(ConstantDatum::Integer(45)),
            vm.get_program_array(&image, &SymbolKey::from("arr"), &[1]).unwrap()
        );
    }

    #[tokio::test]
    async fn test_get_program_type_mismatch_errors() {
        let compiler = Compiler::new(&HashMap::default(), &[]).unwrap();
        let image =
            compiler.compile(&mut b"x = 1: DIM arr(2) AS INTEGER: arr(1) = 45".as_slice()).unwrap();
        let mut vm = Vm::new(HashMap::default());
        run_to_end(&mut vm, &image).await;

        match vm.get_program(&image, &SymbolKey::from("arr")) {
            Err(GetGlobalError::IsArray(name)) => assert_eq!("ARR", name),
            other => panic!("Unexpected result: {:?}", other),
        }

        match vm.get_program_array(&image, &SymbolKey::from("x"), &[0]) {
            Err(GetGlobalError::IsScalar(name)) => assert_eq!("X", name),
            other => panic!("Unexpected result: {:?}", other),
        }
    }

    #[tokio::test]
    async fn test_get_program_array_out_of_bounds() {
        let compiler = Compiler::new(&HashMap::default(), &[]).unwrap();
        let image =
            compiler.compile(&mut b"DIM arr(2) AS INTEGER: arr(1) = 45".as_slice()).unwrap();
        let mut vm = Vm::new(HashMap::default());
        run_to_end(&mut vm, &image).await;

        match vm.get_program_array(&image, &SymbolKey::from("arr"), &[3]) {
            Err(GetGlobalError::SubscriptOutOfBounds(_)) => (),
            other => panic!("Unexpected result: {:?}", other),
        }
    }
}
