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

use crate::CallResult;
use crate::ast::ExprType;
use crate::bytecode::{ExitCode, Register};
use crate::callable::{Callable, Scope};
use crate::compiler::SymbolKey;
use crate::image::Image;
use crate::mem::{ConstantDatum, DatumPtr, HeapDatum};
use crate::reader::LineCol;
use std::collections::HashMap;
use std::rc::Rc;

mod context;
use context::{Context, ErrorHandler, InternalStopReason};

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
pub struct UpcallHandler<'a>(&'a mut Vm);

impl<'a> UpcallHandler<'a> {
    /// Invokes the pending upcall.
    pub async fn invoke(self) -> CallResult<()> {
        let vm = self.0;
        let (index, first_reg, upcall_pc) = vm
            .pending_upcall
            .take()
            .expect("This is only reachable when the VM has a pending upcall");
        let upcall = vm.upcalls[usize::from(index)].clone();
        match upcall.exec(vm.upcall_scope(first_reg, upcall_pc)).await {
            Ok(()) => Ok(()),
            Err(e) => {
                let pos_override = vm.image.as_ref().and_then(|image| {
                    image.debug_info.instrs[upcall_pc].arg_linecols.first().copied()
                });
                vm.handle_exception(upcall_pc, e.to_string(), pos_override);
                Ok(())
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

    /// Execution stopped due to an upcall that requires service from the caller.
    Upcall(UpcallHandler<'a>),
}

/// Virtual machine for EndBASIC program execution.
pub struct Vm {
    /// Mapping of all available upcall names to their handlers.
    upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>>,

    /// Active image for execution.
    image: Option<Image>,

    /// Upcalls used by the loaded image in index order.
    upcalls: Vec<Rc<dyn Callable>>,

    /// Heap memory for dynamic allocations.
    heap: Vec<HeapDatum>,

    /// Processor context for execution.
    context: Context,

    /// Last error seen by the VM, if any.
    last_error: Option<String>,

    /// Pending exception to report to the caller.
    pending_exception: Option<(LineCol, String)>,

    /// Details about the pending upcall that has to be handled by the caller.
    ///
    /// The tuple contains the upcall index, the first argument register, and the PC of the
    /// UPCALL instruction (for arg position lookup in `DebugInfo`).
    pending_upcall: Option<(u16, Register, usize)>,
}

impl Vm {
    /// Creates a new VM with the given `upcalls_by_name` as the available built-in callables.
    pub fn new(upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>>) -> Self {
        Self {
            upcalls_by_name,
            image: None,
            upcalls: vec![],
            heap: vec![],
            context: Context::default(),
            last_error: None,
            pending_exception: None,
            pending_upcall: None,
        }
    }

    /// Loads an `image` into the VM for execution, resetting any previous execution state.
    pub fn load(&mut self, image: Image) {
        self.upcalls.clear();
        for key in &image.upcalls {
            self.upcalls.push(
                self.upcalls_by_name
                    .get(key)
                    .expect("All upcalls exposed during compilation must be present at runtime")
                    .clone(),
            );
        }

        self.image = Some(image);

        self.heap.clear();
        self.context = Context::default();
        self.last_error = None;
        self.pending_exception = None;
        self.pending_upcall = None;
    }

    /// Constructs a `Scope` for an upcall with arguments starting at `reg`.
    ///
    /// `upcall_pc` is the address of the UPCALL instruction in the image, used to look up
    /// per-argument source locations from `DebugInfo`.
    fn upcall_scope<'a>(&'a mut self, reg: Register, upcall_pc: usize) -> Scope<'a> {
        let (constants, arg_linecols, data) = match self.image.as_ref() {
            Some(image) => (
                image.constants.as_slice(),
                image
                    .debug_info
                    .instrs
                    .get(upcall_pc)
                    .map(|m| m.arg_linecols.as_slice())
                    .unwrap_or(&[]),
                image.data.as_slice(),
            ),
            None => (&[][..], &[][..], &[][..]),
        };
        self.context.upcall_scope(
            reg,
            constants,
            &mut self.heap,
            arg_linecols,
            &self.last_error,
            data,
        )
    }

    /// Handles an exception raised at `pc` with `message`.  Returns true if the error was handled.
    fn handle_exception(
        &mut self,
        pc: usize,
        message: String,
        pos_override: Option<LineCol>,
    ) -> bool {
        let Some(image) = self.image.as_ref() else {
            let pos = pos_override.unwrap_or(LineCol { line: 0, col: 0 });
            self.pending_exception = Some((pos, message));
            return false;
        };

        let pos = pos_override.unwrap_or(image.debug_info.instrs[pc].linecol);
        self.last_error = Some(format!("{}: {}", pos, message));
        self.pending_exception = None;

        match self.context.error_handler() {
            ErrorHandler::None => {
                self.pending_exception = Some((pos, message));
                false
            }
            ErrorHandler::Jump(addr) => {
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

    /// Returns the value of the global scalar variable `name` as a `ConstantDatum`.
    ///
    /// Returns `Ok(None)` if the variable is not defined (no image is loaded or the
    /// variable was not declared).  Returns `Err` if the variable exists but is an
    /// array; in that case, use `get_global_array` instead.
    pub fn get_global(&self, name: &str) -> GetGlobalResult<Option<ConstantDatum>> {
        let key = SymbolKey::from(name);
        let Some(image) = self.image.as_ref() else {
            return Ok(None);
        };
        let Some(info) = image.debug_info.global_vars.get(&key) else {
            return Ok(None);
        };
        if info.ndims != 0 {
            return Err(GetGlobalError::IsArray(name.to_owned()));
        }
        let raw = self.context.get_global_reg_raw(info.reg);
        let datum = match info.subtype {
            ExprType::Boolean => ConstantDatum::Boolean(raw != 0),
            ExprType::Double => ConstantDatum::Double(f64::from_bits(raw)),
            ExprType::Integer => ConstantDatum::Integer(raw as i32),
            ExprType::Text => {
                let ptr = DatumPtr::from(raw);
                ConstantDatum::Text(ptr.resolve_string(&image.constants, &self.heap).to_owned())
            }
        };
        Ok(Some(datum))
    }

    /// Returns the value of an element in the global array variable `name` at the given
    /// `subscripts` as a `ConstantDatum`.
    ///
    /// Returns `Ok(None)` if the variable is not defined (no image is loaded or the
    /// variable was not declared).  Returns `Err` if the variable exists but is a scalar
    /// (use `get_global` instead), or if the subscripts are out of bounds.
    pub fn get_global_array(
        &self,
        name: &str,
        subscripts: &[i32],
    ) -> GetGlobalResult<Option<ConstantDatum>> {
        let key = SymbolKey::from(name);
        let Some(image) = self.image.as_ref() else {
            return Ok(None);
        };
        let Some(info) = image.debug_info.global_vars.get(&key) else {
            return Ok(None);
        };
        if info.ndims == 0 {
            return Err(GetGlobalError::IsScalar(name.to_owned()));
        }
        let raw = self.context.get_global_reg_raw(info.reg);
        let ptr = DatumPtr::from(raw);
        let heap_idx = ptr.heap_index();
        let HeapDatum::Array(a) = &self.heap[heap_idx] else {
            panic!("Array variable does not point to an array on the heap");
        };
        let flat_idx = a.flat_index(subscripts).map_err(GetGlobalError::SubscriptOutOfBounds)?;
        let v = a.values[flat_idx];
        let datum = match info.subtype {
            ExprType::Boolean => ConstantDatum::Boolean(v != 0),
            ExprType::Double => ConstantDatum::Double(f64::from_bits(v)),
            ExprType::Integer => ConstantDatum::Integer(v as i32),
            ExprType::Text => {
                let ptr = DatumPtr::from(v);
                ConstantDatum::Text(ptr.resolve_string(&image.constants, &self.heap).to_owned())
            }
        };
        Ok(Some(datum))
    }

    /// Starts or resumes execution of the loaded image.
    ///
    /// Returns a `StopReason` indicating why execution stopped, which may be due to program
    /// termination, an exception, or a pending upcall that requires caller handling.
    pub fn exec(&mut self) -> StopReason<'_> {
        loop {
            if let Some((pos, message)) = self.pending_exception.take() {
                return StopReason::Exception(pos, message);
            }

            let Some(image) = self.image.as_ref() else {
                return StopReason::Eof;
            };

            if self.pending_upcall.is_some() {
                return StopReason::Upcall(UpcallHandler(self));
            }

            match self.context.exec(image, &mut self.heap) {
                InternalStopReason::End(code) => return StopReason::End(code),
                InternalStopReason::Eof => return StopReason::Eof,
                InternalStopReason::Exception(pc, e) => {
                    if !self.handle_exception(pc, e, None)
                        && let Some((pos, message)) = self.pending_exception.take()
                    {
                        return StopReason::Exception(pos, message);
                    }
                }
                InternalStopReason::Upcall(index, first_reg, upcall_pc) => {
                    self.pending_upcall = Some((index, first_reg, upcall_pc));
                    return StopReason::Upcall(UpcallHandler(self));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{ArgSep, ExprType};
    use crate::callable::{
        ArgSepSyntax, CallResult, CallableMetadata, CallableMetadataBuilder, RequiredValueSyntax,
        SingularArgSyntax,
    };
    use crate::compiler::{SymbolKey, compile, only_metadata};
    use crate::image::Image;
    use crate::reader::LineCol;
    use crate::testutils::OutCommand;
    use async_trait::async_trait;
    use std::borrow::Cow;
    use std::cell::RefCell;
    use std::collections::HashMap;
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

    #[async_trait(?Send)]
    impl Callable for PosCapture {
        fn metadata(&self) -> Rc<CallableMetadata> {
            self.metadata.clone()
        }

        async fn exec(&self, scope: Scope<'_>) -> CallResult<()> {
            let mut positions = self.positions.borrow_mut();
            for i in 0..self.nargs {
                positions.push(scope.get_pos(i));
            }
            Ok(())
        }
    }

    /// Runs the VM to completion, invoking every upcall as it is encountered.
    async fn run_to_end(vm: &mut Vm) {
        loop {
            match vm.exec() {
                StopReason::End(_) => break,
                StopReason::Eof => break,
                StopReason::Exception(_, msg) => panic!("Unexpected exception: {}", msg),
                StopReason::Upcall(handler) => handler.invoke().await.unwrap(),
            }
        }
    }

    #[test]
    fn test_exec_without_load_is_eof() {
        let mut vm = Vm::new(HashMap::default());
        match vm.exec() {
            StopReason::Eof => (),
            _ => panic!("Unexpected stop reason"),
        }
    }

    #[test]
    fn test_exec_empty_image_is_eof() {
        let mut vm = Vm::new(HashMap::default());
        vm.load(Image::default());
        match vm.exec() {
            StopReason::Eof => (),
            _ => panic!("Unexpected stop reason"),
        }
    }

    #[test]
    fn test_exec_empty_compilation_is_eof() {
        let mut vm = Vm::new(HashMap::default());
        let image = compile(&mut b"".as_slice(), HashMap::default()).unwrap();
        vm.load(image);
        match vm.exec() {
            StopReason::Eof => (),
            _ => panic!("Unexpected stop reason"),
        }
    }

    #[tokio::test]
    async fn test_exec_upcall_flow() {
        let data = Rc::from(RefCell::from(vec![]));
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("OUT"), OutCommand::new(data.clone()));

        let image =
            compile(&mut b"OUT 30: OUT 20".as_slice(), only_metadata(&upcalls_by_name)).unwrap();

        let mut vm = Vm::new(upcalls_by_name);
        vm.load(image);

        match vm.exec() {
            StopReason::Upcall(_handler) => (),
            _ => panic!("First exec should stop at the first upcall"),
        }
        assert!(data.borrow().is_empty());

        match vm.exec() {
            StopReason::Upcall(handler) => handler.invoke().await.unwrap(),
            _ => panic!("Second exec should stop at the same upcall (not yet executed)"),
        }
        assert_eq!(["30"], *data.borrow().as_slice());

        match vm.exec() {
            StopReason::Upcall(handler) => handler.invoke().await.unwrap(),
            _ => panic!("Third exec should stop at the second upcall"),
        }
        assert_eq!(["30", "20"], *data.borrow().as_slice());

        match vm.exec() {
            StopReason::Eof => (),
            _ => panic!("Fourth exec should stop at EOF"),
        }
        assert_eq!(["30", "20"], *data.borrow().as_slice());
    }

    #[tokio::test]
    async fn test_exec_end_code_default() {
        let mut vm = Vm::new(HashMap::default());
        let image = compile(&mut b"END".as_slice(), HashMap::default()).unwrap();
        vm.load(image);
        match vm.exec() {
            StopReason::End(code) if code.is_success() => (),
            _ => panic!("Unexpected stop reason"),
        }
    }

    #[tokio::test]
    async fn test_exec_end_code_explicit() {
        let mut vm = Vm::new(HashMap::default());
        let image = compile(&mut b"END 3".as_slice(), HashMap::default()).unwrap();
        vm.load(image);
        match vm.exec() {
            StopReason::End(code) if code.to_i32() == 3 => (),
            _ => panic!("Unexpected stop reason"),
        }
    }

    #[tokio::test]
    async fn test_scope_get_pos_no_args() {
        let positions: Rc<RefCell<Vec<LineCol>>> = Rc::default();
        let cmd = PosCapture::new(0, positions.clone());
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("POS_CAPTURE"), cmd);

        let image =
            compile(&mut b"POS_CAPTURE".as_slice(), only_metadata(&upcalls_by_name)).unwrap();
        let mut vm = Vm::new(upcalls_by_name);
        vm.load(image);
        run_to_end(&mut vm).await;

        let pos = positions.borrow();
        assert_eq!(&[] as &[LineCol], pos.as_slice());
    }

    #[tokio::test]
    async fn test_scope_get_pos_single_arg() {
        let positions: Rc<RefCell<Vec<LineCol>>> = Rc::default();
        let cmd = PosCapture::new(1, positions.clone());
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("POS_CAPTURE"), cmd);

        let image =
            compile(&mut b"POS_CAPTURE 42".as_slice(), only_metadata(&upcalls_by_name)).unwrap();
        let mut vm = Vm::new(upcalls_by_name);
        vm.load(image);
        run_to_end(&mut vm).await;

        let pos = positions.borrow();
        assert_eq!(&[LineCol { line: 1, col: 13 }], pos.as_slice());
    }

    #[tokio::test]
    async fn test_scope_get_pos_multiple_args() {
        let positions: Rc<RefCell<Vec<LineCol>>> = Rc::default();
        let cmd = PosCapture::new(3, positions.clone());
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("POS_CAPTURE"), cmd);

        let image =
            compile(&mut b"POS_CAPTURE 1, 2, 3".as_slice(), only_metadata(&upcalls_by_name))
                .unwrap();
        let mut vm = Vm::new(upcalls_by_name);
        vm.load(image);
        run_to_end(&mut vm).await;

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

        let image =
            compile(&mut b"POS_CAPTURE 1 + 2".as_slice(), only_metadata(&upcalls_by_name)).unwrap();
        let mut vm = Vm::new(upcalls_by_name);
        vm.load(image);
        run_to_end(&mut vm).await;

        let pos = positions.borrow();
        assert_eq!(&[LineCol { line: 1, col: 13 }], pos.as_slice());
    }
}
