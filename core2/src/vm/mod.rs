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
use crate::bytecode::Register;
use crate::callable::{Callable, Scope};
use crate::compiler::SymbolKey;
use crate::image::Image;
use crate::mem::{ConstantDatum, DatumPtr, HeapDatum};
use crate::reader::LineCol;
use std::collections::HashMap;
use std::rc::Rc;

mod context;
use context::{Context, InternalStopReason};

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
        let (index, first_reg) = vm
            .pending_upcall
            .take()
            .expect("This is only reachable when the VM has a pending upcall");
        let upcall = vm.upcalls[usize::from(index)].clone();
        upcall.exec(vm.upcall_scope(first_reg)).await
    }
}

/// Representation of termination states from program execution.
pub enum StopReason<'a> {
    /// Execution terminated due to an `END` instruction.
    End(i32),

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

    /// Details about the pending upcall that has to be handled by the caller.
    pending_upcall: Option<(u16, Register)>,
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
    }

    /// Constructs a `Scope` for an upcall with arguments starting at `reg`.
    fn upcall_scope<'a>(&'a mut self, reg: Register) -> Scope<'a> {
        let constants = match self.image.as_ref() {
            Some(image) => image.constants.as_slice(),
            None => &[],
        };
        self.context.upcall_scope(reg, constants, &mut self.heap)
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
        let Some(image) = self.image.as_ref() else {
            return StopReason::End(0);
        };

        if self.pending_upcall.is_some() {
            return StopReason::Upcall(UpcallHandler(self));
        };

        match self.context.exec(image, &mut self.heap) {
            InternalStopReason::End(code) => StopReason::End(code),
            InternalStopReason::Exception(pc, e) => {
                let pos = image.debug_info.instr_linecols[pc];
                StopReason::Exception(pos, e)
            }
            InternalStopReason::Upcall(index, first_reg) => {
                self.pending_upcall = Some((index, first_reg));
                StopReason::Upcall(UpcallHandler(self))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::{SymbolKey, compile, only_metadata};
    use crate::image::Image;
    use crate::testutils::OutCommand;
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::rc::Rc;

    #[test]
    fn test_exec_without_load_is_eof() {
        let mut vm = Vm::new(HashMap::default());
        match vm.exec() {
            StopReason::End(0) => (),
            _ => panic!("Unexpected stop reason"),
        }
    }

    #[test]
    fn test_exec_empty_image_is_eof() {
        let mut vm = Vm::new(HashMap::default());
        vm.load(Image::default());
        match vm.exec() {
            StopReason::End(0) => (),
            _ => panic!("Unexpected stop reason"),
        }
    }

    #[test]
    fn test_exec_empty_compilation_is_eof() {
        let mut vm = Vm::new(HashMap::default());
        let image = compile(&mut b"".as_slice(), &HashMap::default()).unwrap();
        vm.load(image);
        match vm.exec() {
            StopReason::End(0) => (),
            _ => panic!("Unexpected stop reason"),
        }
    }

    #[tokio::test]
    async fn test_exec_upcall_flow() {
        let data = Rc::from(RefCell::from(vec![]));
        let mut upcalls_by_name: HashMap<SymbolKey, Rc<dyn Callable>> = HashMap::new();
        upcalls_by_name.insert(SymbolKey::from("OUT"), OutCommand::new(data.clone()));

        let image =
            compile(&mut b"OUT 30: OUT 20".as_slice(), &only_metadata(&upcalls_by_name)).unwrap();

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
            StopReason::End(0) => (),
            _ => panic!("Fourth exec should stop at EOF"),
        }
        assert_eq!(["30", "20"], *data.borrow().as_slice());
    }

    #[tokio::test]
    async fn test_exec_end_code_default() {
        let mut vm = Vm::new(HashMap::default());
        let image = compile(&mut b"END".as_slice(), &HashMap::default()).unwrap();
        vm.load(image);
        match vm.exec() {
            StopReason::End(0) => (),
            _ => panic!("Unexpected stop reason"),
        }
    }

    #[tokio::test]
    async fn test_exec_end_code_explicit() {
        let mut vm = Vm::new(HashMap::default());
        let image = compile(&mut b"END 3".as_slice(), &HashMap::default()).unwrap();
        vm.load(image);
        match vm.exec() {
            StopReason::End(3) => (),
            _ => panic!("Unexpected stop reason"),
        }
    }
}
