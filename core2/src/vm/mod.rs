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

//! Virtual machine for EndBASIC execution.

use crate::CallResult;
use crate::bytecode::Register;
use crate::callable::{Callable, Scope};
use crate::compiler::SymbolKey;
use crate::image::Image;
use crate::mem::Datum;
use crate::reader::LineCol;
use std::collections::HashMap;
use std::rc::Rc;

mod context;
use context::{Context, InternalStopReason};

/// Opaque handle to invoke a pending upcall.
pub struct UpcallHandler<'a>(&'a mut Vm);

impl<'a> UpcallHandler<'a> {
    /// Invokes the pending upcall.
    pub async fn invoke(mut self) -> CallResult<()> {
        let vm = &mut self.0;
        let (index, first_reg) = vm
            .pending_upcall
            .take()
            .expect("This is only reachable when the VM has a pending upcall");
        vm.upcalls[usize::from(index)].exec(vm.upcall_scope(first_reg)).await
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
    heap: Vec<Datum>,

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
    fn upcall_scope<'a>(&'a self, reg: Register) -> Scope<'a> {
        let constants = match self.image.as_ref() {
            Some(image) => image.constants.as_slice(),
            None => &[],
        };
        Scope { regs: self.context.get_local_regs(reg), constants, heap: &self.heap }
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
