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

//! Compiled program representation.

use crate::callable::Callable;
use crate::compiler::SymbolKey;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone, Eq, Hash, PartialEq)]
pub(crate) enum Constant {
    //Double(f64),
    Integer(i32),
    Text(String),
}

pub struct Image {
    pub(crate) code: Vec<u32>,
    pub(crate) data: Vec<u32>,
    pub(crate) upcalls: Vec<SymbolKey>,
    pub(crate) constants: Vec<Constant>,
}

impl Image {
    pub fn map_upcalls(
        &self,
        upcalls_by_name: &HashMap<SymbolKey, Rc<dyn Callable>>,
    ) -> Vec<Rc<dyn Callable>> {
        let mut upcalls = Vec::with_capacity(self.upcalls.len());
        for key in &self.upcalls {
            upcalls.push(upcalls_by_name.get(&key).unwrap().clone());
        }
        upcalls
    }
}
