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

//! Build script for the crate.

use std::env;

fn main() {
    if cfg!(target_os = "windows") {
        // Point linker to the libraries prepared by setup-sdl.ps1.
        let current_dir = env::current_dir().unwrap();
        let libs = current_dir.parent().unwrap().join("libs");
        if libs.exists() {
            println!("cargo:rustc-link-search={}", libs.display());
        }
    }
}
