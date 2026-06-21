// EndBASIC
// Copyright 2021 Julio Merino
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

//! Stored program manipulation.

use crate::Yielder;
use crate::console::{Console, Pager, read_line};
use crate::storage::Storage;
use crate::strings::parse_boolean;
use crate::{MachineAction, MachineBuilder};
use async_trait::async_trait;
use endbasic_core::{
    ArgSepSyntax, CallError, CallResult, Callable, CallableMetadata, CallableMetadataBuilder,
    Compiler, ExprType, RequiredValueSyntax, Scope, SingularArgSyntax, SymbolKey,
};
use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::io;
use std::rc::Rc;
use std::str;

/// Category description for all symbols provided by this module.
const CATEGORY: &str = "Stored program
The EndBASIC interpreter has a piece of read/write memory called the \"stored program\".  This \
memory serves to maintain the code of a program you edit and manipulate right from the \
interpreter.
The common flow to interact with a stored program is to load a program from disk using the LOAD \
command, modify its contents via the EDIT command, execute the program via the RUN command, and \
finally save the new or modified program via the SAVE command.
Be aware that the stored program's content is lost whenever you load a program, exit the \
interpreter, or use the NEW command.  These operations will ask you to save the program if you \
have forgotten to do so, but it's better to get in the habit of saving often.
See the \"File system\" help topic for information on where the programs can be saved and loaded \
from.";

/// Message to print on the console when receiving a break signal.
pub const BREAK_MSG: &str = "**** BREAK ****";

/// Default extension to add to file names.
const DEFAULT_EXTENSION: &str = "bas";

/// Representation of the single program that we can keep in memory.
#[async_trait(?Send)]
pub trait Program {
    /// Returns true if the program was modified since it was last saved (as indicated by a call to
    /// `set_name`).
    fn is_dirty(&self) -> bool;

    /// Edits the program interactively via the given `console`.
    async fn edit(&mut self, console: &mut dyn Console) -> io::Result<()>;

    /// Reloads the contents of the stored program with the given `text` and tracks them as coming
    /// from the file given in `name`.
    fn load(&mut self, name: Option<&str>, text: &str);

    /// Path of the loaded program.  Should be `None` if the program has never been saved yet.
    fn name(&self) -> Option<&str>;

    /// Resets the name of the program.  Used when saving it.
    fn set_name(&mut self, name: &str);

    /// Gets the contents of the stored program as a single string.
    fn text(&self) -> String;
}

/// Trivial implementation of a recorded program that doesn't support editing.
#[derive(Default)]
pub(crate) struct ImmutableProgram {
    name: Option<String>,
    text: String,
}

#[async_trait(?Send)]
impl Program for ImmutableProgram {
    fn is_dirty(&self) -> bool {
        false
    }

    async fn edit(&mut self, _console: &mut dyn Console) -> io::Result<()> {
        Err(io::Error::other("Editing not supported"))
    }

    fn load(&mut self, name: Option<&str>, text: &str) {
        self.name = name.map(str::to_owned);
        text.clone_into(&mut self.text);
    }

    fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    fn set_name(&mut self, name: &str) {
        self.name = Some(name.to_owned());
    }

    fn text(&self) -> String {
        self.text.clone()
    }
}

/// If the `program` is dirty, asks if it's OK to continue on `console` and discard its changes.
pub async fn continue_if_modified(
    program: &dyn Program,
    console: &mut dyn Console,
) -> io::Result<bool> {
    if !program.is_dirty() {
        return Ok(true);
    }

    match program.name() {
        Some(name) => console.print(&format!("Current program {} has unsaved changes!", name))?,
        None => console.print("Current program has unsaved changes and has never been saved!")?,
    }
    let answer = read_line(console, "Discard and continue (y/N)? ", "", None).await?;
    Ok(parse_boolean(&answer).unwrap_or(false))
}

/// The `DISASM` command.
pub struct DisasmCommand {
    metadata: Rc<CallableMetadata>,
    callables_metadata: Rc<RefCell<HashMap<SymbolKey, Rc<CallableMetadata>>>>,
    console: Rc<RefCell<dyn Console>>,
    program: Rc<RefCell<dyn Program>>,
    yielder: Option<Rc<RefCell<dyn Yielder>>>,
}

struct MetadataCallable {
    metadata: Rc<CallableMetadata>,
}

#[async_trait(?Send)]
impl Callable for MetadataCallable {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    fn exec(&self, _scope: Scope<'_>) -> CallResult<()> {
        unreachable!("MetadataCallable::exec must not be called")
    }
}

impl DisasmCommand {
    /// Creates a new `DISASM` command that dumps the disassembled version of the program.
    pub fn new(
        callables_metadata: Rc<RefCell<HashMap<SymbolKey, Rc<CallableMetadata>>>>,
        console: Rc<RefCell<dyn Console>>,
        program: Rc<RefCell<dyn Program>>,
        yielder: Option<Rc<RefCell<dyn Yielder>>>,
    ) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("DISASM")
                .with_async(true)
                .with_syntax(&[(&[], None)])
                .with_category(CATEGORY)
                .with_description(
                    "Disassembles the stored program.
The assembly code printed by this command is provided as a tool to understand how high level code \
gets translated to the machine code of a fictitious stack-based machine.  Note, however, that the \
assembly code cannot be reassembled nor modified at this point.",
                )
                .build(),
            callables_metadata,
            console,
            program,
            yielder,
        })
    }
}

#[async_trait(?Send)]
impl Callable for DisasmCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn async_exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(0, scope.nargs());

        let image = {
            let metadata = self.callables_metadata.borrow();
            let mut callables = HashMap::with_capacity(metadata.len());
            for (name, metadata) in metadata.iter() {
                let callable = Rc::from(MetadataCallable { metadata: metadata.clone() });
                callables.insert(name.clone(), callable as Rc<dyn Callable>);
            }

            let compiler = Compiler::new(&callables, &[])
                .map_err(|e| CallError::Syntax(e.pos(), e.message_without_pos()))?;
            compiler
                .compile(&mut self.program.borrow().text().as_bytes())
                .map_err(|e| CallError::Syntax(e.pos(), e.message_without_pos()))?
        };

        let mut console = self.console.borrow_mut();
        let mut pager = Pager::new(&mut *console, self.yielder.clone())?;
        for line in image.disasm() {
            pager.print(&line).await?;
        }
        pager.print("").await?;

        Ok(())
    }
}

/// The `EDIT` command.
pub struct EditCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
    program: Rc<RefCell<dyn Program>>,
}

impl EditCommand {
    /// Creates a new `EDIT` command that edits the stored `program` in the `console`.
    pub fn new(console: Rc<RefCell<dyn Console>>, program: Rc<RefCell<dyn Program>>) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("EDIT")
                .with_async(true)
                .with_syntax(&[(&[], None)])
                .with_category(CATEGORY)
                .with_description("Interactively edits the stored program.")
                .build(),
            console,
            program,
        })
    }
}

#[async_trait(?Send)]
impl Callable for EditCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn async_exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(0, scope.nargs());

        let mut console = self.console.borrow_mut();
        let mut program = self.program.borrow_mut();
        program.edit(&mut *console).await?;
        Ok(())
    }
}

/// The `LIST` command.
pub struct ListCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
    program: Rc<RefCell<dyn Program>>,
    yielder: Option<Rc<RefCell<dyn Yielder>>>,
}

impl ListCommand {
    /// Creates a new `LIST` command that dumps the `program` to the `console`.
    pub fn new(
        console: Rc<RefCell<dyn Console>>,
        program: Rc<RefCell<dyn Program>>,
        yielder: Option<Rc<RefCell<dyn Yielder>>>,
    ) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("LIST")
                .with_async(true)
                .with_syntax(&[(&[], None)])
                .with_category(CATEGORY)
                .with_description("Prints the currently-loaded program.")
                .build(),
            console,
            program,
            yielder,
        })
    }
}

#[async_trait(?Send)]
impl Callable for ListCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn async_exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(0, scope.nargs());

        let mut console = self.console.borrow_mut();
        let mut pager = Pager::new(&mut *console, self.yielder.clone())?;
        for line in self.program.borrow().text().lines() {
            pager.print(line).await?;
        }
        Ok(())
    }
}

/// The `LOAD` command.
pub struct LoadCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
    storage: Rc<RefCell<Storage>>,
    program: Rc<RefCell<dyn Program>>,
    actions: Rc<RefCell<Vec<MachineAction>>>,
}

impl LoadCommand {
    /// Creates a new `LOAD` command that loads a program from `storage` into `program` and that
    /// uses `console` to communicate unsaved changes.
    pub fn new(
        console: Rc<RefCell<dyn Console>>,
        storage: Rc<RefCell<Storage>>,
        program: Rc<RefCell<dyn Program>>,
        actions: Rc<RefCell<Vec<MachineAction>>>,
    ) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("LOAD")
                .with_async(true)
                .with_syntax(&[(
                    &[SingularArgSyntax::RequiredValue(
                        RequiredValueSyntax {
                            name: Cow::Borrowed("filename"),
                            vtype: ExprType::Text,
                        },
                        ArgSepSyntax::End,
                    )],
                    None,
                )])
                .with_category(CATEGORY)
                .with_description(
                    "Loads the given program.
The filename must be a string and must be a valid EndBASIC path.  The .BAS extension is optional \
but, if present, it must be .BAS.
Any previously stored program is discarded from memory, but LOAD will pause to ask before \
discarding any unsaved modifications.
See the \"File system\" help topic for information on the path syntax.",
                )
                .build(),
            console,
            storage,
            program,
            actions,
        })
    }
}

#[async_trait(?Send)]
impl Callable for LoadCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn async_exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(1, scope.nargs());
        let pathname = scope.get_string(0);

        if continue_if_modified(&*self.program.borrow(), &mut *self.console.borrow_mut()).await? {
            let (full_name, content) = {
                let storage = self.storage.borrow();
                let full_name =
                    storage.make_canonical_with_extension(pathname, DEFAULT_EXTENSION)?;
                let content = storage.get(&full_name).await?;
                let content = match String::from_utf8(content) {
                    Ok(text) => text,
                    Err(e) => {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            format!("Invalid file content: {}", e),
                        )
                        .into());
                    }
                };
                (full_name, content)
            };
            self.program.borrow_mut().load(Some(&full_name), &content);
            self.actions.borrow_mut().push(MachineAction::Clear);
            Ok(())
        } else {
            self.console
                .borrow_mut()
                .print("LOAD aborted; use SAVE to save your current changes.")?;
            Ok(())
        }
    }
}

/// The `NEW` command.
pub struct NewCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
    program: Rc<RefCell<dyn Program>>,
    actions: Rc<RefCell<Vec<MachineAction>>>,
}

impl NewCommand {
    /// Creates a new `NEW` command that clears the contents of `program` and that uses `console`
    /// to communicate unsaved changes.
    pub fn new(
        console: Rc<RefCell<dyn Console>>,
        program: Rc<RefCell<dyn Program>>,
        actions: Rc<RefCell<Vec<MachineAction>>>,
    ) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("NEW")
                .with_async(true)
                .with_syntax(&[(&[], None)])
                .with_category(CATEGORY)
                .with_description(
                    "Restores initial machine state and creates a new program.
This command resets the machine to a pristine state by clearing all user-defined variables \
and restoring the state of shared resources.  These resources include: the console, whose color \
and video syncing bit are reset; and the GPIO pins, which are set to their default state.
The stored program is also discarded from memory, but NEW will pause to ask before discarding \
any unsaved modifications.  To reset resources but avoid clearing the stored program, use CLEAR \
instead.",
                )
                .build(),
            console,
            program,
            actions,
        })
    }
}

#[async_trait(?Send)]
impl Callable for NewCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn async_exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(0, scope.nargs());

        if continue_if_modified(&*self.program.borrow(), &mut *self.console.borrow_mut()).await? {
            self.program.borrow_mut().load(None, "");
            self.actions.borrow_mut().push(MachineAction::Clear);
        } else {
            self.console
                .borrow_mut()
                .print("NEW aborted; use SAVE to save your current changes.")?;
        }
        Ok(())
    }
}

/// The `RUN` command.
pub struct RunCommand {
    metadata: Rc<CallableMetadata>,
    program: Rc<RefCell<dyn Program>>,
    actions: Rc<RefCell<Vec<MachineAction>>>,
}

impl RunCommand {
    /// Creates a new `RUN` command that executes the `program`.
    pub fn new(
        program: Rc<RefCell<dyn Program>>,
        actions: Rc<RefCell<Vec<MachineAction>>>,
    ) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("RUN")
                .with_async(true)
                .with_syntax(&[(&[], None)])
                .with_category(CATEGORY)
                .with_description(
                    "Runs the stored program.
This issues a CLEAR operation before starting the program to prevent previous leftover state \
from interfering with the new execution.",
                )
                .build(),
            program,
            actions,
        })
    }
}

#[async_trait(?Send)]
impl Callable for RunCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn async_exec(&self, scope: Scope<'_>) -> CallResult<()> {
        debug_assert_eq!(0, scope.nargs());

        let program = self.program.borrow().text();
        self.actions.borrow_mut().push(MachineAction::Run(program));
        Ok(())
    }
}

/// The `SAVE` command.
pub struct SaveCommand {
    metadata: Rc<CallableMetadata>,
    console: Rc<RefCell<dyn Console>>,
    storage: Rc<RefCell<Storage>>,
    program: Rc<RefCell<dyn Program>>,
}

impl SaveCommand {
    /// Creates a new `SAVE` command that saves the contents of the `program` into `storage`.
    pub fn new(
        console: Rc<RefCell<dyn Console>>,
        storage: Rc<RefCell<Storage>>,
        program: Rc<RefCell<dyn Program>>,
    ) -> Rc<Self> {
        Rc::from(Self {
            metadata: CallableMetadataBuilder::new("SAVE")
                .with_async(true)
                .with_syntax(&[
                    (&[], None),
                    (
                        &[SingularArgSyntax::RequiredValue(
                            RequiredValueSyntax {
                                name: Cow::Borrowed("filename"),
                                vtype: ExprType::Text,
                            },
                            ArgSepSyntax::End,
                        )],
                        None,
                    ),
                ])
                .with_category(CATEGORY)
                .with_description(
                    "Saves the current program in memory to the given filename.
The filename must be a string and must be a valid EndBASIC path.  The .BAS extension is optional \
but, if present, it must be .BAS.
If no filename is given, SAVE will try to use the filename of the loaded program (if any) and \
will fail if no name has been given yet.
See the \"File system\" help topic for information on the path syntax.",
                )
                .build(),
            console,
            storage,
            program,
        })
    }
}

#[async_trait(?Send)]
impl Callable for SaveCommand {
    fn metadata(&self) -> Rc<CallableMetadata> {
        self.metadata.clone()
    }

    async fn async_exec(&self, scope: Scope<'_>) -> CallResult<()> {
        let name = if scope.nargs() == 0 {
            match self.program.borrow().name() {
                Some(name) => name.to_owned(),
                None => {
                    return Err(CallError::Precondition(
                        "Unnamed program; please provide a filename".to_owned(),
                    ));
                }
            }
        } else {
            debug_assert_eq!(1, scope.nargs());
            scope.get_string(0).to_owned()
        };

        let full_name =
            self.storage.borrow().make_canonical_with_extension(&name, DEFAULT_EXTENSION)?;
        let content = self.program.borrow().text();
        self.storage.borrow_mut().put(&full_name, content.as_bytes()).await?;
        self.program.borrow_mut().set_name(&full_name);

        self.console.borrow_mut().print(&format!("Saved as {}", full_name))?;

        Ok(())
    }
}

/// Adds all program editing commands against the stored `program` to the `machine`, using
/// `console` for interactive editing and using `storage` as the on-disk storage for the programs.
pub fn add_all(
    machine: &mut MachineBuilder,
    program: Rc<RefCell<dyn Program>>,
    console: Rc<RefCell<dyn Console>>,
    storage: Rc<RefCell<Storage>>,
    yielder: Option<Rc<RefCell<dyn Yielder>>>,
) {
    machine.add_callable(DisasmCommand::new(
        machine.callables_metadata(),
        console.clone(),
        program.clone(),
        yielder.clone(),
    ));
    machine.add_callable(EditCommand::new(console.clone(), program.clone()));
    machine.add_callable(ListCommand::new(console.clone(), program.clone(), yielder));
    machine.add_callable(LoadCommand::new(
        console.clone(),
        storage.clone(),
        program.clone(),
        machine.actions(),
    ));
    machine.add_callable(NewCommand::new(console.clone(), program.clone(), machine.actions()));
    machine.add_callable(RunCommand::new(program.clone(), machine.actions()));
    machine.add_callable(SaveCommand::new(console, storage, program));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::console::{CharsXY, Key};
    use crate::datetime::DateTime;
    use crate::testutils::*;
    use crate::{MachineBuilder, Signal};
    use async_trait::async_trait;
    use futures_lite::future::{FutureExt, block_on};
    use std::rc::Rc;
    use std::time::Duration;

    const NO_ANSWERS: &[&str] =
        &["n\n", "N\n", "no\n", "NO\n", "false\n", "FALSE\n", "xyz\n", "\n", "1\n"];

    const YES_ANSWERS: &[&str] = &["y\n", "yes\n", "Y\n", "YES\n", "true\n", "TRUE\n"];

    struct MockDateTime {
        on_sleep: Box<dyn Fn(Duration) -> futures_lite::future::BoxedLocal<Result<(), String>>>,
    }

    #[async_trait(?Send)]
    impl DateTime for MockDateTime {
        async fn sleep(&self, d: Duration) -> Result<(), String> {
            (self.on_sleep)(d).await
        }
    }

    #[test]
    fn test_disasm_nothing() {
        Tester::default()
            .run("DISASM")
            .expect_prints(["0000:   EOF                             ; 0:0", ""])
            .check();
    }

    #[test]
    fn test_disasm_ok() {
        Tester::default()
            .set_program(None, "A = 2 + 3")
            .run("DISASM")
            .expect_prints([
                "0000:   LOADI       R64, 2              ; 1:5",
                "0001:   LOADI       R65, 3              ; 1:9",
                "0002:   ADDI        R64, R64, R65       ; 1:7",
                "0003:   EOF                             ; 0:0",
                "",
            ])
            .expect_program(None as Option<&str>, "A = 2 + 3")
            .check();
    }

    #[test]
    fn test_disasm_paging() {
        let t = Tester::default();
        t.get_console().borrow_mut().set_interactive(true);
        t.get_console().borrow_mut().set_size_chars(CharsXY { x: 80, y: 4 });
        t.get_console().borrow_mut().add_input_keys(&[Key::NewLine]);
        t.set_program(None, "A = 2 + 3")
            .run("DISASM")
            .expect_prints([
                "0000:   LOADI       R64, 2              ; 1:5",
                "0001:   LOADI       R65, 3              ; 1:9",
                "0002:   ADDI        R64, R64, R65       ; 1:7",
                " << Press any key for more; ESC or Ctrl+C to stop >> ",
                "0003:   EOF                             ; 0:0",
                "",
            ])
            .expect_program(None as Option<&str>, "A = 2 + 3")
            .check();
    }

    #[test]
    fn test_disasm_code_errors() {
        Tester::default()
            .set_program(None, "A = 3 +")
            .run("DISASM")
            .expect_err("1:7: Not enough values to apply operator")
            .expect_program(None as Option<&str>, "A = 3 +")
            .check();
    }

    #[test]
    fn test_disasm_errors() {
        check_stmt_compilation_err("1:1: DISASM expected no arguments", "DISASM 2");
    }

    #[test]
    fn test_edit_ok() {
        Tester::default()
            .set_program(Some("foo.bas"), "previous\n")
            .add_input_chars("new line\n")
            .run("EDIT")
            .expect_program(Some("foo.bas"), "previous\nnew line\n")
            .check();
    }

    #[test]
    fn test_edit_errors() {
        check_stmt_compilation_err("1:1: EDIT expected no arguments", "EDIT 1");
    }

    #[test]
    fn test_list_ok() {
        Tester::default().run("LIST").check();

        Tester::default()
            .set_program(None, "one\n\nthree\n")
            .run("LIST")
            .expect_prints(["one", "", "three"])
            .expect_program(None as Option<&str>, "one\n\nthree\n")
            .check();
    }

    #[test]
    fn test_list_paging() {
        let t = Tester::default();
        t.get_console().borrow_mut().set_interactive(true);
        t.get_console().borrow_mut().set_size_chars(CharsXY { x: 30, y: 5 });
        t.get_console().borrow_mut().add_input_keys(&[Key::NewLine]);
        t.set_program(None, "one\n\nthree\nfour\nfive")
            .run("LIST")
            .expect_prints(["one", "", "three", "four", " << More >> ", "five"])
            .expect_program(None as Option<&str>, "one\n\nthree\nfour\nfive")
            .check();
    }

    #[test]
    fn test_list_errors() {
        check_stmt_compilation_err("1:1: LIST expected no arguments", "LIST 2");
    }

    #[test]
    fn test_load_ok() {
        let content = "line 1\n\n  line 2\n";
        for (explicit, canonical) in &[
            ("foo", "MEMORY:foo.bas"),
            ("foo.bas", "MEMORY:foo.bas"),
            ("BAR", "MEMORY:BAR.BAS"),
            ("BAR.BAS", "MEMORY:BAR.BAS"),
            ("Baz", "MEMORY:Baz.bas"),
        ] {
            Tester::default()
                .write_file("foo.bas", content)
                .write_file("foo.bak", "")
                .write_file("BAR.BAS", content)
                .write_file("Baz.bas", content)
                .run(format!(r#"LOAD "{}""#, explicit))
                .expect_clear()
                .expect_program(Some(*canonical), "line 1\n\n  line 2\n")
                .expect_file("MEMORY:/foo.bas", content)
                .expect_file("MEMORY:/foo.bak", "")
                .expect_file("MEMORY:/BAR.BAS", content)
                .expect_file("MEMORY:/Baz.bas", content)
                .check();
        }
    }

    #[test]
    fn test_load_dirty_no_name_abort() {
        for answer in NO_ANSWERS {
            Tester::default()
                .add_input_chars("modified unnamed file\n")
                .add_input_chars(answer)
                .write_file("other.bas", "other file\n")
                .run("EDIT: LOAD \"other.bas\"")
                .expect_prints([
                    "Current program has unsaved changes and has never been saved!",
                    "LOAD aborted; use SAVE to save your current changes.",
                ])
                .expect_program(None as Option<&str>, "modified unnamed file\n")
                .expect_file("MEMORY:/other.bas", "other file\n")
                .check();
        }
    }

    #[test]
    fn test_load_dirty_no_name_continue() {
        for answer in YES_ANSWERS {
            Tester::default()
                .add_input_chars("modified unnamed file\n")
                .add_input_chars(answer)
                .write_file("other.bas", "other file\n")
                .run("EDIT: LOAD \"other.bas\"")
                .expect_prints(["Current program has unsaved changes and has never been saved!"])
                .expect_clear()
                .expect_program(Some("MEMORY:other.bas"), "other file\n")
                .expect_file("MEMORY:/other.bas", "other file\n")
                .check();
        }
    }

    #[test]
    fn test_load_dirty_with_name_abort() {
        for answer in NO_ANSWERS {
            Tester::default()
                .add_input_chars("modified named file\n")
                .add_input_chars(answer)
                .write_file("other.bas", "other file\n")
                .set_program(Some("MEMORY:/named.bas"), "previous contents\n")
                .run("EDIT: LOAD \"other.bas\"")
                .expect_prints([
                    "Current program MEMORY:/named.bas has unsaved changes!",
                    "LOAD aborted; use SAVE to save your current changes.",
                ])
                .expect_program(
                    Some("MEMORY:/named.bas"),
                    "previous contents\nmodified named file\n",
                )
                .expect_file("MEMORY:/other.bas", "other file\n")
                .check();
        }
    }

    #[test]
    fn test_load_dirty_with_name_continue() {
        for answer in YES_ANSWERS {
            Tester::default()
                .add_input_chars("modified unnamed file\n")
                .add_input_chars(answer)
                .write_file("other.bas", "other file\n")
                .set_program(Some("MEMORY:/named.bas"), "previous contents\n")
                .run("EDIT: LOAD \"other.bas\"")
                .expect_prints(["Current program MEMORY:/named.bas has unsaved changes!"])
                .expect_clear()
                .expect_program(Some("MEMORY:other.bas"), "other file\n")
                .expect_file("MEMORY:/other.bas", "other file\n")
                .check();
        }
    }

    /// Checks errors that should be handled the same way by `LOAD` and `SAVE`.
    fn check_load_save_common_errors(cmd: &str) {
        Tester::default()
            .run(format!("{} 3", cmd))
            .expect_compilation_err(format!(
                "1:{}: Expected STRING but found INTEGER",
                cmd.len() + 2,
            ))
            .check();

        Tester::default()
            .run(format!(r#"{} "a/b.bas""#, cmd))
            .expect_err("1:1: Too many / separators in path 'a/b.bas'")
            .check();

        Tester::default()
            .run(format!(r#"{} "drive:""#, cmd))
            .expect_err("1:1: Missing file name in path 'drive:'")
            .check();
    }

    #[test]
    fn test_load_errors() {
        check_load_save_common_errors("LOAD");

        Tester::default()
            .run("LOAD")
            .expect_compilation_err("1:1: LOAD expected filename$")
            .check();

        check_stmt_err("1:1: Entry not found", r#"LOAD "missing-file""#);

        Tester::default()
            .write_file("mismatched-extension.bat", "")
            .run(r#"LOAD "mismatched-extension""#)
            .expect_err("1:1: Entry not found")
            .expect_file("MEMORY:/mismatched-extension.bat", "")
            .check();
    }

    #[test]
    fn test_new_nothing() {
        Tester::default().run("NEW").expect_clear().check();
    }

    #[test]
    fn test_new_clears_program_and_variables() {
        Tester::default()
            .set_program(Some("previous.bas"), "some stuff")
            .run("a = 3: NEW")
            .expect_clear()
            .check();
    }

    #[test]
    fn test_new_dirty_no_name_abort() {
        for answer in NO_ANSWERS {
            Tester::default()
                .add_input_chars("modified unnamed file\n")
                .add_input_chars(answer)
                .run("EDIT: NEW")
                .expect_prints([
                    "Current program has unsaved changes and has never been saved!",
                    "NEW aborted; use SAVE to save your current changes.",
                ])
                .expect_program(None as Option<&str>, "modified unnamed file\n")
                .check();
        }
    }

    #[test]
    fn test_new_dirty_no_name_continue() {
        for answer in YES_ANSWERS {
            Tester::default()
                .add_input_chars("modified unnamed file\n")
                .add_input_chars(answer)
                .run("EDIT: NEW")
                .expect_prints(["Current program has unsaved changes and has never been saved!"])
                .expect_clear()
                .check();
        }
    }

    #[test]
    fn test_new_dirty_with_name_abort() {
        for answer in NO_ANSWERS {
            Tester::default()
                .add_input_chars("modified named file\n")
                .add_input_chars(answer)
                .set_program(Some("MEMORY:/named.bas"), "previous contents\n")
                .run("EDIT: NEW")
                .expect_prints([
                    "Current program MEMORY:/named.bas has unsaved changes!",
                    "NEW aborted; use SAVE to save your current changes.",
                ])
                .expect_program(
                    Some("MEMORY:/named.bas"),
                    "previous contents\nmodified named file\n",
                )
                .check();
        }
    }

    #[test]
    fn test_new_dirty_with_name_continue() {
        for answer in YES_ANSWERS {
            Tester::default()
                .add_input_chars("modified named file\n")
                .add_input_chars(answer)
                .set_program(Some("MEMORY:/named.bas"), "previous contents\n")
                .run("EDIT: NEW")
                .expect_prints(["Current program MEMORY:/named.bas has unsaved changes!"])
                .expect_clear()
                .check();
        }
    }

    #[test]
    fn test_new_errors() {
        check_stmt_compilation_err("1:1: NEW expected no arguments", "NEW 10");
    }

    #[test]
    fn test_run_nothing() {
        Tester::default().run("RUN").expect_clear().check();
    }

    #[test]
    fn test_run_clears_before_execution_only() {
        let program = "DIM a(1) AS INTEGER: a(0) = 123";
        let mut t = Tester::default().set_program(Some("untouched.bas"), program);
        t.run("DIM a(1) AS STRING: RUN")
            .expect_array_simple("a", ExprType::Integer, vec![123.into()])
            .expect_clear()
            .expect_program(Some("untouched.bas"), program)
            .check();
        t.run("RUN")
            .expect_array_simple("a", ExprType::Integer, vec![123.into()])
            .expect_clear()
            .expect_clear()
            .expect_program(Some("untouched.bas"), program)
            .check();
    }

    #[test]
    fn test_run_something_that_exits() {
        let program = "PRINT 5: END 1: PRINT 4";
        Tester::default()
            .set_program(Some("untouched.bas"), program)
            .run(r#"RUN"#)
            .expect_clear()
            .expect_prints([" 5", "Program exited with code 1"])
            .expect_program(Some("untouched.bas"), program)
            .check();
    }

    #[test]
    fn test_run_something_that_exits_with_trailing_code() {
        // TODO(jmmv): Versions of EndBASIC before the core rewrite would show the "after"
        // message after an abrupt termination from the program.  core cannot do this because
        // of how the whole line is compiled first and how RUN then replaces the full program
        // memory.  We should fix this at some point.
        let program = "PRINT 5: END 1: PRINT 4";
        Tester::default()
            .set_program(Some("untouched.bas"), program)
            .run(r#"RUN: PRINT "after""#)
            .expect_clear()
            .expect_prints([" 5", "Program exited with code 1"])
            .expect_program(Some("untouched.bas"), program)
            .check();
    }

    #[test]
    fn test_run_after_break_starts_from_beginning() {
        let console = Rc::from(RefCell::from(MockConsole::default()));
        let program = Rc::from(RefCell::from(RecordedProgram::default()));
        program.borrow_mut().load(None, r#"PRINT "begin": SLEEP 0: PRINT "done""#);

        let (signals_tx, signals_rx) = async_channel::unbounded();
        let signal_sent = Rc::from(RefCell::from(false));
        let sleep_tx = signals_tx.clone();
        let sleep_signal_sent = signal_sent.clone();
        let datetime = Rc::from(MockDateTime {
            on_sleep: Box::from(
                move |_d: Duration| -> futures_lite::future::BoxedLocal<Result<(), String>> {
                    let sleep_tx = sleep_tx.clone();
                    let sleep_signal_sent = sleep_signal_sent.clone();
                    async move {
                        if !*sleep_signal_sent.borrow() {
                            *sleep_signal_sent.borrow_mut() = true;
                            sleep_tx.send(Signal::Break).await.unwrap();
                        }
                        Ok(())
                    }
                    .boxed_local()
                },
            ),
        });

        let storage = Rc::from(RefCell::from(Storage::default()));
        let mut machine = MachineBuilder::default()
            .with_console(console.clone())
            .with_signals_chan((signals_tx, signals_rx))
            .with_datetime(datetime)
            .make_interactive()
            .with_program(program)
            .with_storage(storage)
            .build();

        machine.compile(&mut "RUN".as_bytes()).unwrap();
        match block_on(machine.exec()) {
            Err(crate::Error::Break) => (),
            r => panic!("Expected Break but got {:?}", r),
        }

        machine.compile(&mut "RUN".as_bytes()).unwrap();
        match block_on(machine.exec()) {
            Ok(None) => (),
            r => panic!("Expected successful completion but got {:?}", r),
        }

        let prints: Vec<String> = console
            .borrow_mut()
            .take_captured_out()
            .into_iter()
            .filter_map(|out| match out {
                CapturedOut::Print(text) => Some(text),
                _ => None,
            })
            .collect();
        assert_eq!(vec!["begin", "begin", "done"], prints);
    }

    #[test]
    fn test_run_after_async_error_discards_old_program() {
        let program = r#"DIR "invalid:": PRINT "stale""#;
        Tester::default()
            .set_program(None, program)
            .continue_from_here()
            .run("RUN")
            .expect_clear()
            .expect_err("1:1: Drive 'INVALID' is not mounted")
            .expect_program(None as Option<String>, program)
            .check()
            .run(r#"PRINT "ok""#)
            .expect_clear()
            .expect_prints(["ok"])
            .expect_program(None as Option<String>, program)
            .check();
    }

    #[test]
    fn test_run_does_not_leave_error_handler_active() {
        let program = r#"
            ON ERROR GOTO @handler
            END

            @handler
            PRINT "captured: "; ERRMSG
            END 1
        "#;
        Tester::default()
            .set_program(None, program)
            .continue_from_here()
            .run("RUN")
            .expect_clear()
            .expect_program(None as Option<String>, program)
            .check()
            .run(r#"LOAD "missing-file""#)
            .expect_clear()
            .expect_err("1:1: Entry not found")
            .expect_program(None as Option<String>, program)
            .check();
    }

    #[test]
    fn test_run_preserves_errmsg_across_commands() {
        let program = r#"ON ERROR RESUME NEXT: COLOR -1: END"#;
        Tester::default()
            .set_program(None, program)
            .continue_from_here()
            .run("RUN")
            .expect_clear()
            .expect_program(None as Option<String>, program)
            .check()
            .run("result = ERRMSG")
            .expect_clear()
            .expect_var("result", "1:29: Color out of range")
            .expect_program(None as Option<String>, program)
            .check();
    }

    #[test]
    fn test_run_after_break_discards_old_program() {
        let program = r#"PRINT "stale""#;
        Tester::default()
            .set_program(None, program)
            .send_break()
            .continue_from_here()
            .run("RUN")
            .expect_err("Break")
            .expect_program(None as Option<String>, program)
            .check()
            .run(r#"SLEEP 0: PRINT "ok""#)
            .expect_prints(["ok"])
            .expect_program(None as Option<String>, program)
            .check();
    }

    #[test]
    fn test_run_errors() {
        check_stmt_compilation_err("1:1: RUN expected no arguments", "RUN 10");
    }

    #[test]
    fn test_save_ok_explicit_name() {
        let content = "\n some line   \n ";
        for (explicit, actual, canonical) in &[
            ("first", "MEMORY:/first.bas", "MEMORY:first.bas"),
            ("second.bas", "MEMORY:/second.bas", "MEMORY:second.bas"),
            ("THIRD", "MEMORY:/THIRD.BAS", "MEMORY:THIRD.BAS"),
            ("FOURTH.BAS", "MEMORY:/FOURTH.BAS", "MEMORY:FOURTH.BAS"),
            ("Fifth", "MEMORY:/Fifth.bas", "MEMORY:Fifth.bas"),
        ] {
            Tester::default()
                .set_program(Some("before.bas"), content)
                .run(format!(r#"SAVE "{}""#, explicit))
                .expect_program(Some(*canonical), content)
                .expect_prints([format!("Saved as {}", canonical)])
                .expect_file(*actual, content)
                .check();
        }
    }

    #[test]
    fn test_save_reuse_name() {
        Tester::default()
            .set_program(Some("loaded.bas"), "content\n")
            .run("SAVE")
            .expect_program(Some("MEMORY:loaded.bas"), "content\n")
            .expect_prints(["Saved as MEMORY:loaded.bas"])
            .expect_file("MEMORY:/loaded.bas", "content\n")
            .check();
    }

    #[test]
    fn test_save_unnamed_error() {
        Tester::default()
            .add_input_chars("modified file\n")
            .run("EDIT: SAVE")
            .expect_program(None as Option<&str>, "modified file\n")
            .expect_err("1:7: Unnamed program; please provide a filename")
            .check();
    }

    #[test]
    fn test_save_errors() {
        check_load_save_common_errors("SAVE");

        Tester::default()
            .run("SAVE 2, 3")
            .expect_compilation_err("1:1: SAVE expected <> | <filename$>")
            .check();
    }
}
