// EndBASIC
// Copyright 2020 Julio Merino
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

//! Command-line interface for the EndBASIC language.

// Keep these in sync with other top-level files.
#![allow(clippy::await_holding_refcell_ref)]
#![warn(anonymous_parameters, bad_style, missing_docs)]
#![warn(unused, unused_extern_crates, unused_import_braces, unused_qualifications)]
#![warn(unsafe_code)]

use anyhow::{anyhow, Error, Result};
use async_trait::async_trait;
use crossterm::{cursor, event, execute, style, terminal, tty::IsTty, QueueableCommand};
use endbasic_core::console;
use endbasic_core::store::{Metadata, Store};
use futures_lite::future::block_on;
use getopts::Options;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::VecDeque;
use std::env;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process;
use std::rc::Rc;

/// Errors caused by the user when invoking this binary (invalid options or arguments).
#[derive(Debug, thiserror::Error)]
#[error("{message}")]
struct UsageError {
    message: String,
}

impl UsageError {
    /// Creates a new usage error with `message`.
    fn new<T: Into<String>>(message: T) -> Self {
        Self { message: message.into() }
    }
}

/// Flattens all causes of an error into a single string.
fn flatten_causes(err: &Error) -> String {
    err.chain().fold(String::new(), |flattened, cause| {
        let flattened = if flattened.is_empty() { flattened } else { flattened + ": " };
        flattened + &format!("{}", cause)
    })
}

/// Consumes and returns the program name from `env::Args`.
///
/// If the program name cannot be obtained, return `default_name` instead.
fn program_name(mut args: env::Args, default_name: &'static str) -> (String, env::Args) {
    let name = match args.next() {
        Some(arg0) => match Path::new(&arg0).file_stem() {
            Some(basename) => match basename.to_str() {
                Some(s) => s.to_owned(),
                None => default_name.to_owned(),
            },
            None => default_name.to_owned(),
        },
        None => default_name.to_owned(),
    };
    (name, args)
}

//// Converts a `crossterm::ErrorKind` to an `io::Error`.
fn crossterm_error_to_io_error(e: crossterm::ErrorKind) -> io::Error {
    match e {
        crossterm::ErrorKind::IoError(e) => e,
        crossterm::ErrorKind::Utf8Error(e) => {
            io::Error::new(io::ErrorKind::InvalidData, format!("{}", e))
        }
        _ => io::Error::new(io::ErrorKind::Other, format!("{}", e)),
    }
}

/// Gets the value of the environment variable `name` and interprets it as a `usize`.  Returns
/// `None` if the variable is not set or if its contents are invalid.
fn get_env_var_as_usize(name: &str) -> Option<usize> {
    match env::var_os(name) {
        Some(value) => {
            value.as_os_str().to_string_lossy().parse::<usize>().map(Some).unwrap_or(None)
        }
        None => None,
    }
}

/// Implementation of the EndBASIC console to interact with stdin and stdout.
pub struct TextConsole {
    /// Whether stdin and stdout are attached to a TTY.  When this is true, the console is put in
    /// raw mode for finer-grained control.
    is_tty: bool,

    /// Line-oriented buffer to hold input when not operating in raw mode.
    buffer: VecDeque<console::Key>,

    /// Whether a background color is active.  If so, we need to flush the contents of every line
    /// we print so that the color applies to the whole line.
    need_line_flush: bool,
}

impl TextConsole {
    /// Creates a new console based on the properties of stdin/stdout.
    pub fn from_stdio() -> io::Result<Self> {
        let is_tty = io::stdin().is_tty() && io::stdout().is_tty();
        if is_tty {
            terminal::enable_raw_mode().map_err(crossterm_error_to_io_error)?;
        }
        Ok(Self { is_tty, buffer: VecDeque::default(), need_line_flush: false })
    }
}

impl Drop for TextConsole {
    fn drop(&mut self) {
        if self.is_tty {
            terminal::disable_raw_mode().unwrap();
        }
    }
}

impl TextConsole {
    /// Converts a line of text read from stdin into a sequence of key presses.
    fn line_to_keys(s: String) -> VecDeque<console::Key> {
        let mut keys = VecDeque::default();
        for ch in s.chars() {
            if ch == '\x1b' {
                keys.push_back(console::Key::Escape);
            } else if ch == '\n' {
                keys.push_back(console::Key::NewLine);
            } else if ch == '\r' {
                // Ignore.  When we run under Windows and use golden test input files, we end up
                // seeing two separate characters to terminate a newline (CRLF) and these confuse
                // our tests.  I am not sure why this doesn't seem to be a problem for interactive
                // usage though, but it might just be that crossterm hides this from us.
            } else if !ch.is_control() {
                keys.push_back(console::Key::Char(ch));
            } else {
                keys.push_back(console::Key::Unknown(format!("{}", ch)));
            }
        }
        keys
    }

    /// Reads a single key from stdin when not attached to a TTY.  Because characters are not
    /// visible to us until a newline is received, this reads complete lines and buffers them in
    /// memory.
    fn read_key_from_stdin(&mut self) -> io::Result<console::Key> {
        if self.buffer.is_empty() {
            let mut line = String::new();
            if io::stdin().read_line(&mut line)? == 0 {
                return Ok(console::Key::Eof);
            }
            self.buffer = TextConsole::line_to_keys(line);
        }
        match self.buffer.pop_front() {
            Some(key) => Ok(key),
            None => Ok(console::Key::Eof),
        }
    }

    /// Reads a single key from the connected TTY.  This assumes the TTY is in raw mode.
    fn read_key_from_tty(&mut self) -> io::Result<console::Key> {
        loop {
            if let event::Event::Key(ev) = event::read().map_err(crossterm_error_to_io_error)? {
                match ev.code {
                    event::KeyCode::Backspace => return Ok(console::Key::Backspace),
                    event::KeyCode::Esc => return Ok(console::Key::Escape),
                    event::KeyCode::Up => return Ok(console::Key::ArrowUp),
                    event::KeyCode::Down => return Ok(console::Key::ArrowDown),
                    event::KeyCode::Left => return Ok(console::Key::ArrowLeft),
                    event::KeyCode::Right => return Ok(console::Key::ArrowRight),
                    event::KeyCode::Char('c') if ev.modifiers == event::KeyModifiers::CONTROL => {
                        return Ok(console::Key::Interrupt)
                    }
                    event::KeyCode::Char('d') if ev.modifiers == event::KeyModifiers::CONTROL => {
                        return Ok(console::Key::Eof)
                    }
                    event::KeyCode::Char('j') if ev.modifiers == event::KeyModifiers::CONTROL => {
                        return Ok(console::Key::NewLine)
                    }
                    event::KeyCode::Char('m') if ev.modifiers == event::KeyModifiers::CONTROL => {
                        return Ok(console::Key::NewLine)
                    }
                    event::KeyCode::Char(ch) => return Ok(console::Key::Char(ch)),
                    event::KeyCode::Enter => return Ok(console::Key::NewLine),
                    _ => return Ok(console::Key::Unknown(format!("{:?}", ev))),
                }
            }
        }
    }
}

#[async_trait(?Send)]
impl console::Console for TextConsole {
    fn clear(&mut self, how: console::ClearType) -> io::Result<()> {
        let how = match how {
            console::ClearType::All => terminal::ClearType::All,
            console::ClearType::CurrentLine => terminal::ClearType::CurrentLine,
            console::ClearType::UntilNewLine => terminal::ClearType::UntilNewLine,
        };
        let mut output = io::stdout();
        output.queue(terminal::Clear(how)).map_err(crossterm_error_to_io_error)?;
        if how == terminal::ClearType::All {
            output.queue(cursor::MoveTo(0, 0)).map_err(crossterm_error_to_io_error)?;
        }
        output.flush()
    }

    fn color(&mut self, fg: Option<u8>, bg: Option<u8>) -> io::Result<()> {
        let mut output = io::stdout();
        let fg = match fg {
            None => style::Color::Reset,
            Some(color) => style::Color::AnsiValue(color),
        };
        let bg = match bg {
            None => style::Color::Reset,
            Some(color) => style::Color::AnsiValue(color),
        };
        output.queue(style::SetForegroundColor(fg)).map_err(crossterm_error_to_io_error)?;
        output.queue(style::SetBackgroundColor(bg)).map_err(crossterm_error_to_io_error)?;
        output.flush()?;
        self.need_line_flush = bg != style::Color::Reset;
        Ok(())
    }

    fn enter_alt(&mut self) -> io::Result<()> {
        execute!(io::stdout(), terminal::EnterAlternateScreen).map_err(crossterm_error_to_io_error)
    }

    fn hide_cursor(&mut self) -> io::Result<()> {
        execute!(io::stdout(), cursor::Hide).map_err(crossterm_error_to_io_error)
    }

    fn is_interactive(&self) -> bool {
        self.is_tty
    }

    fn leave_alt(&mut self) -> io::Result<()> {
        execute!(io::stdout(), terminal::LeaveAlternateScreen).map_err(crossterm_error_to_io_error)
    }

    fn locate(&mut self, pos: console::Position) -> io::Result<()> {
        if pos.row > std::u16::MAX as usize {
            return Err(io::Error::new(io::ErrorKind::Other, "Row out of range"));
        }
        let row = pos.row as u16;

        if pos.column > std::u16::MAX as usize {
            return Err(io::Error::new(io::ErrorKind::Other, "Column out of range"));
        }
        let column = pos.column as u16;

        execute!(io::stdout(), cursor::MoveTo(column, row)).map_err(crossterm_error_to_io_error)
    }

    fn move_within_line(&mut self, off: i16) -> io::Result<()> {
        match off.cmp(&0) {
            Ordering::Less => execute!(io::stdout(), cursor::MoveLeft(-off as u16)),
            Ordering::Equal => Ok(()),
            Ordering::Greater => execute!(io::stdout(), cursor::MoveRight(off as u16)),
        }
        .map_err(crossterm_error_to_io_error)
    }

    fn print(&mut self, text: &str) -> io::Result<()> {
        let stdout = io::stdout();
        let mut stdout = stdout.lock();
        stdout.write_all(text.as_bytes())?;
        if self.need_line_flush {
            execute!(stdout, terminal::Clear(terminal::ClearType::UntilNewLine))
                .map_err(crossterm_error_to_io_error)?;
        }
        if self.is_tty {
            stdout.write_all(b"\r\n")?;
        } else {
            stdout.write_all(b"\n")?;
        }
        Ok(())
    }

    async fn read_key(&mut self) -> io::Result<console::Key> {
        if self.is_tty {
            self.read_key_from_tty()
        } else {
            self.read_key_from_stdin()
        }
    }

    fn show_cursor(&mut self) -> io::Result<()> {
        execute!(io::stdout(), cursor::Show).map_err(crossterm_error_to_io_error)
    }

    fn size(&self) -> io::Result<console::Position> {
        // Must be careful to not query the terminal size if both LINES and COLUMNS are set, because
        // the query fails when we don't have a PTY and we still need to run under these conditions
        // for testing purposes.
        let lines = get_env_var_as_usize("LINES");
        let columns = get_env_var_as_usize("COLUMNS");
        let size = match (lines, columns) {
            (Some(l), Some(c)) => console::Position { row: l, column: c },
            (l, c) => {
                let (actual_columns, actual_lines) =
                    terminal::size().map_err(crossterm_error_to_io_error)?;
                console::Position {
                    row: l.unwrap_or(actual_lines as usize),
                    column: c.unwrap_or(actual_columns as usize),
                }
            }
        };
        Ok(size)
    }

    fn write(&mut self, bytes: &[u8]) -> io::Result<()> {
        let stdout = io::stdout();
        let mut stdout = stdout.lock();
        stdout.write_all(bytes)?;
        stdout.flush()
    }
}

/// An implementation of `Store` backed by an on-disk directory.
pub struct FileStore {
    /// Path to the directory containing all entries backed by this `Store`.  The directory may
    /// contain files that are not EndBASIC programs, and that's OK, but those files will not be
    /// accessible through this interface.
    dir: PathBuf,
}

impl FileStore {
    /// Creates a new store backed by the `dir` directory.
    pub fn new<P: Into<PathBuf>>(dir: P) -> Self {
        Self { dir: dir.into() }
    }
}

impl Store for FileStore {
    fn delete(&mut self, name: &str) -> io::Result<()> {
        let path = self.dir.join(name);
        fs::remove_file(path)
    }

    fn enumerate(&self) -> io::Result<BTreeMap<String, Metadata>> {
        let mut entries = BTreeMap::default();
        match fs::read_dir(&self.dir) {
            Ok(dirents) => {
                for de in dirents {
                    let de = de?;

                    let file_type = de.file_type()?;
                    if !file_type.is_file() && !file_type.is_symlink() {
                        // Silently ignore entries we cannot handle.
                        continue;
                    }

                    // This follows symlinks for cross-platform simplicity, but it is ugly.  I don't
                    // expect symlinks in the programs directory anyway.  If we want to handle this
                    // better, we'll have to add a way to report file types.
                    let metadata = fs::metadata(de.path())?;
                    let offset = match time::UtcOffset::try_current_local_offset() {
                        Ok(offset) => offset,
                        Err(_) => time::UtcOffset::UTC,
                    };
                    let date = time::OffsetDateTime::from(metadata.modified()?).to_offset(offset);
                    let length = metadata.len();

                    entries.insert(
                        de.file_name().to_string_lossy().to_string(),
                        Metadata { date, length },
                    );
                }
            }
            Err(e) => {
                if e.kind() != io::ErrorKind::NotFound {
                    return Err(e);
                }
            }
        }
        Ok(entries)
    }

    fn get(&self, name: &str) -> io::Result<String> {
        let path = self.dir.join(name);
        let input = File::open(&path)?;
        let mut content = String::new();
        io::BufReader::new(input).read_to_string(&mut content)?;
        Ok(content)
    }

    fn put(&mut self, name: &str, content: &str) -> io::Result<()> {
        let path = self.dir.join(name);
        let dir = path.parent().expect("Must be a filename with a directory");
        fs::create_dir_all(&dir)?;

        // TODO(jmmv): Should back up existing files.
        let output = OpenOptions::new().create(true).write(true).truncate(true).open(path)?;
        let mut writer = io::BufWriter::new(output);
        writer.write_all(content.as_bytes())
    }
}

/// Prints usage information for program `name` with `opts` following the GNU Standards format.
fn help(name: &str, opts: &Options) -> Result<i32> {
    let brief = format!("Usage: {} [options] [program-file]", name);
    println!("{}", opts.usage(&brief));
    println!("Report bugs to: https://github.com/jmmv/endbasic/issues");
    println!("EndBASIC home page: https://github.com/jmmv/endbasic");
    Ok(0)
}

/// Prints version information following the GNU Standards format.
fn version() -> Result<i32> {
    println!("EndBASIC {}", env!("CARGO_PKG_VERSION"));
    println!("Copyright 2020-2021 Julio Merino");
    println!("License Apache Version 2.0 <http://www.apache.org/licenses/LICENSE-2.0>");
    Ok(0)
}

/// Computes the path to the directory where user programs live if `flag` is none; otherwise
/// just returns `flag`.
fn get_programs_dir(flag: Option<String>) -> Result<PathBuf> {
    let dir = flag.map(PathBuf::from).or_else(|| {
        dirs::document_dir().map(|d| d.join("endbasic")).or_else(|| {
            // On Linux, dirs::document_dir() seems to return None whenever user-dirs.dirs is
            // not present... which is suboptimal.  Compute a reasonable default based on the
            // home directory.
            dirs::home_dir().map(|h| h.join("Documents/endbasic"))
        })
    });

    // Instead of aborting on a missing programs directory, we could disable the LOAD/SAVE commands
    // when we cannot compute this folder, but that seems like hiding a corner case that is unlikely
    // to surface.  A good reason to do this, however, would be to allow the user to explicitly
    // disable this functionality to keep the interpreter from touching the disk.
    if dir.is_none() {
        return Err(anyhow!("Cannot compute default path to the Documents folder"));
    }
    Ok(dir.unwrap())
}

/// Creates a new store backed by `dir` and overlays the built-in demos.
fn new_store_with_demos(dir: &Path) -> Rc<RefCell<dyn Store>> {
    if dir == Path::new(":memory:") {
        Rc::from(RefCell::from(endbasic::demos::DemoStoreOverlay::new(
            endbasic_core::store::InMemoryStore::default(),
        )))
    } else {
        Rc::from(RefCell::from(endbasic::demos::DemoStoreOverlay::new(FileStore::new(dir))))
    }
}

/// Enters the interactive interpreter.
///
/// `dir` specifies the directory that the interpreter will use for any commands that manipulate
/// files.  The special name `:memory:` makes the interpreter use an in-memory only store.
fn run_repl_loop(dir: &Path) -> io::Result<i32> {
    let console = Rc::from(RefCell::from(TextConsole::from_stdio()?));
    block_on(endbasic::run_repl_loop(console, new_store_with_demos(dir)))
}

/// Executes the `path` program in a fresh machine.
fn run_script<P: AsRef<Path>>(path: P) -> endbasic_core::exec::Result<i32> {
    let console = Rc::from(RefCell::from(TextConsole::from_stdio()?));
    let mut machine = endbasic_core::scripting_machine_builder(console).build();
    let mut input = File::open(path)?;
    Ok(block_on(machine.exec(&mut input))?.as_exit_code())
}

/// Executes the `path` program in a fresh machine allowing any interactive-only calls.
///
/// `dir` has the same meaning as the parameter passed to `run_repl_loop`.
fn run_interactive<P: AsRef<Path>>(path: P, dir: &Path) -> endbasic_core::exec::Result<i32> {
    let console = Rc::from(RefCell::from(TextConsole::from_stdio()?));
    let mut machine =
        endbasic_core::interactive_machine_builder(console, new_store_with_demos(dir)).build();
    let mut input = File::open(path)?;
    Ok(block_on(machine.exec(&mut input))?.as_exit_code())
}

/// Version of `main` that returns errors to the caller for reporting.
fn safe_main(name: &str, args: env::Args) -> Result<i32> {
    let args: Vec<String> = args.collect();

    let mut opts = Options::new();
    opts.optflag("h", "help", "show command-line usage information and exit");
    opts.optflag("i", "interactive", "force interactive mode when running a script");
    opts.optopt("", "programs-dir", "directory where user programs are stored", "PATH");
    opts.optflag("", "version", "show version information and exit");
    let matches = opts.parse(args)?;

    if matches.opt_present("help") {
        return help(name, &opts);
    }

    if matches.opt_present("version") {
        return version();
    }

    match matches.free.as_slice() {
        [] => {
            let programs_dir = get_programs_dir(matches.opt_str("programs-dir"))?;
            Ok(run_repl_loop(&programs_dir)?)
        }
        [file] => {
            if matches.opt_present("interactive") {
                let programs_dir = get_programs_dir(matches.opt_str("programs-dir"))?;
                Ok(run_interactive(file, &programs_dir)?)
            } else {
                Ok(run_script(file)?)
            }
        }
        [_, ..] => Err(UsageError::new("Too many arguments").into()),
    }
}

fn main() {
    let (name, args) = program_name(env::args(), "endbasic");
    match safe_main(&name, args) {
        Ok(code) => process::exit(code),
        Err(e) => {
            if let Some(e) = e.downcast_ref::<UsageError>() {
                eprintln!("Usage error: {}", e);
                eprintln!("Type {} --help for more information", name);
                process::exit(2);
            } else if let Some(e) = e.downcast_ref::<getopts::Fail>() {
                eprintln!("Usage error: {}", e);
                eprintln!("Type {} --help for more information", name);
                process::exit(2);
            } else {
                eprintln!("{}: {}", name, flatten_causes(&e));
                process::exit(1);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use endbasic_core::store::Metadata;
    use std::io::BufRead;
    use std::path::Path;

    #[test]
    fn flatten_causes_one() {
        assert_eq!("the error", flatten_causes(&anyhow!("the error")));
    }

    #[test]
    fn flatten_causes_several() {
        let err = anyhow!("first").context("second").context("and last");
        assert_eq!("and last: second: first", flatten_causes(&err));
    }

    /// Reads `path` and checks that its contents match `exp_lines`.
    fn check_file(path: &Path, exp_lines: &[&str]) {
        let file = File::open(path).unwrap();
        let reader = io::BufReader::new(file);
        let mut lines = vec![];
        for line in reader.lines() {
            lines.push(line.unwrap());
        }
        assert_eq!(exp_lines, lines.as_slice());
    }

    /// Creates `path` with the contents in `lines` and with a deterministic modification time.
    fn write_file(path: &Path, lines: &[&str]) {
        let mut file = fs::OpenOptions::new()
            .create(true)
            .truncate(false) // Should not be creating the same file more than once.
            .write(true)
            .open(path)
            .unwrap();
        for line in lines {
            file.write_fmt(format_args!("{}\n", line)).unwrap();
        }
        drop(file);

        filetime::set_file_mtime(path, filetime::FileTime::from_unix_time(1_588_757_875, 0))
            .unwrap();
    }

    #[test]
    fn test_delete_ok() {
        let dir = tempfile::tempdir().unwrap();
        write_file(&dir.path().join("a.bas"), &[]);
        write_file(&dir.path().join("a.bat"), &[]);

        let mut store = FileStore::new(&dir.path());
        store.delete("a.bas").unwrap();
        assert!(!dir.path().join("a.bas").exists());
        assert!(dir.path().join("a.bat").exists());
    }

    #[test]
    fn test_delete_missing_file() {
        let dir = tempfile::tempdir().unwrap();

        // TODO(jmmv): This is very ugly... need better error reporting in general, not just for
        // this one case.
        let enoent_message = if cfg!(target_os = "windows") {
            "The system cannot find the file specified. (os error 2)"
        } else {
            "No such file or directory (os error 2)"
        };

        let mut store = FileStore::new(&dir.path());
        assert_eq!(enoent_message, format!("{}", store.delete("a.bas").unwrap_err()));
    }

    #[test]
    fn test_enumerate_nothing() {
        let dir = tempfile::tempdir().unwrap();

        let store = FileStore::new(&dir.path());
        assert!(store.enumerate().unwrap().is_empty());
    }

    #[test]
    fn test_enumerate_some_files() {
        let dir = tempfile::tempdir().unwrap();
        write_file(&dir.path().join("empty.bas"), &[]);
        write_file(&dir.path().join("some file.bas"), &["this is not empty"]);

        let store = FileStore::new(&dir.path());
        let entries = store.enumerate().unwrap();
        assert_eq!(2, entries.len());
        let date = time::OffsetDateTime::from_unix_timestamp(1_588_757_875);
        assert_eq!(&Metadata { date, length: 0 }, entries.get("empty.bas").unwrap());
        assert_eq!(&Metadata { date, length: 18 }, entries.get("some file.bas").unwrap());
    }

    #[test]
    fn test_enumerate_treats_missing_dir_as_empty() {
        let dir = tempfile::tempdir().unwrap();
        let store = FileStore::new(dir.path().join("does-not-exist"));
        assert!(store.enumerate().unwrap().is_empty());
    }

    #[test]
    fn test_enumerate_ignores_non_files() {
        let dir = tempfile::tempdir().unwrap();
        fs::create_dir(dir.path().join("will-be-ignored")).unwrap();
        let store = FileStore::new(&dir.path());
        assert!(store.enumerate().unwrap().is_empty());
    }

    #[cfg(not(target_os = "windows"))]
    #[test]
    fn test_enumerate_follows_symlinks() {
        use std::os::unix::fs as unix_fs;

        let dir = tempfile::tempdir().unwrap();
        write_file(&dir.path().join("some file.bas"), &["this is not empty"]);
        unix_fs::symlink(&Path::new("some file.bas"), &dir.path().join("a link.bas")).unwrap();

        let store = FileStore::new(&dir.path());
        let entries = store.enumerate().unwrap();
        assert_eq!(2, entries.len());
        let metadata =
            Metadata { date: time::OffsetDateTime::from_unix_timestamp(1_588_757_875), length: 18 };
        assert_eq!(&metadata, entries.get("some file.bas").unwrap());
        assert_eq!(&metadata, entries.get("a link.bas").unwrap());
    }

    #[test]
    fn test_enumerate_fails_on_non_directory() {
        let dir = tempfile::tempdir().unwrap();

        // TODO(jmmv): This is very ugly... need better error reporting in general, not just for
        // this one case.
        let enotdir_message = if cfg!(target_os = "windows") {
            "The directory name is invalid. (os error 267)"
        } else {
            "Not a directory (os error 20)"
        };

        let file = dir.path().join("not-a-dir");
        write_file(&file, &[]);
        let store = FileStore::new(&file);
        assert_eq!(enotdir_message, format!("{}", store.enumerate().unwrap_err()));
    }

    #[test]
    fn test_get() {
        let dir = tempfile::tempdir().unwrap();
        write_file(&dir.path().join("some file.bas"), &["one line", "two lines"]);

        let store = FileStore::new(&dir.path());
        assert_eq!("one line\ntwo lines\n", store.get("some file.bas").unwrap());
    }

    #[test]
    fn test_put() {
        let dir = tempfile::tempdir().unwrap();

        let mut store = FileStore::new(&dir.path());
        store.put("some file.bas", "a b c\nd e\n").unwrap();
        check_file(&dir.path().join("some file.bas"), &["a b c", "d e"]);
    }
}
