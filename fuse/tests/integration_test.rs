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

//! Integration tests for the endbasic-fuse binary.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{self, Child};
use std::thread;
use std::time::{Duration, Instant};

const PROD_API_ADDRESS: &str = "https://service.endbasic.dev/";

fn self_dir() -> PathBuf {
    let self_exe = env::current_exe().expect("Cannot get self's executable path");
    let dir = self_exe.parent().expect("Cannot get self's directory");
    assert!(dir.ends_with("target/debug/deps") || dir.ends_with("target/release/deps"));
    dir.to_owned()
}

fn bin_path<P: AsRef<Path>>(name: P) -> PathBuf {
    let test_dir = self_dir();
    let debug_or_release_dir = test_dir.parent().expect("Failed to get parent directory");
    debug_or_release_dir.join(name).with_extension(env::consts::EXE_EXTENSION)
}

fn repo_root() -> PathBuf {
    let test_dir = self_dir();
    let debug_or_release_dir = test_dir.parent().expect("Failed to get parent directory");
    let target_dir = debug_or_release_dir.parent().expect("Failed to get parent directory");
    let dir = target_dir.parent().expect("Failed to get parent directory");
    assert!(dir.join("Cargo.toml").exists());
    dir.to_owned()
}

fn read_passwords() -> (String, String) {
    let content = fs::read_to_string(repo_root().join("passwords.txt"))
        .expect("Failed to read passwords.txt");
    let mut password1 = None;
    let mut password2 = None;
    for line in content.lines() {
        let Some((username, password)) = line.split_once(':') else {
            continue;
        };
        match username.trim() {
            "testuser1" => password1 = Some(password.trim().to_owned()),
            "testuser2" => password2 = Some(password.trim().to_owned()),
            _ => panic!("Unexpected account in passwords.txt"),
        }
    }
    (password1.expect("Missing testuser1 password"), password2.expect("Missing testuser2 password"))
}

fn have_fusermount() -> Option<String> {
    for program in ["fusermount3", "fusermount"] {
        if process::Command::new(program).arg("--version").output().is_ok() {
            return Some(program.to_owned());
        }
    }
    None
}

fn wait_for_mount(mountpoint: &Path) {
    let deadline = Instant::now() + Duration::from_secs(15);
    while Instant::now() < deadline {
        if fs::read_dir(mountpoint).is_ok_and(|mut entries| entries.next().is_some()) {
            return;
        }
        thread::sleep(Duration::from_millis(100));
    }
    panic!("Timed out waiting for mount to become available");
}

struct MountGuard {
    child: Child,
    mountpoint: tempfile::TempDir,
    unmount_program: String,
}

impl Drop for MountGuard {
    fn drop(&mut self) {
        let _ = process::Command::new(&self.unmount_program)
            .arg("-u")
            .arg(self.mountpoint.path())
            .status();
        let _ = self.child.wait();
    }
}

#[cfg(target_os = "linux")]
fn mount_for_user(username: &str, password: &str) -> MountGuard {
    let unmount_program = have_fusermount().expect("Missing fusermount support on this host");
    let mountpoint = tempfile::tempdir().unwrap();
    let child = process::Command::new(bin_path("endbasic-fuse"))
        .args([
            "--service-url",
            PROD_API_ADDRESS,
            "--user",
            username,
            "--password",
            password,
            mountpoint.path().to_str().unwrap(),
        ])
        .spawn()
        .expect("Failed to start endbasic-fuse");
    wait_for_mount(mountpoint.path());
    MountGuard { child, mountpoint, unmount_program }
}

#[test]
fn test_help() {
    let output = process::Command::new(bin_path("endbasic-fuse")).arg("--help").output().unwrap();
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("--user"));
    assert!(stdout.contains("--password"));
    assert!(stdout.contains("mountpoint"));
}

#[cfg(target_os = "linux")]
#[test]
#[ignore = "Requires Linux FUSE support and talks to the public service"]
fn test_mount_and_file_operations() {
    if have_fusermount().is_none() {
        return;
    }
    let (password1, _password2) = read_passwords();
    let guard = mount_for_user("testuser1", &password1);

    let root_entries: Vec<_> = fs::read_dir(guard.mountpoint.path())
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect();
    assert!(root_entries.iter().any(|entry| entry == "testuser1"));

    let filename = format!("fuse-test-{}", process::id());
    let path = guard.mountpoint.path().join("testuser1").join(&filename);
    let content = format!("hello from {}", filename);
    fs::write(&path, &content).unwrap();
    assert_eq!(content, fs::read_to_string(&path).unwrap());
    fs::remove_file(&path).unwrap();
    assert!(!path.exists());
}

#[cfg(target_os = "linux")]
#[test]
#[ignore = "Requires Linux FUSE support and talks to the public service"]
fn test_other_users_are_read_only() {
    if have_fusermount().is_none() {
        return;
    }
    let (password1, _password2) = read_passwords();
    let guard = mount_for_user("testuser1", &password1);

    let root_entries: Vec<_> = fs::read_dir(guard.mountpoint.path())
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect();
    if !root_entries.iter().any(|entry| entry == "testuser2") {
        return;
    }

    let path =
        guard.mountpoint.path().join("testuser2").join(format!("fuse-test-{}", process::id()));
    let err = fs::write(&path, b"denied").unwrap_err();
    assert_eq!(std::io::ErrorKind::PermissionDenied, err.kind());
}
