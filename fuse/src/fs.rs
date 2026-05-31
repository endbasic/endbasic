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

//! FUSE filesystem implementation for the EndBASIC cloud service.

use anyhow::Result;
use endbasic_client::{CloudService, FileEntry, Service};
use fuser::{
    FileAttr, FileType, Filesystem, MountOption, ReplyAttr, ReplyCreate, ReplyData, ReplyDirectory,
    ReplyEmpty, ReplyEntry, ReplyOpen, ReplyWrite, Request,
};
use libc::{EACCES, EINVAL, EIO, ENOENT, ENOSYS};
use std::collections::HashMap;
use std::ffi::OsStr;
use std::os::unix::fs::MetadataExt;
use std::time::{Duration, SystemTime};

const BLOCK_SIZE: u32 = 4096;
const ROOT_INODE: u64 = 1;
const TTL: Duration = Duration::from_secs(1);

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum NodeKey {
    File { user: String, name: String },
    Root,
    UserDir(String),
}

#[derive(Clone, Debug)]
enum Node {
    File(FileNode),
    Root,
    UserDir(UserDirNode),
}

#[derive(Clone, Debug)]
struct FileNode {
    filename: String,
    length: u64,
    mtime: SystemTime,
    user: String,
}

#[derive(Clone, Debug)]
struct UserDirNode {
    username: String,
}

#[derive(Debug)]
struct OpenFile {
    dirty: bool,
    inode: u64,
    content: Vec<u8>,
    loaded: bool,
}

#[derive(Debug)]
pub(crate) struct EndbasicFs {
    gid: u32,
    mounted_at: SystemTime,
    next_file_handle: u64,
    next_inode: u64,
    nodes: HashMap<u64, Node>,
    nodes_by_key: HashMap<NodeKey, u64>,
    open_files: HashMap<u64, OpenFile>,
    rt: tokio::runtime::Runtime,
    service: CloudService,
    uid: u32,
    writable_user: String,
}

impl EndbasicFs {
    fn new(rt: tokio::runtime::Runtime, service: CloudService, writable_user: String) -> Self {
        let metadata =
            std::fs::metadata(".").expect("Current directory metadata must be accessible");
        let mut nodes = HashMap::new();
        nodes.insert(ROOT_INODE, Node::Root);

        let mut nodes_by_key = HashMap::new();
        nodes_by_key.insert(NodeKey::Root, ROOT_INODE);

        Self {
            gid: metadata.gid(),
            mounted_at: SystemTime::now(),
            next_file_handle: 1,
            next_inode: ROOT_INODE + 1,
            nodes,
            nodes_by_key,
            open_files: HashMap::new(),
            rt,
            service,
            uid: metadata.uid(),
            writable_user,
        }
    }

    fn alloc_handle(&mut self, inode: u64, content: Vec<u8>, dirty: bool, loaded: bool) -> u64 {
        let fh = self.next_file_handle;
        self.next_file_handle += 1;
        self.open_files.insert(fh, OpenFile { dirty, inode, content, loaded });
        fh
    }

    fn ensure_file_inode(&mut self, user: &str, file: &FileEntry) -> u64 {
        let key = NodeKey::File { user: user.to_owned(), name: file.filename.clone() };
        if let Some(inode) = self.nodes_by_key.get(&key) {
            self.nodes.insert(
                *inode,
                Node::File(FileNode {
                    filename: file.filename.clone(),
                    length: file.length,
                    mtime: file.mtime,
                    user: user.to_owned(),
                }),
            );
            *inode
        } else {
            let inode = self.next_inode;
            self.next_inode += 1;
            self.nodes.insert(
                inode,
                Node::File(FileNode {
                    filename: file.filename.clone(),
                    length: file.length,
                    mtime: file.mtime,
                    user: user.to_owned(),
                }),
            );
            self.nodes_by_key.insert(key, inode);
            inode
        }
    }

    fn ensure_user_inode(&mut self, username: &str) -> u64 {
        let key = NodeKey::UserDir(username.to_owned());
        if let Some(inode) = self.nodes_by_key.get(&key) {
            *inode
        } else {
            let inode = self.next_inode;
            self.next_inode += 1;
            self.nodes.insert(inode, Node::UserDir(UserDirNode { username: username.to_owned() }));
            self.nodes_by_key.insert(key, inode);
            inode
        }
    }

    fn file_attr(&self, inode: u64, file: &FileNode) -> FileAttr {
        let writable = file.user == self.writable_user;
        FileAttr {
            atime: file.mtime,
            blksize: BLOCK_SIZE,
            blocks: file.length.div_ceil(BLOCK_SIZE as u64),
            crtime: file.mtime,
            ctime: file.mtime,
            flags: 0,
            gid: self.gid,
            ino: inode,
            kind: FileType::RegularFile,
            mtime: file.mtime,
            nlink: 1,
            perm: if writable { 0o644 } else { 0o444 },
            rdev: 0,
            size: file.length,
            uid: self.uid,
        }
    }

    fn get_attr(&mut self, inode: u64) -> Result<FileAttr, i32> {
        let node = self.nodes.get(&inode).cloned().ok_or(ENOENT)?;
        Ok(match node {
            Node::File(file) => self.file_attr(inode, &file),
            Node::Root => self.synthetic_dir_attr(inode, false),
            Node::UserDir(user) => {
                self.synthetic_dir_attr(inode, user.username == self.writable_user)
            }
        })
    }

    fn is_writable_path(&self, user: &str) -> bool {
        user == self.writable_user
    }

    fn list_root(&mut self) -> Result<Vec<(u64, FileType, String)>, i32> {
        let mut users = self.rt.block_on(self.service.list_users()).map_err(errno_from_io_error)?;
        if !users.iter().any(|user| user == &self.writable_user) {
            users.push(self.writable_user.clone());
        }
        users.sort();
        users.retain(|user| is_valid_name(user));
        users.dedup();

        let mut entries = vec![(ROOT_INODE, FileType::Directory, ".".to_owned())];
        entries.push((ROOT_INODE, FileType::Directory, "..".to_owned()));
        for user in users {
            let inode = self.ensure_user_inode(&user);
            entries.push((inode, FileType::Directory, user));
        }
        Ok(entries)
    }

    fn list_user_dir(
        &mut self,
        user: &str,
        inode: u64,
    ) -> Result<Vec<(u64, FileType, String)>, i32> {
        let mut entries = vec![(inode, FileType::Directory, ".".to_owned())];
        entries.push((ROOT_INODE, FileType::Directory, "..".to_owned()));

        let mut files: Vec<FileEntry> = self.rt.block_on(self.service.get_files(user))
            .map_err(errno_from_io_error)?
            .into_files();
        files.sort_by(|lhs, rhs| lhs.filename.cmp(&rhs.filename));
        files.retain(|file| is_valid_name(&file.filename));
        for file in files {
            let file_inode = self.ensure_file_inode(user, &file);
            entries.push((file_inode, FileType::RegularFile, file.filename));
        }
        Ok(entries)
    }

    fn lookup_file(&mut self, user: &str, name: &str) -> Result<(u64, FileAttr), i32> {
        for file in self.rt.block_on(self.service.get_files(user))
            .map_err(errno_from_io_error)?
            .into_files()
        {
            if file.filename == name {
                let inode = self.ensure_file_inode(user, &file);
                return Ok((inode, self.file_attr(inode, self.expect_file(inode)?)));
            }
        }
        Err(ENOENT)
    }

    fn open_file(&mut self, inode: u64, flags: i32) -> Result<u64, i32> {
        let file = self.expect_file(inode)?.clone();
        let wants_write = flags & libc::O_ACCMODE != libc::O_RDONLY;
        if wants_write && !self.is_writable_path(&file.user) {
            return Err(EACCES);
        }

        let truncated = flags & libc::O_TRUNC != 0;
        let content = if wants_write {
            if truncated {
                vec![]
            } else {
                self.rt.block_on(self.service.get_file(&file.user, &file.filename)).map_err(errno_from_io_error)?
            }
        } else {
            vec![]
        };
        Ok(self.alloc_handle(inode, content, truncated, wants_write))
    }

    fn flush_handle(&mut self, ino: u64, fh: u64) -> Result<(), i32> {
        let file = match self.nodes.get(&ino).cloned() {
            Some(Node::File(file)) => file,
            _ => return Err(ENOENT),
        };

        let (dirty, content) = match self.open_files.get(&fh) {
            Some(open_file) => (open_file.dirty, open_file.content.clone()),
            None => return Ok(()),
        };
        if !dirty {
            return Ok(());
        }

        self.rt.block_on(self.service.patch_file_content(&file.user, &file.filename, content.clone()))
            .map_err(errno_from_io_error)?;
        self.update_file_metadata(ino, content.len() as u64)?;

        if let Some(open_file) = self.open_files.get_mut(&fh) {
            open_file.dirty = false;
        }
        Ok(())
    }

    fn reply_readdir(&mut self, ino: u64, offset: i64, mut reply: ReplyDirectory) {
        let entries = match self.nodes.get(&ino).cloned() {
            Some(Node::Root) => self.list_root(),
            Some(Node::UserDir(user)) => self.list_user_dir(&user.username, ino),
            Some(Node::File(_)) => Err(ENOENT),
            None => Err(ENOENT),
        };

        let entries = match entries {
            Ok(entries) => entries,
            Err(errno) => {
                reply.error(errno);
                return;
            }
        };

        for (index, (entry_ino, kind, name)) in
            entries.into_iter().enumerate().skip(offset as usize)
        {
            if reply.add(entry_ino, (index + 1) as i64, kind, name) {
                break;
            }
        }
        reply.ok();
    }

    fn slice_content(content: &[u8], offset: i64, size: u32) -> &[u8] {
        let start = offset.max(0) as usize;
        if start >= content.len() {
            return &[];
        }
        let end = content.len().min(start + size as usize);
        &content[start..end]
    }

    fn synthetic_dir_attr(&self, inode: u64, writable: bool) -> FileAttr {
        FileAttr {
            atime: self.mounted_at,
            blksize: BLOCK_SIZE,
            blocks: 1,
            crtime: self.mounted_at,
            ctime: self.mounted_at,
            flags: 0,
            gid: self.gid,
            ino: inode,
            kind: FileType::Directory,
            mtime: self.mounted_at,
            nlink: 2,
            perm: if writable { 0o755 } else { 0o555 },
            rdev: 0,
            size: 0,
            uid: self.uid,
        }
    }

    fn update_file_metadata(&mut self, inode: u64, length: u64) -> Result<(), i32> {
        let file = self.expect_file_mut(inode)?;
        file.length = length;
        file.mtime = SystemTime::now();
        Ok(())
    }

    fn expect_file(&self, inode: u64) -> Result<&FileNode, i32> {
        match self.nodes.get(&inode) {
            Some(Node::File(file)) => Ok(file),
            _ => Err(ENOENT),
        }
    }

    fn expect_file_mut(&mut self, inode: u64) -> Result<&mut FileNode, i32> {
        match self.nodes.get_mut(&inode) {
            Some(Node::File(file)) => Ok(file),
            _ => Err(ENOENT),
        }
    }
}

impl Filesystem for EndbasicFs {
    fn create(
        &mut self,
        _req: &Request<'_>,
        parent: u64,
        name: &OsStr,
        mode: u32,
        _umask: u32,
        flags: i32,
        reply: ReplyCreate,
    ) {
        let Some(name) = name.to_str() else {
            reply.error(EINVAL);
            return;
        };
        if !is_valid_name(name) {
            reply.error(EINVAL);
            return;
        }

        let user = match self.nodes.get(&parent) {
            Some(Node::UserDir(user)) => user.username.clone(),
            _ => {
                reply.error(ENOENT);
                return;
            }
        };
        if !self.is_writable_path(&user) {
            reply.error(EACCES);
            return;
        }

        let file = FileEntry { filename: name.to_owned(), length: 0, mtime: SystemTime::now() };
        let inode = self.ensure_file_inode(&user, &file);
        let fh = self.alloc_handle(inode, vec![], true, true);
        let attr = self.file_attr(inode, self.expect_file(inode).expect("New node must exist"));
        let _ = mode;
        reply.created(&TTL, &attr, 0, fh, flags as u32);
    }

    fn flush(
        &mut self,
        _req: &Request<'_>,
        ino: u64,
        fh: u64,
        _lock_owner: u64,
        reply: ReplyEmpty,
    ) {
        match self.flush_handle(ino, fh) {
            Ok(()) => reply.ok(),
            Err(errno) => reply.error(errno),
        }
    }

    fn getattr(&mut self, _req: &Request<'_>, ino: u64, reply: ReplyAttr) {
        match self.get_attr(ino) {
            Ok(attr) => reply.attr(&TTL, &attr),
            Err(errno) => reply.error(errno),
        }
    }

    fn lookup(&mut self, _req: &Request<'_>, parent: u64, name: &OsStr, reply: ReplyEntry) {
        let Some(name) = name.to_str() else {
            reply.error(EINVAL);
            return;
        };

        let result = match self.nodes.get(&parent).cloned() {
            Some(Node::Root) => {
                if !is_valid_name(name) {
                    Err(ENOENT)
                } else {
                    match self.rt.block_on(self.service.list_users()).map_err(errno_from_io_error) {
                        Ok(mut users) => {
                            if !users.iter().any(|user| user == &self.writable_user) {
                                users.push(self.writable_user.clone());
                            }
                            if users.iter().any(|user| user == name) {
                                let inode = self.ensure_user_inode(name);
                                Ok(self.synthetic_dir_attr(inode, self.is_writable_path(name)))
                            } else {
                                Err(ENOENT)
                            }
                        }
                        Err(errno) => Err(errno),
                    }
                }
            }
            Some(Node::UserDir(user)) => {
                self.lookup_file(&user.username, name).map(|(_, attr)| attr)
            }
            _ => Err(ENOENT),
        };

        match result {
            Ok(attr) => reply.entry(&TTL, &attr, 0),
            Err(errno) => reply.error(errno),
        }
    }

    fn open(&mut self, _req: &Request<'_>, ino: u64, flags: i32, reply: ReplyOpen) {
        match self.open_file(ino, flags) {
            Ok(fh) => reply.opened(fh, flags as u32),
            Err(errno) => reply.error(errno),
        }
    }

    fn read(
        &mut self,
        _req: &Request<'_>,
        ino: u64,
        fh: u64,
        offset: i64,
        size: u32,
        _flags: i32,
        _lock_owner: Option<u64>,
        reply: ReplyData,
    ) {
        let file = match self.nodes.get(&ino).cloned() {
            Some(Node::File(file)) => file,
            _ => {
                reply.error(ENOENT);
                return;
            }
        };

        let content = if let Some(open_file) = self.open_files.get(&fh) {
            debug_assert_eq!(open_file.inode, ino);
            if open_file.loaded {
                open_file.content.clone()
            } else {
                match self.rt.block_on(self.service.get_file(&file.user, &file.filename)) {
                    Ok(content) => content,
                    Err(e) => {
                        reply.error(errno_from_io_error(e));
                        return;
                    }
                }
            }
        } else {
            match self.rt.block_on(self.service.get_file(&file.user, &file.filename)) {
                Ok(content) => content,
                Err(e) => {
                    reply.error(errno_from_io_error(e));
                    return;
                }
            }
        };
        reply.data(Self::slice_content(&content, offset, size));
    }

    fn readdir(
        &mut self,
        _req: &Request<'_>,
        ino: u64,
        _fh: u64,
        offset: i64,
        reply: ReplyDirectory,
    ) {
        self.reply_readdir(ino, offset, reply);
    }

    fn release(
        &mut self,
        _req: &Request<'_>,
        ino: u64,
        fh: u64,
        _flags: i32,
        _lock_owner: Option<u64>,
        flush: bool,
        reply: ReplyEmpty,
    ) {
        if flush && let Err(errno) = self.flush_handle(ino, fh) {
            reply.error(errno);
            return;
        }
        self.open_files.remove(&fh);
        reply.ok();
    }

    fn setattr(
        &mut self,
        _req: &Request<'_>,
        ino: u64,
        _mode: Option<u32>,
        _uid: Option<u32>,
        _gid: Option<u32>,
        size: Option<u64>,
        _atime: Option<fuser::TimeOrNow>,
        _mtime: Option<fuser::TimeOrNow>,
        _ctime: Option<SystemTime>,
        fh: Option<u64>,
        _crtime: Option<SystemTime>,
        _chgtime: Option<SystemTime>,
        _bkuptime: Option<SystemTime>,
        _flags: Option<u32>,
        reply: ReplyAttr,
    ) {
        let Some(size) = size else {
            match self.get_attr(ino) {
                Ok(attr) => reply.attr(&TTL, &attr),
                Err(errno) => reply.error(errno),
            }
            return;
        };
        let Some(fh) = fh else {
            reply.error(ENOSYS);
            return;
        };
        let Some(open_file) = self.open_files.get_mut(&fh) else {
            reply.error(EIO);
            return;
        };
        open_file.content.resize(size as usize, 0);
        open_file.dirty = true;
        open_file.loaded = true;

        if let Err(errno) = self.update_file_metadata(ino, size) {
            reply.error(errno);
            return;
        }
        match self.get_attr(ino) {
            Ok(attr) => reply.attr(&TTL, &attr),
            Err(errno) => reply.error(errno),
        }
    }

    fn unlink(&mut self, _req: &Request<'_>, parent: u64, name: &OsStr, reply: ReplyEmpty) {
        let Some(name) = name.to_str() else {
            reply.error(EINVAL);
            return;
        };
        let user = match self.nodes.get(&parent).cloned() {
            Some(Node::UserDir(user)) => user.username,
            _ => {
                reply.error(ENOENT);
                return;
            }
        };
        if !self.is_writable_path(&user) {
            reply.error(EACCES);
            return;
        }
        match self.rt.block_on(self.service.delete_file(&user, name)).map_err(errno_from_io_error) {
            Ok(()) => {
                let key = NodeKey::File { user, name: name.to_owned() };
                if let Some(inode) = self.nodes_by_key.remove(&key) {
                    self.nodes.remove(&inode);
                }
                reply.ok();
            }
            Err(errno) => reply.error(errno),
        }
    }

    fn write(
        &mut self,
        _req: &Request<'_>,
        ino: u64,
        fh: u64,
        offset: i64,
        data: &[u8],
        _write_flags: u32,
        _flags: i32,
        _lock_owner: Option<u64>,
        reply: ReplyWrite,
    ) {
        if offset < 0 {
            reply.error(EINVAL);
            return;
        }
        let Some(open_file) = self.open_files.get_mut(&fh) else {
            reply.error(EIO);
            return;
        };
        let start = offset as usize;
        if open_file.content.len() < start {
            open_file.content.resize(start, 0);
        }
        let end = start + data.len();
        if open_file.content.len() < end {
            open_file.content.resize(end, 0);
        }
        open_file.content[start..end].copy_from_slice(data);
        open_file.dirty = true;
        open_file.loaded = true;
        let new_len = open_file.content.len() as u64;
        if let Err(errno) = self.update_file_metadata(ino, new_len) {
            reply.error(errno);
            return;
        }
        reply.written(data.len() as u32);
    }
}

pub(crate) fn mount(
    service_url: String,
    username: String,
    password: String,
    mountpoint: &str,
) -> Result<()> {
    let rt = tokio::runtime::Builder::new_current_thread().build()?;
    let mut service = CloudService::new(&service_url)?;
    rt.block_on(service.login(&username, &password))?;
    let fs = EndbasicFs::new(rt, service, username);
    let options = vec![MountOption::FSName("endbasic".to_owned()), MountOption::DefaultPermissions];
    fuser::mount2(fs, mountpoint, &options)?;
    Ok(())
}

fn errno_from_io_error(e: std::io::Error) -> i32 {
    match e.kind() {
        std::io::ErrorKind::AddrNotAvailable => libc::EHOSTUNREACH,
        std::io::ErrorKind::AlreadyExists => libc::EEXIST,
        std::io::ErrorKind::InvalidInput => EINVAL,
        std::io::ErrorKind::NotFound => ENOENT,
        std::io::ErrorKind::PermissionDenied => EACCES,
        _ => EIO,
    }
}

fn is_valid_name(name: &str) -> bool {
    !name.is_empty() && name != "." && name != ".." && !name.contains('/') && !name.contains('\0')
}
