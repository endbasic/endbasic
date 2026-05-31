# The EndBASIC programming language - FUSE filesystem

[![Crates.io](https://img.shields.io/crates/v/endbasic-fuse.svg)](https://crates.io/crates/endbasic-fuse/)
[![Docs.rs](https://docs.rs/endbasic-fuse/badge.svg)](https://docs.rs/endbasic-fuse/)

EndBASIC is an interpreter for a BASIC-like language and is inspired by
Amstrad's Locomotive BASIC 1.1 and Microsoft's QuickBASIC 4.5.  Like the former,
EndBASIC intends to provide an interactive environment that seamlessly merges
coding with immediate visual feedback.  Like the latter, EndBASIC offers
higher-level programming constructs and strong typing.

EndBASIC offers a simplified and restricted environment to learn the foundations
of programming and focuses on features that can quickly reward the programmer.
These features include things like a built-in text editor, commands to
render graphics, and commands to interact with the hardware of a Raspberry
Pi.  Implementing this kind of features has priority over others such as
performance or a much richer language.

EndBASIC is written in Rust and runs both on the web and locally on a variety of
operating systems and platforms, including macOS, Windows, and Linux.

EndBASIC is free software under the [AGPL v3+](LICENSE).

## What's in this crate?

`endbasic-fuse` provides a Linux-only FUSE filesystem that exposes the
EndBASIC cloud service as a mounted hierarchy of users and files.

Run it like this:

```shell
endbasic-fuse --user my-name --password my-password /mnt/endbasic
```

The mounted tree contains one directory per user at the service root.  The
logged-in user's directory is writable; all other user directories are read-only.
