# The EndBASIC programming language - REPL

![Build and test](https://github.com/endbasic/endbasic/workflows/Build%20and%20test/badge.svg)
![Health checks](https://github.com/endbasic/endbasic/workflows/Health%20checks/badge.svg)
![Deploy to staging](https://github.com/endbasic/endbasic/workflows/Deploy%20to%20staging/badge.svg)
![Deploy to release](https://github.com/endbasic/endbasic/workflows/Deploy%20to%20release/badge.svg)
[![Crates.io](https://img.shields.io/crates/v/endbasic-repl.svg)](https://crates.io/crates/endbasic-repl/)
[![Docs.rs](https://docs.rs/endbasic-repl/badge.svg)](https://docs.rs/endbasic-repl/)

EndBASIC is an interpreter for a BASIC-like language and is inspired by
Amstrad's Locomotive BASIC 1.1 and Microsoft's QuickBASIC 4.5.  Like the former,
EndBASIC intends to provide an interactive environment that seamlessly merges
coding with immediate visual feedback.  Like the latter, EndBASIC offers
higher-level programming constructs and strong typing.

EndBASIC offers a simplified and restricted environment to learn the foundations
of programming and focuses on features that can quickly reward the programmer.
These features include things like a built-in text editor, commands to
manipulate the screen, and commands to interact with the hardware of a Raspberry
Pi.  Implementing this kind of features has priority over others such as
performance or a much richer language.

EndBASIC is written in Rust and runs both on the web and locally on a variety of
operating systems and platforms, including macOS, Windows, and Linux.

EndBASIC is free software under the [Apache 2.0 License](LICENSE).

## What's in this crate?

`endbasic-repl` provides logic that is specific to the REPL and that is shared
by all frontends to EndBASIC.  This includes features like:

*   `AUTOEXEC.BAS` support.
*   Built-in demo programs.
*   Common console initialization.
