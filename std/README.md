# The EndBASIC programming language - standard library

![Build and test](https://github.com/endbasic/endbasic/workflows/Build%20and%20test/badge.svg)
![Health checks](https://github.com/endbasic/endbasic/workflows/Health%20checks/badge.svg)
![Deploy to staging](https://github.com/endbasic/endbasic/workflows/Deploy%20to%20staging/badge.svg)
![Deploy to release](https://github.com/endbasic/endbasic/workflows/Deploy%20to%20release/badge.svg)
[![Crates.io](https://img.shields.io/crates/v/endbasic-std.svg)](https://crates.io/crates/endbasic-std/)
[![Docs.rs](https://docs.rs/endbasic-std/badge.svg)](https://docs.rs/endbasic-std/)

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

EndBASIC is free software under the [Apache 2.0 License](LICENSE).

## What's in this crate?

`endbasic-std` provides the language standard library, which is composed of
various commands and functions.  Each of these can be exposed to the
interpreter individually.

## Standard library features

EndBASIC's standard library is inspired by other BASIC interpreters but does
not intend to be fully compatible with them.  The library currently contains:

*   Arrays: `LBOUND`, `UBOUND`.
*   Console manipulation: `CLS`, `COLOR`, `INKEY`, `INPUT`, `LOCATE`, `PRINT`.
*   Data manipulation: `READ`, `RESTORE`.
*   Date and time manipulation: `SLEEP`.
*   Graphics: `GFX_LINE`, `GFX_RECT`, `GFX_RECTF`.
*   Hardware interaction: `GPIO_CLEAR`, `GPIO_READ`, `GPIO_SETUP`, `GPIO_WRITE`.
*   File system interaction: `CD`, `DIR`, `MOUNT`, `PWD`, `UNMOUNT`.
*   Interpreter interaction: `CLEAR`, `HELP`.
*   Numerics: `ATN`, `CINT`, `COS`, `DEG`, `INT`, `MAX`, `MIN`, `PI`, `RAD`,
    `RANDOMIZE`, `RND`, `SIN`, `SQR`, `TAN`.
*   Program manipulation: `EDIT`, `KILL`, `LIST`, `LOAD`,`NEW`, `RUN`, `SAVE`.
*   Strings and characters: `ASC`, `CHR`, `LEFT`, `LEN`, `LTRIM`, `MID`,
    `RIGHT`, `RTRIM`.

## Design principles

Some highlights about the EndBASIC implementation are:

*   Minimalist library.  The standard library provides the logic for all
    built-in commands, but each command can be individually installed into the
    parser, and all interactions with the environment (e.g. the console, or the
    file system) are exposed via hooks that the caller needs to implement.

*   Async support.  The library is async-compatible, making it trivial to
    embed it into Javascript via WASM.

## Examples

The `examples` directory contains sample code to show how to embed the EndBASIC
interpreter and standard library into your own programs.

*   [`examples/script-runner.rs`](examples/script-runner.rs): Shows how to
    instantiate full-blown EndBASIC interpreter and uses it to implement a
    script runner.
