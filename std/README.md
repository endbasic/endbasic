# The EndBASIC programming language - standard library

![Build and test](https://github.com/jmmv/endbasic/workflows/Build%20and%20test/badge.svg)
![Health checks](https://github.com/jmmv/endbasic/workflows/Health%20checks/badge.svg)
![Deploy to staging](https://github.com/jmmv/endbasic/workflows/Deploy%20to%20staging/badge.svg)
![Deploy to release](https://github.com/jmmv/endbasic/workflows/Deploy%20to%20release/badge.svg)
[![Crates.io](https://img.shields.io/crates/v/endbasic-std.svg)](https://crates.io/crates/endbasic-std/)
[![Docs.rs](https://docs.rs/endbasic-std/badge.svg)](https://docs.rs/endbasic-std/)

EndBASIC is an interpreter for a BASIC-like language and is inspired by
Amstrad's Locomotive BASIC 1.1 and Microsoft's QuickBASIC 4.5.  Like the former,
EndBASIC intends to provide an interactive environment that seamlessly merges
coding with immediate visual feedback.  Like the latter, EndBASIC offers
higher-level programming constructs and strong typing.  The main idea behind
EndBASIC is to provide a playground for learning the foundations of programming
in a simplified environment.

EndBASIC is written in Rust.  The parser and interpreter's primary goal is to
be readable and easy to modify.  A secondary goal is to make the core minimal,
extensible, and configurable.  Performance is not a goal right now, though it
likely won't disappoint.

EndBASIC is free software under the [Apache 2.0 License](LICENSE).

## What's in this crate?

`endbasic-std` provides the language standard library, which is composed of
various commands and functions.  Each of these can be exposed to the
interpreter individually.

## Standard library features

EndBASIC's standard library is inspired by other BASIC interpreters but does
not intend to be fully compatible with them.  The library currently contains:

*   Console manipulation: `CLS`, `COLOR`, `INPUT`, `LOCATE`, `PRINT`.
*   Interpreter interaction: `CLEAR`, `EXIT`, `HELP`.
*   Numerics: `DTOI`, `ITOD`, `RANDOMIZE`, `RND`.
*   Program manipulation: `DEL`, `DIR`, `EDIT`, `LOAD`, `NEW`, `RUN`, `SAVE`.
*   Strings: `LEFT`, `LEN`, `LTRIM`, `MID`, `RIGHT`, `RTRIM`.

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
