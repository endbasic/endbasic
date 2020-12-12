# The EndBASIC programming language - core

[![Build Status](https://travis-ci.org/jmmv/endbasic.svg?branch=master)](https://travis-ci.org/jmmv/endbasic/)
[![Crates.io](https://img.shields.io/crates/v/endbasic-core.svg)](https://crates.io/crates/endbasic-core/)
[![Docs.rs](https://docs.rs/endbasic-core/badge.svg)](https://docs.rs/endbasic-core/)

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

`endbasic-core` provides the language parser and interpreter, as well as the
standard library.  Note that exposing the standard library via the interpreter
is optional, and this can be done on a command-by-command basis.

## Language features

EndBASIC's language features are inspired by other BASIC interpreters but the
language does not intend to be fully compatible with them.  The language
currently supports:

*   Variable types: boolean (`?`), integer (`%`), and string (`$`).
*   Strong typing with optional variable type annotations.
*   `IF ... THEN` / `ELSEIF ... THEN` / `ELSE` / `END IF` statements.
*   `FOR x = ... TO ... [STEP ...]` / `NEXT` loops.
*   `WHILE ...` / `END WHILE` loops.
*   `INPUT` and `PRINT` builtins.
*   UTF-8 everywhere (I think).

## Implementation features

Some highlights about the EndBASIC implementation are:

*   Minimalist core.  The interpreter knows how to execute the logic of the
    language but, by default, it exposes no builtins to the scripts—not even
    `INPUT` or `PRINT`.  This makes EndBASIC ideal for embedding into other
    programs, as it is possible to execute external code without side-effects or
    by precisely controlling how such code interacts with the host program.

*   Minimalist library.  The standard library provides the logic for all
    built-in commands, but each command can be individually installed into the
    parser, and all interactions with the environment (e.g. the console, or the
    file system) are exposed via hooks that the caller needs to implement.

*   Async support.  The interpreter is async-compatible, making it trivial to
    embed it into Javascript via WASM.

## Examples

You can peek into the `tests` subdirectory of this repository to see actual
EndBASIC code samples.  Look for all files with a `.bas` extension.

The `examples` directory contains sample code to show how to embed the EndBASIC
interpreter into your own programs.
