# The EndBASIC programming language - core

![Build and test](https://github.com/jmmv/endbasic/workflows/Build%20and%20test/badge.svg)
![Health checks](https://github.com/jmmv/endbasic/workflows/Health%20checks/badge.svg)
![Deploy to staging](https://github.com/jmmv/endbasic/workflows/Deploy%20to%20staging/badge.svg)
![Deploy to release](https://github.com/jmmv/endbasic/workflows/Deploy%20to%20release/badge.svg)
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

`endbasic-core` provides the language parser and interpreter.  By design, this
crate provides zero commands and zero functions.

## Language features

EndBASIC's language features are inspired by other BASIC interpreters but the
language does not intend to be fully compatible with them.  The language
currently supports:

*   Variable types: boolean (`?`), double (`#`), integer (`%`), and string
    (`$`).
*   Strong typing with optional variable type annotations.
*   `IF ... THEN` / `ELSEIF ... THEN` / `ELSE` / `END IF` statements.
*   `FOR x = ... TO ... [STEP ...]` / `NEXT` loops.
*   `WHILE ...` / `WEND` loops.
*   UTF-8 everywhere (I think).

## Design principles

Some highlights about the EndBASIC implementation are:

*   Minimalist core.  The interpreter knows how to execute the logic of the
    language but, by default, it exposes no builtins to the scripts—not even
    `INPUT` or `PRINT`.  This makes EndBASIC ideal for embedding into other
    programs, as it is possible to execute external code without side-effects or
    by precisely controlling how such code interacts with the host program.

*   Async support.  The interpreter is async-compatible, making it trivial to
    embed it into Javascript via WASM.

## Examples

The `examples` directory contains sample code to show how to embed the EndBASIC
interpreter into your own programs.  In particular:

*   [`examples/config.rs`](examples/config.rs): Shows how to instantiate a
    minimal EndBASIC interpreter and uses it to implement what could be a
    configuration file parser.

*   [`examples/dsl.rs`](example/dsl.rs): Shows how to instantiate an EndBASIC
    interpreter with custom functions and commands to construct what could be a
    domain-specific language.  This language is then used to control some
    hypothetical hardware lights and exemplifies how to bridge the Rust world
    and the EndBASIC world.
