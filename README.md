# The EndBASIC programming language

[![Build Status](https://travis-ci.org/jmmv/endbasic.svg?branch=master)](https://travis-ci.org/jmmv/endbasic/)
[![Crates.io](https://img.shields.io/crates/v/endbasic.svg)](https://crates.io/crates/endbasic/)
[![Docs.rs](https://docs.rs/endbasic/badge.svg)](https://docs.rs/endbasic/)

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

## Features

EndBASIC's features are inspired by other BASIC interpreters but the language
does not intend to be fully compatible with them.  The language currently
supports:

*   Variable types: boolean (`?`), integer (`%`), and string (`$`).
*   Strong typing with optional variable type annotations.
*   `IF ... THEN` / `ELSEIF ... THEN` / `ELSE` / `END IF` statements.
*   `WHILE ...` / `END WHILE` loops.
*   `INPUT` and `PRINT` builtins.
*   UTF-8 everywhere (I think).

The EndBASIC core is minimal: the interpreter knows how to execute the logic
of the language but, by default, it exposes no builtins to the scripts---not
even `INPUT` or `PRINT`.  This makes EndBASIC ideal for embedding into other
programs, as it is possible to execute external code without side-effects or
by precisely controlling how such code interacts with the host program.

## Installation

The latest version of EndBASIC is 0.1.0 and was released on 2020-04-22.

There currently are no binary releases for EndBASIC.  To install, first get a
Rust toolchain (either from your system's package manager, if any, or using
[`rustup`](https://www.rust-lang.org/learn/get-started)) and then build from
source using `cargo`:

```shell
cargo install endbasic
```

This should work on any Linux, macOS, and Windows system (all of which are
tested on CI).

## Usage

At the moment, the `endbasic` binary does not yet provide an interactive
interpreter so all you can do is give it files to execute:

```shell
endbasic some-program.bas
```

You can peek into the `tests` subdirectory of this repository to see actual code
samples.

## Why EndBASIC?

EndBASIC started as part of my desire to teach programming to my own kids.
I remember learning programming on an old Amstrad CPC 6128: the experience was
unique in the sense that every command had immediate effect.  Changing colors,
drawing on the screen, or playing sounds were just a few keystrokes away after
booting the computer, without the need to deal with separate editors and
terminals.  I've noticed a similar excitement in my kids when showing this to
them via an emulator, so I thought I would replicate this in a more modern
fashion.  And here we are.

Because of this inspiration, EndBASIC's name stands for "E. and D.'s BASIC"
following my kids first name initials.
