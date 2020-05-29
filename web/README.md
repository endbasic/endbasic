# The EndBASIC programming language - web interface

[![Build Status](https://travis-ci.org/jmmv/endbasic.svg?branch=master)](https://travis-ci.org/jmmv/endbasic/)

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

`endbasic-web` provides a WASM target for the EndBASIC interpreter, as well as
a minimal web interface to it.

## Trying it out

Visit the following address for a live deployment of the EndBASIC interpreter!

> https://jmmv.github.io/endbasic/
