# The EndBASIC programming language - web interface

EndBASIC is an interpreter for a BASIC-like language and is inspired by
Amstrad's Locomotive BASIC 1.1 and Microsoft's QuickBASIC 4.5.  Like the former,
EndBASIC intends to provide an interactive environment that seamlessly merges
coding with immediate visual feedback.  Like the latter, EndBASIC offers
higher-level programming constructs and strong typing.

EndBASIC offers a simplified and restricted environment to learn the foundations
of programming and focuses on features that can quickly reward the programmer.
These features include things like a built-in text editor, commands to
render graphics and play sound, and commands to interact with the hardware of a
Raspberry Pi.

EndBASIC is written in Rust and runs both on the web and locally on a variety of
operating systems and platforms, including macOS, Windows, and Linux.

EndBASIC is free software under the [AGPL v3+](LICENSE).

## What's in this crate?

`endbasic-web` provides a WASM target for the EndBASIC interpreter, as well as
a minimal web interface to it.

## Trying it out

Visit the following address for a live deployment of the EndBASIC interpreter!

> https://repl.endbasic.dev/

## AGPLv3 deployment metadata

When producing a web build, you can customize the compliance and support links
embedded in the footer:

* `SOURCE_CODE_URL`: URL where users can fetch corresponding source code.
* `LICENSE_URL`: URL to the license text presented to users.
* `ISSUES_URL`: URL where users can report issues.

These are optional and default to the upstream EndBASIC URLs.
