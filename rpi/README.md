# The EndBASIC programming language - Raspbery Pi support

[![Crates.io](https://img.shields.io/crates/v/endbasic-rpi.svg)](https://crates.io/crates/endbasic-rpi/)
[![Docs.rs](https://docs.rs/endbasic-rpi/badge.svg)](https://docs.rs/endbasic-rpi/)

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

`endbasic-rpi` provides Raspberry Pi support for the following features defined
in the `endbasic-std` crate:

*   GPIO pins support.
*   SPI bus support.
