# The EndBASIC programming language - benchmarks

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

## What's in this directory?

This directory contains ad-hoc benchmarking scenarios for EndBASIC.

The scenarios are stored under `scenarios` and are intended to exercise various
inner parts of the `core` (compiler and VM) and certain features of `std`.  The
`compare.sh` script is the driver to run one or more of these scenarios and
compare two different releases.

These scenarios were tuned to take about 30 seconds each on my machine--a
ThinkStation P710 with dual Intel(R) Xeon(R) CPU E5-2697 v4 @ 2.30GHz--when
executed with 0.12.1.
