# Major changes between releases

**IMPORTANT: There currently are no guarantees regarding the stability of
the EndBASIC language definition nor the API exposed by this crate.  Expect
them to change at any time (especially the Rust API).  Version numbers will
not adhere to semantic versioning until 1.0.0.**

## Changes in version X.Y.Z

**STILL UNDER DEVELOPMENT; NOT RELEASED YET.**

*   Fixed the `EXIT` command so that it doesn't terminate the REPL when it is
    part of a script run via `RUN`.

*   Added support for an in-memory store when running the REPL by specifying
    the `--programs-dir=:memory:` flag.

*   Added support to run scripts as if they were run in the interactive REPL
    by passing the `--interactive` flag.

*   Split the language and standard library into two separate crates: the
    existing `endbasic-core` continues to provide the language interpreter
    and the new `endbasic-std` provides the standard library.

## Changes in version 0.4.0

**Released on 2020-12-25.**

New user-experience features:

*   Added support for built-in demo programs.  These are loadable via the
    special read-only `DEMO:*.BAS` files.

*   Added the `DEMO:GUESS.BAS`, `DEMO:HELLO.BAS` and `DEMO:TOUR.BAS` built-in
    demo programs.

New language features:

*   Added simple `FOR` range loops with support for custom `STEP`s.

*   Added support for calls to builtin functions within expressions.

*   Added string manipulation functions: `LEFT`, `LEN`, `LTRIM`, `MID`,
    `RIGHT` and `RTRIM`.

*   Added numerical functions: `DTOI` and `ITOD`.

*   Added support to for random numbers via the `RANDOMIZE` command and the
    `RND` numerical function.

*   Added support for double-precision floating point numbers (`#` type
    annotation).  This feature is incomplete in many ways but is needed for
    random number generation.  Notably, it is not possible to express some
    double values in the code (exponents, infinities, and NaNs), and there is
    no type promotion between integers and doubles.  Use the new `ITOD` AND
    `DTOI` functions to convert between these two types.

Bug fixes:

*   Fixed the expression parser to properly handle subtractions where the first
    operand is a negative number.

*   Fixed the expression parser to detect and report unbalanced parenthesis.

Operational changes:

*   Builds from `HEAD` are now pushed to a separate staging area to keep the
    official site pinned to the latest release.  This is to make release
    numbers meaningful in the web context.

## Changes in version 0.3.1

**Released on 2020-11-29.**

The highlight of this new release is a much improved interactive interface,
as it gets rid of the line-oriented editor (which used meaningless line
numbers) and replaces it with a full-screen interactive editor.

New features:

*   Turned the `EDIT` command into an interactive full-screen text editor and
    removed the `LIST` and `RENUM` commands.

*   Added the `CLS`, `COLOR`, and `LOCATE` commands for terminal
    manipulation.

*   Added the `DEL` command to delete a saved program.

*   Added a language cheat sheet via `HELP LANG`.

*   Added a barebones web interface.

Notable bug fixes:

*   Fixed arithmetic operators to capture overflow conditions.

*   Fixed `EXIT` to accept `0` as the exit code.

Structural code changes:

*   Split the language core (parser, interpreter, and command implementations)
    out of the `endbasic` crate and moved it to a separate `endbasic-core`
    crate.  This is to ensure that the language components stay free from
    heavy dependencies that assume things about the environment (like terminal
    or file system access).

*   Made the language interpreter `async`-compatible.

## Changes in version 0.3.0

**Released on 2020-11-29.**

Broken build due to a bad merge from `HEAD`.

## Changes in version 0.2.0

**Released on 2020-05-07.**

This is the first release with an interactive command-line interface (aka
a REPL).  You can start this by simply typing `endbasic` without any
arguments.  Once in it, the following features are now available:

*   The `HELP` command to provide interactive information.

*   The `CLEAR` command to wipe machine state (variables).

*   The stored program manipulation commands `EDIT`, `LIST`, `NEW`, `RENUM`
    and `RUN`.

*   The on-disk program manipulation commands `DIR`, `LOAD` and `SAVE`.

Similarly, this is the first release that supports a nicer command-line
invocation experience, including flag parsing.  As a result:

*   Added the `--help` and `--version` flags to the command-line interface.

Finally, these are the changes to the core interpreter and language:

*   Added support for `:` as a statement delimiter.

*   Added support for `_` in identifiers.

*   Made `INPUT` recognize `yes/no` and `y/n` answers for boolean values
    on top of the already supported `true/false` values.

*   Added the `MOD` operator to compute the remainder of an integer division.

*   Made `INPUT` resilient to invalid boolean and integer answers by asking
    the user to input them again.  The caller has no means of determining
    failure so we must do this (like other BASIC implementations do).

*   Split the `INPUT` and `PRINT` builtin commands out of the language's
    core and into their own module.  This keeps the interpreter free from
    side-effects if the caller so chooses, which makes it ideal for
    embedding.

## Changes in version 0.1.0

**Released on 2020-04-22.**

*   Initial release of the EndBASIC project.
