# Major changes between releases

**IMPORTANT: There currently are no guarantees regarding the stability of
the EndBASIC language definition nor the API exposed by this crate.  Expect
them to change at any time (especially the Rust API).  Version numbers will
not adhere to semantic versioning until 1.0.0.**

## Changes in version X.Y.Z

**STILL UNDER DEVELOPMENT; NOT RELEASED YET.**

*   Split the language core (parser, interpreter, and command implementations)
    out of the `endbasic` crate and moved them to a separate `endbasic-core`
    crate.  This is to ensure that the language components stay free from
    heavy dependencies that assume things about the environment (like terminal
    or file system access).

*   Added the `CLS`, `COLOR`, and `LOCATE` commands for terminal
    manipulation.

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
