# Major changes between releases

**IMPORTANT: There currently are no guarantees regarding the stability of
the EndBASIC language definition nor the API exposed by this crate.  Expect
them to change at any time (especially the Rust API).  Version numbers will
not adhere to semantic versioning until 1.0.0.**

**IMPORTANT: Similarly, there are no guarantees that old releases will be able
to talk to the cloud service.  If you use the web interface, this should not be
a problem, but if you use local builds, please try to stay on the latest release
for the time being.**

## Changes in version 0.10.99

**STILL UNDER DEVELOPMENT; NOT RELEASED YET.**

*   Fixed JSON requests to the service to properly set the correct
    `Content-Type` header.

*   Improved support for narrow consoles: trimmed the width of the welcome
    banner, fixed the editor's status line handling, made `DIR` print a
    concise directory summary, made `LOGIN` skip the server's `motd`, and
    fixed handling of line input in prompts.

*   Issue #110: Homogenized the implementation of the SDL and web consoles to
    guarantee consistent behavior and to have indirect test coverage of the
    web console.

*   Added the new console `st7735s` for the Raspberry Pi.  This console uses the
    ST7735S 1.44in LCD for the console output and the terminal console for input,
    but also recognizes the hat's buttons and injects them as keyboard events.

*   Rewrote the expression evaluator to be bytecode based.  This opens the way
    towards user-supplied functions and the ability to interrupt functions as
    they execute.

*   Changed the way integers with explicit bases are parsed so that they can
    express integers with their highest bit set.  For bitmasks, this is needed.

*   The `CLEAR` command is now only available in the interactive interpreter given
    that it cannot clear compilation state.

*   Many errors that were previously discovered only at runtime (such as undefined
    variables) are now caught during the compilation stage.  This means that bad
    programs abort earlier instead of half-way during execution.

*   Reverted integer-only operations to *not* perform automatic upgrades to
    doubles on underflows, overflows, and other error conditions.  This behavior
    was previously added in 0.10.0 but it's now problematic that we do type
    propagation during compilation as it pushes too much responsibility to the
    runtime.

*   Major performance improvements: type checking now happens at compilation time
    and the interpreter checks for interrupts more rarely now.

*   Fixed the `MID` function so that the `length%` parameter is actually optional
    as the documentation claimed.
    
*   Homogenized the handling of command and function arguments into a single
    parser.  The user-visible effects of this change are that all syntax
    definitions that `HELP` prints now follow a consistent pattern and that such
    help strings truly match what the commands and functions expect.

## Changes in version 0.10.0

**Released on 2022-12-27.**

This is a huge release that focuses on extending the capabilities of the core
language so that non-trivial programs can be written in it.

Language changes for better control flow:

*   Issue #153: Added support for labels (identifiers prefixed by an `@` sign)
    and `GOTO`.

*   Issue #155: Added support for "line numbers as labels", just like
    QuickBASIC does, which permits running the traditional `10 GOTO 10`
    program.  Note, however, that these line numbers have nothing to do with
    the actual line numbers in the file.  To minimize confusion, line numbers
    have been removed from the output of `LIST`.

*   Added support for `GOSUB` and `RETURN`, which provides a rudimentary
    mechanism to reuse code within a program.

*   Issue #121: Added support for catching errors via `ON ERROR GOTO` and `ON
    ERROR RESUME NEXT`.  Captured error messages are exposed to the user via
    a new `ERRMSG` function.

*   Replaced the `EXIT` command with the `END` keyword.

*   Added support for `DO` loops with optional `UNTIL`/`WHILE` pre- and
    post-guards and `EXIT DO` early terminations.

*   Issue #152: Added support for uniline `IF` statements.

*   Added support for `SELECT CASE`.

*   Fixed `END` so that it works in the context of `WHILE` loops and so that
    no further expressions are evaluated in `FOR` and `IF statements.

*   Rewrote the execution interpreter to be bytecode based instead of walking
    over the AST.

Language changes for better numeric handling:

*   Issue #114: Added transparent promotion from integers to doubles and
    automatic rounding of doubles as integers.

*   Issue #114: Added support for doubles in `FOR` iteration, both to specify
    the loop range and the step.

*   Added support for the exponent (`^`) operator and the `SQR` function.

*   Added syntax to specify integers in different bases, using forms like
    `&b_1010`, `&d_1234`, `&o_750`, and `&x_12f`.

*   Extended `AND`, `NOT`, `OR`, and `XOR` to perform bitwise operations when
    operating on an integer context and added the `<<` and `>>` bit shift
    operators.

Standard library changes:

*   Issue #114: Removed the `DTOI` and `ITOD` functions now that integers and
    doubles are automatically converted between them, and added the `CINT` and
    `INT` functions.

*   Issue #114: Removed the `MAXD`/`MAXI` and `MIND`/`MINI` duality in favor of
    simpler `MAX` and `MIN` functions that can mix and match integers and
    doubles.

*   Changed the syntax of the `MOUNT` command to take advantage of the `AS`
    keyword as an argument separator and thus be of the form
    `MOUNT target$ AS $drive_name$`.

*   Fixed `PRINT` so that, if the statement ends in a comma or in a semicolon,
    no newline character is printed.  Useful to construct output lines in
    multiple steps and matches the behavior of other BASIC implementations.

*   Issue #154: Added support for the `DATA` statement and the `READ` and
    `RESTORE` commands.  Booleans, numbers, and strings are supported, but
    strings must be double-quoted (as opposed to other BASIC implementations
    where the double-quoting is optional).

*   Added the `ASC`, `CHR`, and `STR` functions.

*   Renamed `DEL` as `KILL` to match QuickBASIC and avoid confusion with a
    potential future `DELETE` command implementation.

*   Fixed `INPUT` so that the prompt is optional and thus things like
    `INPUT var` work as they do in traditional BASIC implementations.

*   Issue #108: Added the `SCRROWS` and `SCRCOLS` functions to query the size
    of the textual console and the `GFX_HEIGHT` and `GFX_WIDTH` to query the
    size of the graphical console.

*   Added the `GFX_CIRCLE` and `GFX_CIRCLEF` commands to draw circles.

Usability improvements and fixes:

*   Issue #113: Added line and column tracking to error messages for parsing
    and execution errors.  Also cleaned up Rust `Debug` impls that leaked
    into strings to provide nicer error messages.

*   Issue #111: Added support to interrupt running programs via `CTRL+C`.

*   Extended the builtin language documentation to explain in detail every
    statement type.  `HELP "LANG"` now displays a collection of topics to
    choose from, instead of a one-page cheat sheet.

*   Added the `PALETTE.BAS` demo, which is a little tool that renders the
    full color palette.

*   Changed the syntax to call argument-less functions, such as `INKEY` and
    `PI`, so that they do not accept `()`.  This matches traditional BASIC
    implementations.

*   Fixed erratic insertion of newlines in existing text in the editor.

*   Modified the `HELP` command to only accept a string as its argument
    instead of also recognizing a bare word.  The latter was only approximate
    and would cause confusion when typing something like `HELP DATA`, as this
    resulted in a parse error.

*   Rewrote the SDL console internals to use a separate thread that implements
    the SDL main loop.  This fixes some rendering issues and crashes that have
    been previously observed with this implementation.

*   Modified the interpreter to parse the full program before executing it,
    which was a requirement for supporting `GOTO`s and features like `DATA`.
    As a side-effect of this change, any syntax errors now cause the
    interpreted program to not run at all, as opposed to before when the
    program would make progress until it hit the error.

## Changes in version 0.9.0

**Released on 2022-06-05.**

The primary goal of this release is to support major changes in the EndBASIC
cloud service, which has a completely new account signup and authentication
flow that allow unauthenticated users to load publicly shared files.  These
changes, combined with the in-interpreter account signup flow, fulfill the
vision of the cloud service interactions.

Cloud service changes:

*   Updated `LOGIN` to deal with the new version of the EndBASIC cloud service
    that does not use Azure AD for authentication.  This new command is faster
    and simpler.

*   Added the `SIGNUP` command to create cloud accounts right from the REPL.
    Having this command in the interpreter had always been the goal, but it
    was not possible to implement it due to Azure AD authentication flows.

*   Added support to access files without logging in first.  The `cloud://`
    file system scheme can now be used before using `LOGIN`, and the `DIR` and
    `LOAD` commands will work on the mounted drive as long as there are public
    files within it.

*   Added the `LOGOUT` command.  As a side-effect of this, it is now possible
    to use `LOGIN` multiple times within the same interpreter session.

*   Issue #131: Added support to auto-run programs from the cloud to the web UI:
    a URL of the form `https://repl.endbasic.dev/?run=username/path` will load
    the interpreter, fetch `path` owned by `username` and run it.

*   Added support to auto-run programs from the cloud to the CLI, to mimic the
    changes done to the web UI.  A path of the form `cloud://username/path`
    given to the command line interpreter will fetch `path` owned by `username`
    and run it.  Due to various limitations, this is only available when the
    interpreter is launched with the `--interactive` flag.

*   Parameterized the cloud service to talk to.  In the CLI, the new
    `--service-url` allows overriding the default, and in the web, the staging
    site now points to the staging service.

Usability fixes:

*   Issue #161: Fixed input methods (line input in the REPL and the full-screen
    text editor) to properly accept UTF-8.

*   Issue #163: Fixed backspace handling in the the web and SDL consoles so
    that the previous character is not left behind the cursor.  The problem was
    visible in the web UI where the semi-transparent cursor would show the
    previous letter.

Internal changes:

*   Added a new `endbasic-client` crate to assimilate all of the funcionality
    and commands required to talk to the cloud service.  This helps to keep the
    `endbasic-std` crate leaner dependencies-wise and facilitates configuring
    the client.

## Changes in version 0.8.1

**Released on 2022-01-29.**

*   Issue #136: Fixed handling of key presses on the web interface so that they
    don't interfere with browser shortcuts.  This prevents Tab from stealing
    focus from the terminal, the arrow keys from doing strange things when
    "caret browsing" is enabled, and the slash key in Firefox from triggering a
    search on the page.

*   Issue #148: Fixed interactive line edits so that moving up and down through
    history doesn't leave old characters behind when the cursor is in the middle
    of a line (not at the end).

*   Replaced the use of Google Analytics in the web interface with EndTRACKER,
    my own experiment at site statistics.  If you are curious, this service's
    code is a direct fork of EndBASIC's cloud service--hence the name.

## Changes in version 0.8.0

**Released on 2021-11-11.**

The main purpose of this release is to bring you the new hybrid graphics/text
console in the form of a feature preview.  This feature brings EndBASIC closer
to its original secret goal, which is to become a platform with which to write
simple retro-looking games.

Please be aware that the new console is still quite rudimentary.  There are
many missing drawing primitives, and performance isn't great yet.  Fixing these
might require changes in the APIs so any code you write might need to be updated
in the future.  But, remember that the same is true for all of EndBASIC right
now given its 0.x state.

This release lines up with the Handmade Seattle 2021 conference, during which it
was first announced.

Graphics support and related console changes:

*   Added a graphical console based on SDL2 behind a new optional `sdl`
    feature.  This is to support graphics on all desktop platforms and has been
    confirmed to work on FreeBSD, Linux, macOS, and Windows.

*   Added the `GFX_LINE`, `GFX_PIXEL`, `GFX_RECT`, `GFX_RECTF`, and `GFX_SYNC`
    graphics commands.

*   Added the `INKEY` function.  This is especially useful to implement event
    loops in graphical applications.

*   Fixed `LOCATE` so that the first argument is the column number and the
    second argument is the row number.  It should always have been this way
    (in fact, this is the syntax exposed by Locomotive BASIC), but this is now
    necessary to match the ordering of the coordinates in all graphics commands
    and avoid confusion.

*   Modified console facilities (including `PRINT` and `INPUT`) so that they do
    not clear lines up to the right margin.  I had originally added this as a
    feature so that changing the background color in the REPL caused all
    subsequent lines to be formatted consistently, but this prevented composing
    overlapping text (with or without graphics), which is a necessary thing to
    do when rendering UIs.

*   Rewrote the web frontend from scratch to support graphics rendering.  This
    implies that we do not use `xterm.js` any more and instead use a
    custom-built console implementation.  Beware of new bugs.

*   Issue #67: Keyboard input on Android should now work when using a soft
    keyboard.  This isn't perfect due to limitations in the Android web APIs
    but should do the trick for simple uses.

General command changes:

*   Extended the `CLEAR` and `NEW` commands so that they reset various
    properties of the machine, not just variables.  This includes the state of
    the console, whose color and video syncing bit are reset, and the GPIO
    pins, which are set to their default state.

*   Modified the `RUN` command to issue a `CLEAR` upfront.  Maintaining the
    previous state of the machine was just too confusing and error-prone due
    to side-effects causing execution failures.

*   Added the `MIND`, `MINI`, `MAXD`, and `MAXI` functions.

*   Added the `DEG` and `RAD` trigonometric commands and the `ATN`, `COS`,
    `PI`, `SIN`, and `TAN` functions.  These are often needed to render
    graphics.

Interactivity improvements:

*   Issue #119: Added support for the Home, End, Page Up, and Page Down keys
    in the text editor.

*   Made the Backspace and Tab keys aware of indentation in the editor.

*   Added support for the Home and End keys in text input fields.

*   Modified the storage commands to keep track of the currently-loaded program
    path so that the editor can display it, so that `LOAD`, `EXIT`, and `NEW`
    can warn about unsaved changes, and so that `SAVE` can reuse the current
    filename.

Internal changes:

*   Refactored the `endbasic-std` crate to minimize optional features in
    library crates by moving the textual console into a new `endbasic-terminal`
    crate, the SDL console into a new `endbasic-sdl` crate, and the Raspberry
    Pi support into a new `endbasic-rpi` crate.

*   Added a new `endbasic-repl` crate to assimilate all of the features and
    code that are specific to the REPL.  This finally breaks the dependency
    of the `endbasic-web` crate on the `endbasic` CLI crate, which required
    optional features to work.

## Changes in version 0.7.0

**Released on 2021-07-03.**

This is a huge release and its primary goal is to offer integration with the new
EndBASIC cloud service.  To reach that goal, this release adds disk drives, new
commands specifically for cloud interaction, and comes with various usability
improvements to make the whole experience better.

Support for disk drives:

*   Added support for storage drives.  All file commands now take a path to a
    file of the form `DRIVE:/PATH` where the drive part and the slash are
    optional.  By default, three drives are available: `MEMORY:`, which is a
    trivial memory-backed drive; `DEMOS:`, which contains the read-only demo
    files; and `LOCAL:`, which points to local storage (either a local directory
    or to the web browser's local storage).

*   Added the `CD` command to change the current drive and the `PWD` command to
    print the current location.

*   Extended the `DIR` command to take an optional path to the directory to
    show.

*   Added the `MOUNT` and `UNMOUNT` commands to inspect and manipulate the
    mounted drives.  Note that this now allows users to mount arbitrary parts
    of the external file system within the EndBASIC namespace, when in theory
    it wasn't possible to escape the programs directory before.  This is
    intentional, but if there is a need, we can put restrictions in place
    again.

*   Renamed the `--programs-dir` flag to `--local-drive` and removed the special
    handling of the `:memory:` value.  Instead, this can now take arbitrary URIs
    to refer to drive targets.

Support for the EndBASIC cloud service:

*   Added the `LOGIN` command to authenticate against the EndBASIC service and
    to mount the user's own drive.

*   Added a new `cloud://` mount target scheme to specify the drives of other
    users.

*   Added the `SHARE` command to set reader ACLs on files hosted in the
    EndBASIC service, allowing users to share files among themselves.

Usability improvements:

*   Refactored the `HELP` command to only print a summary of topics by
    default.  As part of this, topics can now be looked up using prefixes of
    their names.

*   Made the output of `HELP` fit within the screen for easier readability
    instead of allowing long paragraphs to wrap at unpredictable points.

*   Added input history tracking to the REPL interface.

Miscellaneous additions:

*   Added the array functions `LBOUND` and `UBOUND`.

## Changes in version 0.6.0

**Released on 2021-02-19.**

Summary: support for (multidimensional) arrays and support for GPIO on the
Raspberry Pi.

New standard library features:

*   Added basic support for GPIO via the new `GPIO_SETUP`, `GPIO_CLEAR`,
    `GPIO_WRITE` commands and the `GPIO_READ` function.  These symbols are
    always available, but at the moment, they are only functional on the
    Raspberry Pi.  Support for this platform must be enabled via the new
    `rpi` feature because the `rppal` dependency does not compile on all
    supported platforms.

*   Added the `SLEEP` command to pause execution for a certain period of time.

*   Readded the `LIST` command to dump the stored program to the console.  This
    was removed in 0.3 with the addition of the full-screen text editor, but
    having quick access to the program's contents is useful to showcase both
    code and output at once.

*   Modified `INPUT` so that it autodetects the target type of a variable when
    the variable is already defined, instead of assuming the integer type for
    unqualified variable references.

New command line features:

*   Added the new demo program `DEMO:GPIO.BAS` to accompany the new support
    for GPIO.

New language features and bug fixes:

*   Added support for the `DIM` statement to define variables and arrays.

*   Added support for multidimensional arrays.

*   Replaced `END WHILE` with `WEND` as the earlier BASICs did.  We could
    probably support both, but for now, sticking to the simpler world of a
    different keyword per statement seems nicer (and this matches what the
    `FOR`/`NEXT` pair do).

*   Fixed the expression parser to properly handle symbol names that appear
    immediately after a left parenthesis.  This broke with the addition of
    function calls.

*   Fixed the definition of variables so that their names cannot shadow
    existing functions.

*   Refactored the internal representation of symbols (variables, arrays,
    functions, and commands) for a more uniform handling.  As a side-effect, it
    is now an error to have two symbols of any kind with the same name.

## Changes in version 0.5.1

**Released on 2021-01-25.**

*   Fixed the dependencies of the `endbasic` crate so that `cargo install`
    works as documented.

## Changes in version 0.5.0

**Released on 2021-01-24.**

This is primarily a quality-focused release.  Most of the work since 0.4.0 has
gone into fixing long-standing issues in the codebase (particularly around
internal testability), but a lot of these have also had end-user impact.

New user-experience features:

*   Added support to load an `AUTOEXEC.BAS` file at REPL startup time.

*   Made file names in the web UI case-insensitive.  Any pre-existing files
    will be renamed to have an all-uppercase name to support the new semantics.

*   Added support for an in-memory store when running the REPL by specifying
    the `--programs-dir=:memory:` flag.

*   Added support to run scripts as if they were run in the interactive REPL
    by passing the `--interactive` flag.

Bug fixes:

*   Fixed the `EXIT` command so that it doesn't terminate the REPL when it is
    part of a script run via `RUN`.

*   Made the web interface not restart the machine on an exit request (such as
    a call to `EXIT`) so that any state is not lost.  It's too easy to hit
    Ctrl+C by mistake, for example.

Major internal API changes:

*   Split the language and standard library into two separate crates: the
    existing `endbasic-core` continues to provide the language interpreter
    and the new `endbasic-std` provides the standard library.

*   Added a public `testutils` module within the `std` crate to offer test
    utilities for consumers of the EndBASIC crates.

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
