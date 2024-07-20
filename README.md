# The EndBASIC programming language

![Test](https://github.com/endbasic/endbasic/workflows/Test/badge.svg)
![Build release](https://github.com/endbasic/endbasic/workflows/Build%20release/badge.svg)
![Release checks](https://github.com/endbasic/endbasic/workflows/Release%20checks/badge.svg)
![Deploy to staging](https://github.com/endbasic/endbasic/workflows/Deploy%20to%20repl-staging.endbasic.dev/badge.svg)
![Deploy to release](https://github.com/endbasic/endbasic/workflows/Deploy%20to%20repl.endbasic.dev/badge.svg)

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

EndBASIC is free software under the [Apache 2.0 License](LICENSE).

**The latest version of EndBASIC is 0.11.0 and was released on 2024-07-20.**

## Quick start on the web

Open EndBASIC in your browser by visiting:

> <https://repl.endbasic.dev/>

Or go the project's website at:

> <https://www.endbasic.dev/>

The web interpreter should work on all major desktop browsers as well as mobile
devices (with some small known issues on Android).

The web interpreter runs fully locally: any programs you write are persisted in
your browser's local storage by default.  That said, you can choose to sign up
for the cloud service and upload your programs to share them with the world.

## Quick start on your machine

Visit the
[release page](https://github.com/endbasic/endbasic/releases/tag/endbasic-0.11.0)
to download prebuilt binaries.  Once downloaded, unpack the archive and run the
`endbasic` binary to get started.

Be aware that [the binaries are *not signed* right
now](https://github.com/endbasic/endbasic/issues/137) so it can be difficult to
get these to run on Windows and macOS.

The binary releases are built with the recommended settings: they all include
graphics support, and the builds for the Raspberry Pi include support for its
hardware.  To use the graphics console, you will need to launch the binary
using one of these forms:

```shell
endbasic --console=graphics            # Default console size, windowed.
endbasic --console=graphics:800x600    # Custom resolution.
endbasic --console=graphics:800x600fs  # Custom resolution, full screen.
endbasic --console=graphics:fs         # Desktop resolution, full screen.
```

## Building from source

Of course, you can also build and install EndBASIC from source by running the
following command (assuming you have a Rust toolchain installed):

```shell
cargo install endbasic
```

The above will fetch EndBASIC from <https://crates.io/>, build it with default
settings, and then install the resulting binary under `~/.cargo/bin/`.

If you want to enable graphics support (recommended), you will first have to
install the `SDL2` and `SDL2_ttf` libraries.  Follow these steps depending on
the platform you are on:

```shell
# On Debian-based systems:
sudo apt install libsdl2-dev libsdl2-ttf-dev
cargo install --features=sdl endbasic

# On FreeBSD systems:
sudo pkg install sdl2 sdl2_ttf
cargo install --features=sdl endbasic

# On macOS systems with Homebrew:
brew install sdl2 sdl2_ttf
cargo install --features=sdl endbasic

# On Windows systems, this is tricky.  The easiest way is to clone this
# repository and then do the following from PowerShell:
.\.github\workflows\setup-sdl.ps1
cargo build --release --features=sdl endbasic
```

If you want to enable support for the Raspberry Pi hardware (along with the
recommended graphics features), do this on the Raspberry Pi itself:

```shell
sudo apt install libsdl2-dev libsdl2-ttf-dev
cargo install --features=rpi,sdl endbasic
```

## More information

Refer to the [**User's Manual**](https://www.endbasic.dev/docs.html) for
information on how to get started with EndBASIC.

Type `HELP` within the interpreter to access the **Reference Manual**.

The following documents provide more information about the structure of
this repository:

*   For language features, see [`core/README.md`](core/README.md).
*   For standard library contents, see [`std/README.md`](std/README.md).
*   For usage details of the command-line interpreter, see
    [`cli/README.md`](cli/README.md).
*   For REPL information, see [`repl/README.md`](repl/README.md).
*   For terminal support, see [`terminal/README.md`](terminal/README.md).
*   For SDL support, see [`sdl/README.md`](sdl/README.md).
*   For Raspberry Pi specific features, see [`rpi/README.md`](rpi/README.md).
*   For the web interface, see [`web/README.md`](web/README.md).
*   For changes across versions, see [`NEWS.md`](NEWS.md).

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
