' EndBASIC
' Copyright 2020 Julio Merino
'
' Licensed under the Apache License, Version 2.0 (the "License"); you may not
' use this file except in compliance with the License.  You may obtain a copy
' of the License at:
'
'     http://www.apache.org/licenses/LICENSE-2.0
'
' Unless required by applicable law or agreed to in writing, software
' distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
' WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
' License for the specific language governing permissions and limitations
' under the License.

GOTO @main

' Clears the screen and prints the title in `title$`.
@banner
CLS
GFX_SYNC FALSE
COLOR 11
PRINT
title$ = " EndBASIC tour: " + title$
underline$ = ""
FOR i = 1 TO LEN%(title$) + 1
    underline$ = underline$ + "="
NEXT
PRINT title$
PRINT underline
COLOR
PRINT
RETURN

' Waits for a key press at the end of a demo screen.
@wait
PRINT
COLOR 11
PRINT "Press ENTER to continue or ESC to exit the demo...";
GFX_SYNC TRUE
DO
    SELECT CASE INKEY
    CASE "ENTER": EXIT DO
    CASE "ESC": GOTO @end
    CASE ELSE: SLEEP 0.01
    END SELECT
LOOP
RETURN

@main

title = "Welcome!": GOSUB @banner
PRINT "Welcome to the EndBASIC tour demo program.  I'm glad you have made it this far!"
PRINT
PRINT "EndBASIC is an interpreter for a BASIC-like language and is inspired by"
PRINT "Amstrad's Locomotive BASIC 1.1 and Microsoft's QuickBASIC 4.5.  The main idea"
PRINT "behind EndBASIC is to provide a playground for learning the foundations of"
PRINT "programming in a simplified environment."
PRINT
PRINT "EndBASIC is written in Rust and is proven to work on Linux, macOS and Windows."
PRINT "It likely works on other Unix systems too.  And, thanks to WASM, it also runs"
PRINT "on the web--which I bet is how you are reading this right now."
PRINT
PRINT "If you are accessing EndBASIC via the web interface, please be aware that"
PRINT "this interface is highly experimental and has many rough edges.  In particular,"
PRINT "things will go wrong if you try to resize the browser window.  Just reload"
PRINT "the page for a \"reboot\"."
PRINT
COLOR 9
PRINT "When not in the tour, use the HELP command to access the interactive help"
PRINT "system."
COLOR
PRINT
PRINT "Without further ado, let's get started!"
GOSUB @wait

title = "Language basics": GOSUB @banner
PRINT "There are four primitive types: booleans (?), double-precision floating"
PRINT "point numbers (#), 32-bit signed integers (%), and strings ($)."
PRINT
PRINT "The common IF and SELECT CASE conditional structures, the DO, FOR, and WHILE"
PRINT "loops, as well as GOSUB and GOTO are supported."
PRINT
PRINT "A trivial program to ask a question and print an answer would look like:"
PRINT
PRINT "    @retry: INPUT \"Enter a number greater than 10: \", n"
PRINT "    IF n <= 10 THEN GOTO @retry"
PRINT "    PRINT \"Good job!\""
PRINT
PRINT "Type HELP \"LANG\" for specific details about the language constructs."
GOSUB @wait

title = "File manipulation": GOSUB @banner
PRINT "Given that you are reading this tour, you have already encountered how to"
PRINT "load a program and run it.  But here is how you'd go about creating a new"
PRINT "program from scratch:"
PRINT
PRINT "1. Type NEW to clear the machine's program and variables."
PRINT "2. Type EDIT to enter the full-screen editor."
PRINT "3. Type your program in the editor and then press ESC to exit."
PRINT "4. Optionally save your program with SAVE \"some-name.bas\"."
PRINT "5. Run the program with RUN."
PRINT "6. Repeat from 2 if things don't go as planned."
PRINT
PRINT "The cycle above works for demos too.  You can LOAD any demo program and"
PRINT "enter the interactive editor with EDIT to see and modify its code.  What"
PRINT "you cannot do is save them under their original name; you will have to pick"
PRINT "a different name."
PRINT
PRINT "If you are in the browser, rest assured that all programs are stored in"
PRINT "your browser's local storage.  Nothing goes to the cloud."
GOSUB @wait

title = "The file system": GOSUB @banner
PRINT "In the previous page, you learned how to create files and how to save and"
PRINT "load them.  Those examples used relative paths.  However, EndBASIC supports"
PRINT "multiple drives (although it does not yet support directories)."
PRINT
PRINT "Paths in EndBASIC have the form DRIVE:FILE or DRIVE:/FILE.  Given that"
PRINT "directories are not yet supported, both are equivalent, but their meaning"
PRINT "might change in the future.  All commands that operate on paths accept these"
PRINT "syntaxes.  Note that the DRIVE: part is optional: when not specified, the"
PRINT "current drive (shown by the DIR command) will be used."
PRINT
PRINT "You can use the MOUNT command to display the list of currently-mounted drives"
PRINT "and to attach new ones.  Pay attention to the default MOUNT output as it"
PRINT "shows some of the possible URIs you can use to mount other drives."
PRINT "For example, if you want to gain access to an arbitrary directory in the"
PRINT "system, you could do:"
PRINT
PRINT "    MOUNT \"TMP\", \"file:///var/tmp\""
PRINT "    CD \"TMP:/\""
PRINT
PRINT "Pay attention to the double quotes surrounding these arguments: these are"
PRINT "EndBASIC commands and thus you must provide the arguments as strings.  You"
PRINT "are bound to trip over this a few times due to muscle memory..."
GOSUB @wait

title = "Screen manipulation": GOSUB @banner
PRINT "You have several commands at your disposal to manipulate the contents of"
PRINT "the screen.  Visual features are particularly interesting for teaching"
PRINT "purposes, so expect more in this regard."
PRINT
PRINT "For example, we can print the foundational colors by selecting them with"
PRINT "the \"COLOR\" command and positioning the cursor with \"LOCATE\":"
PRINT
FOR c% = 0 TO 7
    LOCATE 4, 11 + c%
    COLOR c%
    PRINT "This is color"; c%
NEXT
FOR c% = 8 TO 15
    LOCATE 23, 11 + c% - 8
    COLOR c%
    PRINT "This is color"; c%
NEXT
COLOR
GOSUB @wait

title = "Hardware access": GOSUB @banner
PRINT "If you happen to be running on a Raspberry Pi, EndBASIC has some support"
PRINT "to manipulate its hardware.  At the moment this includes only basic access"
PRINT "to the GPIO lines.  See the \"DEMOS:/GPIO.BAS\" demo for an example."
PRINT
PRINT "Please note that you have to be running on a Raspberry Pi *AND* you must"
PRINT "have compiled EndBASIC with --features=rpi for this to work."
GOSUB @wait

title = "Enjoy": GOSUB @banner
PRINT "And that's it for the tour.  You can now type EDIT to see the code that"
PRINT "took you over this journey, load other demo files or... just go forth and"
PRINT "explore.  HELP, MOUNT, and DIR are your friends at any point, but so that"
PRINT "you don't feel too lost, run this now:"
PRINT
COLOR 1
PRINT "    CD \"DEMOS:/\""
PRINT "    DIR"
COLOR
PRINT
PRINT "If you like what you have seen so far, please head to the project's GitHub"
PRINT "page and give it a star:"
COLOR 12
PRINT
PRINT "    https://github.com/endbasic/endbasic/"
PRINT
COLOR
PRINT "Then, visit my blog and subscribe to receive fresh EndBASIC content or..."
PRINT "you know, to keep me motivated in writing stuff and building this project:"
COLOR 12
PRINT
PRINT "    https://jmmv.dev/"
PRINT
COLOR
PRINT "Thank you! :-)"
PRINT
COLOR 10
PRINT "-- Brought to you by Julio Merino <jmmv@>"

@end
GFX_SYNC TRUE
COLOR
PRINT
