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

CLS
COLOR 11
PRINT
PRINT " EndBASIC tour: Welcome!"
PRINT "========================="
COLOR
PRINT
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
PRINT
COLOR 11
INPUT "Press ENTER to continue or CTRL+C to exit the demo...", dummy$

CLS
COLOR 11
PRINT
PRINT " EndBASIC tour: The basics"
PRINT "==========================="
COLOR
PRINT
PRINT "There are four primitive types:"
PRINT
PRINT "* Booleans (?): Literals TRUE and FALSE."
PRINT "* Double-precision floating point (#): Literals must contain a period."
PRINT "* 32-bit integers (%): Literals must not contain a period."
PRINT "* Strings ($): Literals are double-quoted."
PRINT
PRINT "Type annotations are optional when the type can be deduced.  The only time"
PRINT "when they are required is when defining new variables via INPUT."
PRINT "There are no type promotions (not even between integers and doubles)."
PRINT
PRINT "A trivial program to ask a question and print an answer would look like:"
PRINT
PRINT "    INPUT \"What is your name\"; name$"
PRINT "    PRINT \"Hello,\"; name$"
PRINT
PRINT "Expressions work as you would expect, with the usual operator precedence"
PRINT "rules.  Expressions can take function calls too, but I'll let you find what"
PRINT "those are via HELP."
PRINT
PRINT "There are no line numbers and no plans to add them... so, sorry, no GOTO!"
PRINT
COLOR 11
INPUT "Press ENTER to continue or CTRL+C to exit the demo...", dummy$

CLS
COLOR 11
PRINT
PRINT " EndBASIC tour: Control flow"
PRINT "============================="
COLOR
PRINT
PRINT "Fully-specified if statements look like this:"
PRINT
PRINT "    IF a% = 1 THEN"
PRINT "        PRINT \"a is 1\""
PRINT "    ELSEIF a% <> 2 THEN"
PRINT "        PRINT \"a is not 2\""
PRINT "    ELSE"
PRINT "        PRINT \"a is something else\""
PRINT "    END IF"
PRINT
PRINT "While loops look like this:"
PRINT
PRINT "    WHILE a% < 10"
PRINT "        a% = a% + 1"
PRINT "    WEND"
PRINT
PRINT "For loops look like this:"
PRINT
PRINT "    FOR a = 1 TO 10 STEP 2"
PRINT "        PRINT a"
PRINT "    NEXT"
PRINT
COLOR 11
INPUT "Press ENTER to continue or CTRL+C to exit the demo...", dummy$

CLS
COLOR 11
PRINT
PRINT " EndBASIC tour: File manipulation"
PRINT "=================================="
COLOR
PRINT
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
PRINT
COLOR 11
INPUT "Press ENTER to continue or CTRL+C to exit the demo...", dummy$

CLS
COLOR 11
PRINT
PRINT " EndBASIC tour: Screen manipulation"
PRINT "===================================="
COLOR
PRINT
PRINT "You have several commands at your disposal to manipulate the contents of"
PRINT "the screen.  Visual features are particularly interesting for teaching"
PRINT "purposes, so expect more in this regard."
PRINT
PRINT "For example, we can print the foundational colors by selecting them with"
PRINT "the \"COLOR\" command and positioning the cursor with \"LOCATE\":"
PRINT
FOR c% = 0 TO 7
    LOCATE 11 + c%, 4
    COLOR c%
    PRINT "This is color"; c%
NEXT
FOR c% = 8 TO 15
    LOCATE 11 + c% - 8, 23
    COLOR c%
    PRINT "This is color"; c%
NEXT
COLOR
PRINT
COLOR 11
INPUT "Press ENTER to continue or CTRL+C to exit the demo...", dummy$

CLS
COLOR 11
PRINT
PRINT " EndBASIC tour: Hardware access"
PRINT "================================"
COLOR
PRINT
PRINT "If you happen to be running on a Raspberry Pi, EndBASIC has some support"
PRINT "to manipulate its hardware.  At the moment this includes only basic access"
PRINT "to the GPIO lines.  See the \"DEMO:GPIO.BAS\" demo for an example."
PRINT
PRINT "Please note that you have to be running on a Raspberry Pi *AND* you must"
PRINT "have compiled EndBASIC with --features=rpi for this to work."
PRINT
COLOR
PRINT
COLOR 11
INPUT "Press ENTER to continue or CTRL+C to exit the demo...", dummy$

CLS
COLOR 11
PRINT
PRINT " EndBASIC tour: Enjoy"
PRINT "======================"
COLOR
PRINT
PRINT "And that's it for the tour.  You can now type EDIT to see the code that"
PRINT "took you over this journey, load other demo files or... just go forth and"
PRINT "explore.  HELP and DIR are your friends at any point."
PRINT
PRINT "If you like what you have seen so far, please head to the project's GitHub"
PRINT "page and give it a star:"
COLOR 12
PRINT
PRINT "    https://github.com/jmmv/endbasic/"
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
COLOR
PRINT
