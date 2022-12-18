<!--
    EndBASIC
    Copyright 2022 Julio Merino

    Licensed under the Apache License, Version 2.0 (the "License"); you may not
    use this file except in compliance with the License.  You may obtain a copy
    of the License at:

        http://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software
    distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
    WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the
    License for the specific language governing permissions and limitations
    under the License.
-->

<!--
    WHEN ADDING NEW SECTIONS TO THIS FILE, REMEMBER TO UPDATE help.bas TO
    VALIDATE THE FORMATTED OUTPUT.

    BEWARE THAT, EVEN IF THIS LOOKS LIKE MARKDOWN, IT REALLY IS NOT.  THE PARSER
    IS INCREDIBLY LIMITED IN WHAT IT CAN ACCEPT.
-->

# Types

Primitive types and arrays

EndBASIC supports the following primitive types:

*   `?`: BOOLEAN
    *   Literal values are `TRUE` and `FALSE`.

*   `#`: DOUBLE
    *   64-bit double floating point.
    *   Literal values have the form 123.4.

*   `%`: INTEGER
    *   32-bit signed integers.
    *   Literal values can be specified in binary (`b`), decimal (`d`), octal (`o`) and hexadecimal (`h`) bases.
    *   Literal values have the form 123, &d123, or &d_123, where `d` specifies the base.

*   `$`: STRING
    *   Literal values are UTF-8 double-quoted strings.
    *   Nested double-quotes can be escaped with a `\` character.

Multidimensional arrays are supported as well, although all the dimensions in an array must have the same type.

Integers are automatically promoted to floats when they appear in a float expression, and floats are demoted to integers via rounding (3.4 becomes 3, 3.5 becomes 4) when they appear in an integer expression.

# Variables

Variable references, assignments, and the DIM keyword

Variable identifiers are alphanumeric words that start with a letter or special character such as _.  Variable references can optionally be suffixed by a type identifier to force them to be of a specific type, but note that EndBASIC is strictly typed and variables cannot change type after they have been assigned.

Variables can be first defined either via an assignment or via the `DIM` keyword, the latter of which sets the variable to its zero value.  The following are all equivalent:

    DIM foo AS BOOLEAN
    DIM foo? AS BOOLEAN
    foo? = FALSE

Arrays must be defined with the `DIM` keyword before they can be used.  The following example defines a matrix and sets the value of a single element within it:

    DIM matrix%(10, 100) AS INTEGER
    matrix%(5, 15) = 1234

# Expressions

Expressions and operators

EndBASIC provides the following operators:

*   Numeric operators:
    *   Binary infix: +, -, *, /, MOD, ^
    *   Unary prefix: -

*   Logical and bitwise operators:
    *   Binary infix: AND, OR, XOR
    *   Unary prefix: NOT
    *   Whether these perform a logical or bitwise operation depends on the expression context.

*   Bitwise operators:
    *   Binary infix: <<, >> (signed integer shift without rotation)

*   Relational operators:
    *   Binary infix: =, <>, <, <=, >, >=

Expressions can also contain variable references, function calls, and array element references.  For example, the following defines an array of doubles, sets one of them, and then reads the value in an expression and rounds it to an integer via the `CINT` builtin function:

    DIM floats(5) AS DOUBLE
    floats(2) = 5.6
    PRINT 3 + 9 - CINT(floats(2))

# Style

Spacing, comments, and general style

Every statement in EndBASIC must appear in its own line.  Lines can be separated by natural newline characters, but also via the `:` character.  The following are equivalent:

    PRINT 3
    PRINT 4

    PRINT 3: PRINT 4

Comments can be introduced via `REM` or an apostrophe character and run throughout the end of a line:

    ' This is a comment.
    REM This is another comment.
    a = 3 ' Comment after statement.

The common EndBASIC style in documentation and sample programs is to:

*   Write all language keywords in uppercase.
*   Write all variable identifiers in lowercase.
*   Suffix all variable references and function calls with a type identifier.

These are just style guidelines and they are neither required nor enforced in your own code.  For a more modern look, you can type all code in lowercase letters and avoid type identifiers.

# IF

Multiline and uniline IF statements

Multiline IF statements look like the following.  Note that the `ELSEIF` and `ELSE` clauses are all optional, but if `ELSE` is present, it must appear last and only once:

    IF a = 1 THEN
        PRINT "a is 1"
    ELSEIF a <> 2 THEN
        PRINT "a is not 2"
    ELSE
        PRINT "a is something else"
    END IF

IF statements can be collapsed into a single line and look like the following.  Similarly to the previous, the `ELSE` clause is optional and can only appear once:

    IF a = 1 THEN PRINT "a is 1" ELSE PRINT "a is something else"

Note that, in the uniline form, only a subset of statements can be specified.

# SELECT CASE

Conditional statement to choose among values

The SELECT CASE statement allows evaluating an expression and comparing it to multiple different values or ranges.

    INPUT "Enter a number"; a
    SELECT CASE a
        CASE 1, 3, 5, 7, 9
            PRINT "Odd"
        CASE 0, 2, 5, 6, 8
            PRINT "Even"
        CASE IS < 0, 10 TO 100
            PRINT "Other cases"
        CASE ELSE
            PRINT "Fallback"
    END SELECT

The expression given to `SELECT CASE` is evaluated exactly once.  Similarly to `IF` statements, the `CASE ELSE`, if present, must appear only once at as the last case guard.

When using the `IS` guard, all relational operators can be specified.

# WHILE

While loops

The `WHILE` keyword is used to define a loop that executes a collection of statements until a guard condition is false.  They look like this:

    a = 0
    WHILE a < 10
        PRINT a
        a = a + 1
    WEND

# DO

Do loops

`DO` loops are a generalized form of `WHILE` loops.  `DO` loops allow testing a condition before or after every iteration, and the condition can be tested until it is true or false.  Take a look at the following examples:

    DO
        PRINT "Infinite loop"
    LOOP

    DO
        a = a + 1
    LOOP UNTIL a = 10

    DO
        a = a + 1
    LOOP WHILE a < 10

    a = 0
    DO UNTIL a = 10
        a = a + 1
    LOOP

    a = 0
    DO WHILE a < 10
        a = a + 1
    LOOP

`DO` loops can be exited an any point via the `EXIT DO` statement.

# FOR

For loops

`FOR` loops provide iteration through a numeric range.  Their most basic form looks like this:

    FOR a = 1 to 10
        PRINT a
    NEXT

You can optionally specify a positive or negative `STEP` to change how the iterator changes in each loop body execution:

    FOR a = 10 to 1 STEP -2
        PRINT a
    NEXT

# Jumps

GOTO, GOSUB, END, and labels

EndBASIC statements can be labeled via explicitly-assigned line numbers or textual identifiers.  These labels can be used as the target of the unstructured control flow statements `GOTO` and `GOSUB`.  For example:

    i = 1
    20 PRINT i ' Statement with a numeric label.
    IF i = 10 THEN GOTO @out
    i = i + 1
    GOTO 20
    @out ' Statement with a textual label.

When using `GOSUB` to temporarily jump to a subroutine, use the `RETURN` keyword when done:

    GOTO @main

    @add
    result = a + b
    RETURN

    @main
    a = 3: b = 5: GOSUB @add
    PRINT result

Program execution can be terminated at any point via the `END` statement, which optionally takes an exit code to return to the calling program.

# ON ERROR

Error handling

Certain types of errors can be caught for inspection and program recovery.

To jump to a line number or label when a recoverable error is caught:

    ON ERROR GOTO 100
    ON ERROR GOTO @label

To continue execution at the next statement after an error is caught:

    ON ERROR RESUME NEXT

To reset the error handler to its default, which terminates program execution on an error:

    ON ERROR GOTO 0

The ERRMSG function can be used to fetch the textual description of the string that was caught.
