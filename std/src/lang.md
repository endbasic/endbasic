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

# Symbols

Variable, array and function references

name?    Boolean (TRUE and FALSE).
name#    Floating point (double).
name%    Integer (32 bits).
name$    String.
name     Type determined by value or definition.

# Assignments

Assignments and declarations

varref[(dim1[, ..., dimN])] = expr
DIM varname[(dim1[, ..., dimN])] [AS BOOLEAN|DOUBLE|INTEGER|STRING]

# Expressions

Expressions and operators

a + b      a - b       a * b     a / b      a MOD b    a ^ b     -a
a AND b    NOT a       a OR b    a XOR b    (logical and bitwise)
a = b      a <> b      a < b     a <= b     a > b      a >= b
(a)        varref
arrayref(s1[, ..., sN])          funcref(a1[, ..., aN])

# Flow control

Jumps, conditionals, and loops

10 GOTO 10: @label GOTO @label
10 RETURN: GOSUB 10: @label RETURN: GOSUB @label
DO [UNTIL|WHILE expr?]: ...: [EXIT DO]: ...: LOOP
DO: ...: [EXIT DO]: ...: LOOP [UNTIL|WHILE expr?]
FOR varref = expr<%|#> TO expr<%|#> [STEP num]: ...: NEXT
IF expr? THEN ... [ELSE ...]
IF expr? THEN: ...: ELSEIF expr? THEN: ...: ELSE: ...: END IF
SELECT CASE expr:
    [CASE <expr|IS =|<>|<|<=|>|>= expr|expr TO expr>[, ...]: ...:]*
    [CASE ELSE: ...:] END SELECT
WHILE expr?: ...: WEND

# Error handling

Error guards

ON ERROR GOTO 0         Terminate program execution on error.
ON ERROR GOTO 100       Jump to line 100 on error.
ON ERROR GOTO @label    Jump to @label on error.
ON ERROR RESUME NEXT    Skip to the next statement on error.

# Miscellaneous

Things that don't fit anywhere else

st1: st2     Separates statements (same as a newline).
END [code%]  Terminates the program.
REM text     Comment until end of line.
' text       Comment until end of line.
,            Long separator for arguments to builtin call.
;            Short separator for arguments to builtin call.
DATA a, b    Registers literal primitive values for later reads.
&x_5fd1      Integer literals in base syntax (can be b, d, o, x).
