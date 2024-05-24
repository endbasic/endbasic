' EndBASIC
' Copyright 2024 Julio Merino
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

' Tests for expressions.
'
' These used to be done in core/src/eval.rs when the expressions were fully
' evaluated within the AST.  However, since we moved to bytecode execution,
' the evaluation of expressions relies on the parser, the compiler, and the
' execution engine.  As a result, it is much simpler to validate these cases
' with an integration test.

ON ERROR RESUME NEXT

PRINT ">>> Expression literals"
PRINT TRUE
PRINT 0.0
PRINT 0
PRINT "z"

PRINT ">>> Symbol references"
b = TRUE: PRINT b
d = 0.0: PRINT d
i = 0: PRINT i
s = "z": PRINT s

PRINT ">>> Operations and variables"
x = 10
y = 3
PRINT y * (x + 2)
PRINT x = (7 + y)

PRINT ">>> Array accesses"
DIM a(2, 4) AS INTEGER
a(1, 3) = 8
PRINT a(0, 3)
PRINT a%(1, 3)
PRINT a(-1, 0): PRINT ERRMSG
PRINT a(10, 0): PRINT ERRMSG

PRINT ">>> Simple function calls"
PRINT PI
PRINT MAX(5)
PRINT MAX(2, 5, 3)
PRINT MAX#(2, 5, 3)
