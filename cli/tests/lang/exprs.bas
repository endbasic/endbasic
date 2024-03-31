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
CLEAR

PRINT ">>> Symbol references"
b = TRUE: PRINT b
d = 0.0: PRINT d
i = 0: PRINT i
s = "z": PRINT s
PRINT x: PRINT ERRMSG
CLEAR

PRINT ">>> Logical operations"
' These tests just make sure that the expression evaluator delegates to the
' Value operations for each expression operator to essentially avoid duplicating
' all those tests.  We do this by triggering errors and rely on the fact that
' their messages are different for every operation.
PRINT FALSE AND 0: PRINT ERRMSG
PRINT FALSE OR 0: PRINT ERRMSG
PRINT FALSE XOR 0: PRINT ERRMSG
PRINT NOT 0.0: PRINT ERRMSG
CLEAR

PRINT ">>> Relational operations"
' These tests just make sure that the expression evaluator delegates to the
' Value operations for each expression operator to essentially avoid duplicating
' all those tests.  We do this by triggering errors and rely on the fact that
' their messages are different for every operation.
PRINT FALSE = 0: PRINT ERRMSG
PRINT FALSE <> 0: PRINT ERRMSG
PRINT FALSE < 0: PRINT ERRMSG
PRINT FALSE <= 0: PRINT ERRMSG
PRINT FALSE > 0: PRINT ERRMSG
PRINT FALSE >= 0: PRINT ERRMSG
CLEAR

PRINT ">>> Arithmetic operations"
' These tests just make sure that the expression evaluator delegates to the
' Value operations for each expression operator to essentially avoid duplicating
' all those tests.  We do this by triggering errors and rely on the fact that
' their messages are different for every operation.
PRINT FALSE + 0: PRINT ERRMSG
PRINT FALSE - 0: PRINT ERRMSG
PRINT FALSE * 0: PRINT ERRMSG
PRINT FALSE / 0: PRINT ERRMSG
PRINT FALSE MOD 0: PRINT ERRMSG
PRINT FALSE ^ 0: PRINT ERRMSG
PRINT -FALSE: PRINT ERRMSG
CLEAR

PRINT ">>> Operations and variables"
x = 10
y = 3
PRINT y * (x + 2)
PRINT x = (7 + y)
PRINT 3 = 7 + TRUE: PRINT ERRMSG
CLEAR

PRINT ">>> Array accesses"
DIM x(2, 4) AS INTEGER
x(1, 3) = 8
PRINT x(0, 3)
PRINT x%(1, 3)
PRINT x#(1, 3): PRINT ERRMSG
PRINT x(1): PRINT ERRMSG
PRINT x(-1): PRINT ERRMSG
PRINT x(10, 0): PRINT ERRMSG
PRINT y$(3, 4): PRINT ERRMSG
CLEAR

PRINT ">>> Simple function calls"
PRINT PI
PRINT MAX(5)
PRINT MAX(2, 5, 3)
PRINT MAX#(2, 5, 3)
PRINT MAX$(2, 5, 3): PRINT ERRMSG
PRINT UNKNOWN(2): PRINT ERRMSG
CLEAR

PRINT ">>> Calling of non-functions"
x = 0
PRINT x()
PRINT PRINT()
