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

'
' Calculates Fibonacci numbers using recursion to demonstrate user-defined
' functions and global variables.
'

DIM SHARED steps AS INTEGER

FUNCTION fibonacci(n AS INTEGER)
    SELECT CASE n
        CASE 0: fibonacci = 0
        CASE 1: fibonacci = 1
        CASE ELSE: fibonacci = fibonacci(n - 1) + fibonacci(n - 2)
    END SELECT
    steps = steps + 1
END FUNCTION

PRINT "fibonacci of 10 is:"; fibonacci(10)
PRINT "took"; steps; "steps to calculate"
