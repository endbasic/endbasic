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

PRINT ">>> argless functions with default return values"

FUNCTION argless_default_default
END FUNCTION

FUNCTION argless_boolean_default?
END FUNCTION

FUNCTION argless_double_default#
END FUNCTION

FUNCTION argless_integer_default%
END FUNCTION

FUNCTION argless_string_default$
END FUNCTION

PRINT "argless_default_default: "; argless_default_default
PRINT "argless_boolean_default: "; argless_boolean_default
PRINT "argless_double_default: "; 1 + argless_double_default + 3
PRINT "argless_integer_default: "; 1 + argless_integer_default + 3
PRINT "argless_string_default: "; argless_string_default + "bar"

PRINT ">>> argless functions with explicit return values"

FUNCTION argless_default_set
    argless_default_set = 5
END FUNCTION

FUNCTION argless_boolean_set?
    argless_boolean_set = TRUE
END FUNCTION

FUNCTION argless_double_set#
    argless_double_set = 5.2
END FUNCTION

FUNCTION argless_integer_set%
    argless_integer_set = 123
END FUNCTION

FUNCTION argless_string_set$
    argless_string_set = "foo"
END FUNCTION

PRINT "argless_default_set: "; argless_default_set
PRINT "argless_boolean_set: "; argless_boolean_set
PRINT "argless_double_set: "; 1 + argless_double_set + 3
PRINT "argless_integer_set: "; 1 + argless_integer_set + 3
PRINT "argless_string_set: "; argless_string_set + "bar"

PRINT ">>> Call chains"

FUNCTION second$
    second = "foo"
END FUNCTION

FUNCTION first%
    IF second = "foo" THEN
        first = 5
    ELSE
        first = 3
    END IF
END FUNCTION

PRINT "first: "; first
PRINT "second: "; second

PRINT ">>> Local variables"

defined_globally = 1

FUNCTION local
    defined_globally = 2
    defined_locally = 3
    PRINT "defined_globally on exit: "; defined_globally
    PRINT "defined_locally on exit: "; defined_locally
END FUNCTION

PRINT local
PRINT defined_globally
defined_locally = "foo"  ' Would yield type error if not unset on exit.

PRINT ">>> Global variables"

DIM SHARED really_global
really_global = 1

FUNCTION get_really_global
    get_really_global = really_global * 2
    really_global = really_global + 1
END FUNCTION

PRINT "get_really_global returned: "; get_really_global
PRINT "get_really_global returned: "; get_really_global
PRINT "really_global is: "; really_global

PRINT ">>> Arguments with annotations"

param_b = 1234

FUNCTION annotated_params(param_b?, param_d#, param_i%, param_s$)
    PRINT "param_b is "; param_b
    PRINT "param_d is "; param_d
    PRINT "param_i is "; param_i
    PRINT "param_s is "; param_s
END FUNCTION

PRINT annotated_params(TRUE, 3.4, 5, "hello")

PRINT ">>> Arguments with types"

FUNCTION params_with_as(b AS BOOLEAN, d AS DOUBLE, i AS INTEGER, s AS STRING)
    PRINT "b is "; b
    PRINT "d is "; d
    PRINT "i is "; i
    PRINT "s is "; s
END FUNCTION

PRINT params_with_as(FALSE, -1.0, 2, "foo")

PRINT ">>> Type promotion in arguments"

FUNCTION args_promotion(d AS DOUBLE, i AS INTEGER)
    PRINT "d is "; d
    PRINT "i is "; i
END FUNCTION

PRINT args_promotion(5, 2.6)

PRINT ">>> Type promotion in return values"

FUNCTION return_promotion%
    return_promotion = 2.8
END FUNCTION

PRINT return_promotion

PRINT ">>> Recursion"

FUNCTION recurse(i)
    IF i > 0 THEN
       PRINT "entering level: "; i
       PRINT recurse(i - 1)
       PRINT "leaving level: "; i
    END IF
END FUNCTION

PRINT recurse(3)
