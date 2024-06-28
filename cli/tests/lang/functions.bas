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
