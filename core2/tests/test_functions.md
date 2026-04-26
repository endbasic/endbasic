# Test: Return value matches function type

## Source

```basic
FUNCTION foo$
    foo = "abc"
END FUNCTION

OUT foo$
```

## Disassembly

```asm
0000:   JUMP        4                   ; 1:10

;; FOO (BEGIN)
0001:   LOADI       R64, 0              ; 1:10
0002:   LOADI       R64, 1              ; 2:11
0003:   RETURN                          ; 3:1
;; FOO (END)

0004:   CALL        R65, 1              ; 5:5, FOO
0005:   LOADI       R64, 259            ; 5:5
0006:   UPCALL      0, R64              ; 5:1, OUT
0007:   EOF                             ; 0:0
```

## Output

```plain
0=abc$
```

# Test: Type mismatch in return value

## Source

```basic
FUNCTION foo$
    foo = 3
END FUNCTION

OUT foo$
```

## Compilation errors

```plain
2:11: Cannot assign value of type INTEGER to variable of type STRING
```

# Test: Elaborate execution flow

## Source

```basic
a = 10

FUNCTION foo
    a = 20
    OUT "Inside", a
    foo = 30
END FUNCTION

OUT "Before", a
OUT "Return value", foo
OUT "After", a
```

## Disassembly

```asm
0000:   LOADI       R64, 10             ; 1:5
0001:   JUMP        11                  ; 3:10

;; FOO (BEGIN)
0002:   LOADI       R64, 0              ; 3:10
0003:   LOADI       R65, 20             ; 4:9
0004:   LOADI       R67, 0              ; 5:9
0005:   LOADI       R66, 291            ; 5:9
0006:   MOVE        R69, R65            ; 5:19
0007:   LOADI       R68, 258            ; 5:19
0008:   UPCALL      0, R66              ; 5:5, OUT
0009:   LOADI       R64, 30             ; 6:11
0010:   RETURN                          ; 7:1
;; FOO (END)

0011:   LOADI       R66, 1              ; 9:5
0012:   LOADI       R65, 291            ; 9:5
0013:   MOVE        R68, R64            ; 9:15
0014:   LOADI       R67, 258            ; 9:15
0015:   UPCALL      0, R65              ; 9:1, OUT
0016:   LOADI       R66, 2              ; 10:5
0017:   LOADI       R65, 291            ; 10:5
0018:   CALL        R68, 2              ; 10:21, FOO
0019:   LOADI       R67, 258            ; 10:21
0020:   UPCALL      0, R65              ; 10:1, OUT
0021:   LOADI       R66, 3              ; 11:5
0022:   LOADI       R65, 291            ; 11:5
0023:   MOVE        R68, R64            ; 11:14
0024:   LOADI       R67, 258            ; 11:14
0025:   UPCALL      0, R65              ; 11:1, OUT
0026:   EOF                             ; 0:0
```

## Output

```plain
0=Before$ , 1=10%
0=Inside$ , 1=20%
0=Return value$ , 1=30%
0=After$ , 1=10%
```

# Test: Function call requires jumping backwards

## Source

```basic
FUNCTION first
    OUT "first"
    first = 123
END FUNCTION

FUNCTION second
    second = first
END FUNCTION

OUT second
```

## Disassembly

```asm
0000:   JUMP        7                   ; 1:10

;; FIRST (BEGIN)
0001:   LOADI       R64, 0              ; 1:10
0002:   LOADI       R66, 0              ; 2:9
0003:   LOADI       R65, 259            ; 2:9
0004:   UPCALL      0, R65              ; 2:5, OUT
0005:   LOADI       R64, 123            ; 3:13
0006:   RETURN                          ; 4:1
;; FIRST (END)

0007:   JUMP        11                  ; 6:10

;; SECOND (BEGIN)
0008:   LOADI       R64, 0              ; 6:10
0009:   CALL        R64, 1              ; 7:14, FIRST
0010:   RETURN                          ; 8:1
;; SECOND (END)

0011:   CALL        R65, 8              ; 10:5, SECOND
0012:   LOADI       R64, 258            ; 10:5
0013:   UPCALL      0, R64              ; 10:1, OUT
0014:   EOF                             ; 0:0
```

## Output

```plain
0=first$
0=123%
```

# Test: Default return value is reset

## Source

```basic
FUNCTION default_double#
END FUNCTION

FUNCTION default_integer
END FUNCTION

FUNCTION default_string$
END FUNCTION

FUNCTION do_call
    OUT 300
    OUT default_double  ' Needs to print 0.
    OUT default_integer  ' Needs to print 0.
    OUT default_string  ' Needs to print "".
END FUNCTION

OUT do_call
```

## Disassembly

```asm
0000:   JUMP        3                   ; 1:10

;; DEFAULT_DOUBLE (BEGIN)
0001:   LOADI       R64, 0              ; 1:10
0002:   RETURN                          ; 2:1
;; DEFAULT_DOUBLE (END)

0003:   JUMP        6                   ; 4:10

;; DEFAULT_INTEGER (BEGIN)
0004:   LOADI       R64, 0              ; 4:10
0005:   RETURN                          ; 5:1
;; DEFAULT_INTEGER (END)

0006:   JUMP        9                   ; 7:10

;; DEFAULT_STRING (BEGIN)
0007:   LOADI       R64, 1              ; 7:10
0008:   RETURN                          ; 8:1
;; DEFAULT_STRING (END)

0009:   JUMP        24                  ; 10:10

;; DO_CALL (BEGIN)
0010:   LOADI       R64, 0              ; 10:10
0011:   LOADI       R66, 300            ; 11:9
0012:   LOADI       R65, 258            ; 11:9
0013:   UPCALL      0, R65              ; 11:5, OUT
0014:   CALL        R66, 1              ; 12:9, DEFAULT_DOUBLE
0015:   LOADI       R65, 257            ; 12:9
0016:   UPCALL      0, R65              ; 12:5, OUT
0017:   CALL        R66, 4              ; 13:9, DEFAULT_INTEGER
0018:   LOADI       R65, 258            ; 13:9
0019:   UPCALL      0, R65              ; 13:5, OUT
0020:   CALL        R66, 7              ; 14:9, DEFAULT_STRING
0021:   LOADI       R65, 259            ; 14:9
0022:   UPCALL      0, R65              ; 14:5, OUT
0023:   RETURN                          ; 15:1
;; DO_CALL (END)

0024:   CALL        R65, 10             ; 17:5, DO_CALL
0025:   LOADI       R64, 258            ; 17:5
0026:   UPCALL      0, R64              ; 17:1, OUT
0027:   EOF                             ; 0:0
```

## Output

```plain
0=300%
0=0#
0=0%
0=$
0=0%
```

# Test: Local variables

## Source

```basic
FUNCTION modify_2
    var = 300
    modify_2 = 2000
    OUT "Inside modify_2", var
END FUNCTION

FUNCTION modify_1
    var = 200
    OUT "Before modify_2", var
    OUT modify_2
    OUT "After modify_2", var
    modify_1 = 1000
END FUNCTION

var = 100
OUT "Before modify_1", var
OUT modify_1
OUT "After modify_1", var
```

## Disassembly

```asm
0000:   JUMP        10                  ; 1:10

;; MODIFY_2 (BEGIN)
0001:   LOADI       R64, 0              ; 1:10
0002:   LOADI       R65, 300            ; 2:11
0003:   LOADI       R64, 2000           ; 3:16
0004:   LOADI       R67, 0              ; 4:9
0005:   LOADI       R66, 291            ; 4:9
0006:   MOVE        R69, R65            ; 4:28
0007:   LOADI       R68, 258            ; 4:28
0008:   UPCALL      0, R66              ; 4:5, OUT
0009:   RETURN                          ; 5:1
;; MODIFY_2 (END)

0010:   JUMP        28                  ; 7:10

;; MODIFY_1 (BEGIN)
0011:   LOADI       R64, 0              ; 7:10
0012:   LOADI       R65, 200            ; 8:11
0013:   LOADI       R67, 1              ; 9:9
0014:   LOADI       R66, 291            ; 9:9
0015:   MOVE        R69, R65            ; 9:28
0016:   LOADI       R68, 258            ; 9:28
0017:   UPCALL      0, R66              ; 9:5, OUT
0018:   CALL        R67, 1              ; 10:9, MODIFY_2
0019:   LOADI       R66, 258            ; 10:9
0020:   UPCALL      0, R66              ; 10:5, OUT
0021:   LOADI       R67, 2              ; 11:9
0022:   LOADI       R66, 291            ; 11:9
0023:   MOVE        R69, R65            ; 11:27
0024:   LOADI       R68, 258            ; 11:27
0025:   UPCALL      0, R66              ; 11:5, OUT
0026:   LOADI       R64, 1000           ; 12:16
0027:   RETURN                          ; 13:1
;; MODIFY_1 (END)

0028:   LOADI       R64, 100            ; 15:7
0029:   LOADI       R66, 3              ; 16:5
0030:   LOADI       R65, 291            ; 16:5
0031:   MOVE        R68, R64            ; 16:24
0032:   LOADI       R67, 258            ; 16:24
0033:   UPCALL      0, R65              ; 16:1, OUT
0034:   CALL        R66, 11             ; 17:5, MODIFY_1
0035:   LOADI       R65, 258            ; 17:5
0036:   UPCALL      0, R65              ; 17:1, OUT
0037:   LOADI       R66, 4              ; 18:5
0038:   LOADI       R65, 291            ; 18:5
0039:   MOVE        R68, R64            ; 18:23
0040:   LOADI       R67, 258            ; 18:23
0041:   UPCALL      0, R65              ; 18:1, OUT
0042:   EOF                             ; 0:0
```

## Output

```plain
0=Before modify_1$ , 1=100%
0=Before modify_2$ , 1=200%
0=Inside modify_2$ , 1=300%
0=2000%
0=After modify_2$ , 1=200%
0=1000%
0=After modify_1$ , 1=100%
```

# Test: Local is not global

## Source

```basic
FUNCTION set_local
    local_var = 8
END FUNCTION

OUT set_local
OUT local_var
```

## Compilation errors

```plain
6:5: Undefined symbol local_var
```

# Test: Argument passing

## Source

```basic
FUNCTION add(a, b)
    add = a + b
END FUNCTION

OUT add(3, 5) + add(10, 20)
```

## Disassembly

```asm
0000:   JUMP        6                   ; 1:10

;; ADD (BEGIN)
0001:   LOADI       R64, 0              ; 1:10
0002:   MOVE        R64, R65            ; 2:11
0003:   MOVE        R67, R66            ; 2:15
0004:   ADDI        R64, R64, R67       ; 2:13
0005:   RETURN                          ; 3:1
;; ADD (END)

0006:   LOADI       R67, 3              ; 5:9
0007:   LOADI       R68, 5              ; 5:12
0008:   CALL        R66, 1              ; 5:5, ADD
0009:   MOVE        R65, R66            ; 5:5
0010:   LOADI       R68, 10             ; 5:21
0011:   LOADI       R69, 20             ; 5:25
0012:   CALL        R67, 1              ; 5:17, ADD
0013:   MOVE        R66, R67            ; 5:17
0014:   ADDI        R65, R65, R66       ; 5:15
0015:   LOADI       R64, 258            ; 5:5
0016:   UPCALL      0, R64              ; 5:1, OUT
0017:   EOF                             ; 0:0
```

## Output

```plain
0=38%
```

# Test: Argument passing with result saved to global

## Source

```basic
FUNCTION foo(i)
    foo = 42 + i
END FUNCTION

DIM SHARED ret
ret = foo(3)
OUT ret
```

## Disassembly

```asm
0000:   JUMP        6                   ; 1:10

;; FOO (BEGIN)
0001:   LOADI       R64, 0              ; 1:10
0002:   LOADI       R64, 42             ; 2:11
0003:   MOVE        R66, R65            ; 2:16
0004:   ADDI        R64, R64, R66       ; 2:14
0005:   RETURN                          ; 3:1
;; FOO (END)

0006:   LOADI       R0, 0               ; 5:12
0007:   LOADI       R65, 3              ; 6:11
0008:   CALL        R64, 1              ; 6:7, FOO
0009:   MOVE        R0, R64             ; 6:7
0010:   MOVE        R65, R0             ; 7:5
0011:   LOADI       R64, 258            ; 7:5
0012:   UPCALL      0, R64              ; 7:1, OUT
0013:   EOF                             ; 0:0
```

## Output

```plain
0=45%
```

# Test: Arguments are passed by value

## Source

```basic
FUNCTION change_integer(i%)
    i = 3
END FUNCTION

FUNCTION change_string(s$)
    s = "foo"
END FUNCTION

i = 5
OUT change_integer(i)
OUT i

s = "bar"
OUT change_string(s)
OUT s
```

## Disassembly

```asm
0000:   JUMP        4                   ; 1:10

;; CHANGE_INTEGER (BEGIN)
0001:   LOADI       R64, 0              ; 1:10
0002:   LOADI       R65, 3              ; 2:9
0003:   RETURN                          ; 3:1
;; CHANGE_INTEGER (END)

0004:   JUMP        8                   ; 5:10

;; CHANGE_STRING (BEGIN)
0005:   LOADI       R64, 0              ; 5:10
0006:   LOADI       R65, 0              ; 6:9
0007:   RETURN                          ; 7:1
;; CHANGE_STRING (END)

0008:   LOADI       R64, 5              ; 9:5
0009:   MOVE        R68, R64            ; 10:20
0010:   CALL        R67, 1              ; 10:5, CHANGE_INTEGER
0011:   MOVE        R66, R67            ; 10:5
0012:   LOADI       R65, 258            ; 10:5
0013:   UPCALL      0, R65              ; 10:1, OUT
0014:   MOVE        R66, R64            ; 11:5
0015:   LOADI       R65, 258            ; 11:5
0016:   UPCALL      0, R65              ; 11:1, OUT
0017:   LOADI       R65, 1              ; 13:5
0018:   MOVE        R69, R65            ; 14:19
0019:   CALL        R68, 5              ; 14:5, CHANGE_STRING
0020:   MOVE        R67, R68            ; 14:5
0021:   LOADI       R66, 258            ; 14:5
0022:   UPCALL      0, R66              ; 14:1, OUT
0023:   MOVE        R67, R65            ; 15:5
0024:   LOADI       R66, 259            ; 15:5
0025:   UPCALL      0, R66              ; 15:1, OUT
0026:   EOF                             ; 0:0
```

## Output

```plain
0=0%
0=5%
0=0%
0=bar$
```

# Test: Upcall with repeated arguments and return of type double

## Source

```basic
OUT SUM_DOUBLES(3.4, 2, 7.1)
```

## Disassembly

```asm
0000:   LOADC       R68, 0              ; 1:17
0001:   LOADI       R67, 289            ; 1:17
0002:   LOADI       R70, 2              ; 1:22
0003:   LOADI       R69, 290            ; 1:22
0004:   LOADC       R72, 1              ; 1:25
0005:   LOADI       R71, 257            ; 1:25
0006:   UPCALL      0, R66              ; 1:5, SUM_DOUBLES
0007:   MOVE        R65, R66            ; 1:5
0008:   LOADI       R64, 257            ; 1:5
0009:   UPCALL      1, R64              ; 1:1, OUT
0010:   EOF                             ; 0:0
```

## Output

```plain
0=12.5#
```

# Test: Upcall returning integer

## Source

```basic
OUT SUM_INTEGERS(3, 2, 7)
```

## Disassembly

```asm
0000:   LOADI       R68, 3              ; 1:18
0001:   LOADI       R67, 290            ; 1:18
0002:   LOADI       R70, 2              ; 1:21
0003:   LOADI       R69, 290            ; 1:21
0004:   LOADI       R72, 7              ; 1:24
0005:   LOADI       R71, 258            ; 1:24
0006:   UPCALL      0, R66              ; 1:5, SUM_INTEGERS
0007:   MOVE        R65, R66            ; 1:5
0008:   LOADI       R64, 258            ; 1:5
0009:   UPCALL      1, R64              ; 1:1, OUT
0010:   EOF                             ; 0:0
```

## Output

```plain
0=12%
```

# Test: Upcall returning string

## Source

```basic
OUT CONCAT$("hello", " ", "world")
```

## Disassembly

```asm
0000:   LOADI       R68, 0              ; 1:13
0001:   LOADI       R67, 291            ; 1:13
0002:   LOADI       R70, 1              ; 1:22
0003:   LOADI       R69, 291            ; 1:22
0004:   LOADI       R72, 2              ; 1:27
0005:   LOADI       R71, 259            ; 1:27
0006:   UPCALL      0, R66              ; 1:5, CONCAT
0007:   MOVE        R65, R66            ; 1:5
0008:   LOADI       R64, 259            ; 1:5
0009:   UPCALL      1, R64              ; 1:1, OUT
0010:   EOF                             ; 0:0
```

## Output

```plain
0=hello world$
```

# Test: Upcall returning boolean

## Source

```basic
OUT IS_POSITIVE?(42)
```

## Disassembly

```asm
0000:   LOADI       R67, 42             ; 1:18
0001:   UPCALL      0, R66              ; 1:5, IS_POSITIVE
0002:   MOVE        R65, R66            ; 1:5
0003:   LOADI       R64, 256            ; 1:5
0004:   UPCALL      1, R64              ; 1:1, OUT
0005:   EOF                             ; 0:0
```

## Output

```plain
0=true?
```

# Test: Argless upcall

## Source

```basic
OUT MEANING_OF_LIFE
```

## Disassembly

```asm
0000:   UPCALL      0, R65              ; 1:5, MEANING_OF_LIFE
0001:   LOADI       R64, 258            ; 1:5
0002:   UPCALL      1, R64              ; 1:1, OUT
0003:   EOF                             ; 0:0
```

## Output

```plain
0=42%
```

# Test: Function upcall result assigned to global

## Source

```basic
DIM SHARED x AS DOUBLE
x = SUM_DOUBLES(1.5, 2.5)
OUT x
```

## Disassembly

```asm
0000:   LOADI       R0, 0               ; 1:12
0001:   LOADC       R66, 0              ; 2:17
0002:   LOADI       R65, 289            ; 2:17
0003:   LOADC       R68, 1              ; 2:22
0004:   LOADI       R67, 257            ; 2:22
0005:   UPCALL      0, R64              ; 2:5, SUM_DOUBLES
0006:   MOVE        R0, R64             ; 2:5
0007:   MOVE        R65, R0             ; 3:5
0008:   LOADI       R64, 257            ; 3:5
0009:   UPCALL      1, R64              ; 3:1, OUT
0010:   EOF                             ; 0:0
```

## Output

```plain
0=4#
```

# Test: Argless upcall result assigned to global

## Source

```basic
DIM SHARED x
x = MEANING_OF_LIFE
OUT x
```

## Disassembly

```asm
0000:   LOADI       R0, 0               ; 1:12
0001:   UPCALL      0, R64              ; 2:5, MEANING_OF_LIFE
0002:   MOVE        R0, R64             ; 2:5
0003:   MOVE        R65, R0             ; 3:5
0004:   LOADI       R64, 258            ; 3:5
0005:   UPCALL      1, R64              ; 3:1, OUT
0006:   EOF                             ; 0:0
```

## Output

```plain
0=42%
```

# Test: Function upcall in expression

## Source

```basic
OUT SUM_DOUBLES(1.0, 2.0) + SUM_DOUBLES(3.0, 4.0)
```

## Disassembly

```asm
0000:   LOADC       R68, 0              ; 1:17
0001:   LOADI       R67, 289            ; 1:17
0002:   LOADC       R70, 1              ; 1:22
0003:   LOADI       R69, 257            ; 1:22
0004:   UPCALL      0, R66              ; 1:5, SUM_DOUBLES
0005:   MOVE        R65, R66            ; 1:5
0006:   LOADC       R69, 2              ; 1:41
0007:   LOADI       R68, 289            ; 1:41
0008:   LOADC       R71, 3              ; 1:46
0009:   LOADI       R70, 257            ; 1:46
0010:   UPCALL      0, R67              ; 1:29, SUM_DOUBLES
0011:   MOVE        R66, R67            ; 1:29
0012:   ADDD        R65, R65, R66       ; 1:27
0013:   LOADI       R64, 257            ; 1:5
0014:   UPCALL      1, R64              ; 1:1, OUT
0015:   EOF                             ; 0:0
```

## Output

```plain
0=10#
```

# Test: Error: calling an argless function upcall with arguments

## Source

```basic
OUT MEANING_OF_LIFE(1)
```

## Compilation errors

```plain
1:5: MEANING_OF_LIFE expected no arguments
```

# Test: Error: calling an argless function upcall with empty parens

## Source

```basic
OUT MEANING_OF_LIFE()
```

## Compilation errors

```plain
1:5: MEANING_OF_LIFE expected no arguments
```

# Test: Error: using a function upcall that requires arguments without arguments

## Source

```basic
x = SUM_DOUBLES
```

## Compilation errors

```plain
1:5: SUM_DOUBLES expected [arg1, .., argN]
```

# Test: Function name conflicts with existing global variable

## Source

```basic
DIM SHARED g AS INTEGER
FUNCTION g%
END FUNCTION
```

## Compilation errors

```plain
2:10: Cannot redefine g%
```

# Test: Function name conflicts with existing global array

## Source

```basic
DIM SHARED g(3) AS INTEGER
FUNCTION g%
END FUNCTION
```

## Compilation errors

```plain
2:10: Cannot redefine g%
```

# Test: Early function exit

## Source

```basic
FUNCTION maybe_exit(i%)
    maybe_exit = 1
    IF i > 2 THEN EXIT FUNCTION
    maybe_exit = 2
END FUNCTION

FOR i = 0 TO 5
    OUT maybe_exit(i)
NEXT
```

## Disassembly

```asm
0000:   JUMP        10                  ; 1:10

;; MAYBE_EXIT (BEGIN)
0001:   LOADI       R64, 0              ; 1:10
0002:   LOADI       R64, 1              ; 2:18
0003:   MOVE        R66, R65            ; 3:8
0004:   LOADI       R67, 2              ; 3:12
0005:   CMPGTI      R66, R66, R67       ; 3:10
0006:   JMPF        R66, 8              ; 3:8
0007:   JUMP        9                   ; 3:19
0008:   LOADI       R64, 2              ; 4:18
0009:   RETURN                          ; 5:1
;; MAYBE_EXIT (END)

0010:   LOADI       R64, 0              ; 7:9
0011:   MOVE        R65, R64            ; 7:5
0012:   LOADI       R66, 5              ; 7:14
0013:   CMPLEI      R65, R65, R66       ; 7:11
0014:   JMPF        R65, 25             ; 7:5
0015:   MOVE        R68, R64            ; 8:20
0016:   CALL        R67, 1              ; 8:9, MAYBE_EXIT
0017:   MOVE        R66, R67            ; 8:9
0018:   LOADI       R65, 258            ; 8:9
0019:   UPCALL      0, R65              ; 8:5, OUT
0020:   MOVE        R65, R64            ; 7:5
0021:   LOADI       R66, 1              ; 7:15
0022:   ADDI        R65, R65, R66       ; 7:11
0023:   MOVE        R64, R65            ; 7:5
0024:   JUMP        11                  ; 7:5
0025:   EOF                             ; 0:0
```

## Output

```plain
0=2%
0=2%
0=2%
0=1%
0=1%
0=1%
```

# Test: EXIT FUNCTION outside FUNCTION

## Source

```basic
FUNCTION a
END FUNCTION
EXIT FUNCTION
```

## Compilation errors

```plain
3:1: EXIT FUNCTION outside of FUNCTION
```

# Test: EXIT SUB in FUNCTION

## Source

```basic
FUNCTION a
    EXIT SUB
END FUNCTION
```

## Compilation errors

```plain
2:5: EXIT SUB outside of SUB
```

# Test: Recursive function

## Source

```basic
DIM SHARED calls AS INTEGER
FUNCTION factorial(n%)
    IF n = 1 THEN factorial = 1 ELSE factorial = n * factorial(n - 1)
    calls = calls + 1
END FUNCTION
OUT calls; factorial(5)
```

## Disassembly

```asm
0000:   LOADI       R0, 0               ; 1:12
0001:   JUMP        23                  ; 2:10

;; FACTORIAL (BEGIN)
0002:   LOADI       R64, 0              ; 2:10
0003:   MOVE        R66, R65            ; 3:8
0004:   LOADI       R67, 1              ; 3:12
0005:   CMPEQI      R66, R66, R67       ; 3:10
0006:   JMPF        R66, 9              ; 3:8
0007:   LOADI       R64, 1              ; 3:31
0008:   JUMP        18                  ; 3:8
0009:   LOADI       R66, 1              ; 3:33
0010:   JMPF        R66, 18             ; 3:33
0011:   MOVE        R64, R65            ; 3:50
0012:   MOVE        R68, R65            ; 3:64
0013:   LOADI       R69, 1              ; 3:68
0014:   SUBI        R68, R68, R69       ; 3:66
0015:   CALL        R67, 2              ; 3:54, FACTORIAL
0016:   MOVE        R66, R67            ; 3:54
0017:   MULI        R64, R64, R66       ; 3:52
0018:   MOVE        R66, R0             ; 4:13
0019:   LOADI       R67, 1              ; 4:21
0020:   ADDI        R66, R66, R67       ; 4:19
0021:   MOVE        R0, R66             ; 4:5
0022:   RETURN                          ; 5:1
;; FACTORIAL (END)

0023:   MOVE        R65, R0             ; 6:5
0024:   LOADI       R64, 274            ; 6:5
0025:   LOADI       R69, 5              ; 6:22
0026:   CALL        R68, 2              ; 6:12, FACTORIAL
0027:   MOVE        R67, R68            ; 6:12
0028:   LOADI       R66, 258            ; 6:12
0029:   UPCALL      0, R64              ; 6:1, OUT
0030:   EOF                             ; 0:0
```

## Output

```plain
0=0% ; 1=120%
```

# Test: Mutually recursive functions

## Source

```basic
DECLARE FUNCTION pong(n%)

FUNCTION ping(n%)
    OUT "ping"; n
    IF n = 0 THEN
        ping = 100
    ELSE
        ping = pong(n - 1) + 1
    END IF
END FUNCTION

FUNCTION pong(n%)
    OUT "pong"; n
    IF n = 0 THEN
        pong = 200
    ELSE
        pong = ping(n - 1) + 10
    END IF
END FUNCTION

OUT ping(3)
```

## Disassembly

```asm
0000:   JUMP        23                  ; 3:10

;; PING (BEGIN)
0001:   LOADI       R64, 0              ; 3:10
0002:   LOADI       R67, 0              ; 4:9
0003:   LOADI       R66, 275            ; 4:9
0004:   MOVE        R69, R65            ; 4:17
0005:   LOADI       R68, 258            ; 4:17
0006:   UPCALL      0, R66              ; 4:5, OUT
0007:   MOVE        R66, R65            ; 5:8
0008:   LOADI       R67, 0              ; 5:12
0009:   CMPEQI      R66, R66, R67       ; 5:10
0010:   JMPF        R66, 13             ; 5:8
0011:   LOADI       R64, 100            ; 6:16
0012:   JUMP        22                  ; 5:8
0013:   LOADI       R66, 1              ; 7:5
0014:   JMPF        R66, 22             ; 7:5
0015:   MOVE        R67, R65            ; 8:21
0016:   LOADI       R68, 1              ; 8:25
0017:   SUBI        R67, R67, R68       ; 8:23
0018:   CALL        R66, 24             ; 8:16, PONG
0019:   MOVE        R64, R66            ; 8:16
0020:   LOADI       R66, 1              ; 8:30
0021:   ADDI        R64, R64, R66       ; 8:28
0022:   RETURN                          ; 10:1
;; PING (END)

0023:   JUMP        46                  ; 12:10

;; PONG (BEGIN)
0024:   LOADI       R64, 0              ; 12:10
0025:   LOADI       R67, 1              ; 13:9
0026:   LOADI       R66, 275            ; 13:9
0027:   MOVE        R69, R65            ; 13:17
0028:   LOADI       R68, 258            ; 13:17
0029:   UPCALL      0, R66              ; 13:5, OUT
0030:   MOVE        R66, R65            ; 14:8
0031:   LOADI       R67, 0              ; 14:12
0032:   CMPEQI      R66, R66, R67       ; 14:10
0033:   JMPF        R66, 36             ; 14:8
0034:   LOADI       R64, 200            ; 15:16
0035:   JUMP        45                  ; 14:8
0036:   LOADI       R66, 1              ; 16:5
0037:   JMPF        R66, 45             ; 16:5
0038:   MOVE        R67, R65            ; 17:21
0039:   LOADI       R68, 1              ; 17:25
0040:   SUBI        R67, R67, R68       ; 17:23
0041:   CALL        R66, 1              ; 17:16, PING
0042:   MOVE        R64, R66            ; 17:16
0043:   LOADI       R66, 10             ; 17:30
0044:   ADDI        R64, R64, R66       ; 17:28
0045:   RETURN                          ; 19:1
;; PONG (END)

0046:   LOADI       R67, 3              ; 21:10
0047:   CALL        R66, 1              ; 21:5, PING
0048:   MOVE        R65, R66            ; 21:5
0049:   LOADI       R64, 258            ; 21:5
0050:   UPCALL      0, R64              ; 21:1, OUT
0051:   EOF                             ; 0:0
```

## Output

```plain
0=ping$ ; 1=3%
0=pong$ ; 1=2%
0=ping$ ; 1=1%
0=pong$ ; 1=0%
0=212%
```

# Test: Calling a function as a command is an error

## Source

```basic
FUNCTION f
    OUT "foo"
END FUNCTION
f
```

## Compilation errors

```plain
4:1: Cannot call F (not a function)
```

# Test: Calling a scalar as a function is an error

## Source

```basic
f = 1
OUT f()
```

## Compilation errors

```plain
2:5: Cannot call f (not a function)
```

# Test: Calling an argless function with incompatible type annotation

## Source

```basic
OUT MEANING_OF_LIFE$
```

## Compilation errors

```plain
1:5: Incompatible type annotation in MEANING_OF_LIFE$ reference
```

# Test: Calling a function with incompatible type annotation

## Source

```basic
OUT SUM_DOUBLES$(1.0, 2.0)
```

## Compilation errors

```plain
1:5: Incompatible type annotation in SUM_DOUBLES$ reference
```

# Test: Calling an argless function upcall as a command is an error

## Source

```basic
MEANING_OF_LIFE
```

## Compilation errors

```plain
1:1: Cannot call MEANING_OF_LIFE (not a function)
```

# Test: Calling a function upcall with arguments as a command is an error

## Source

```basic
SUM_DOUBLES 1.0, 2.0
```

## Compilation errors

```plain
1:1: Cannot call SUM_DOUBLES (not a function)
```

# Test: Function redefines existing function

## Source

```basic
FUNCTION foo
END FUNCTION

FUNCTION foo
END FUNCTION
```

## Compilation errors

```plain
4:10: Cannot redefine foo%
```

# Test: Function redefines existing sub

## Source

```basic
SUB foo
END SUB

FUNCTION foo
END FUNCTION
```

## Compilation errors

```plain
4:10: Cannot redefine foo%
```

# Test: Function nesting within a function

## Source

```basic
FUNCTION foo
    FUNCTION bar
    END FUNCTION
END FUNCTION
```

## Compilation errors

```plain
2:5: Cannot nest FUNCTION or SUB definitions
```

# Test: Function nesting within a sub

## Source

```basic
SUB foo
    FUNCTION bar
    END FUNCTION
END SUB
```

## Compilation errors

```plain
2:5: Cannot nest FUNCTION or SUB definitions
```

# Test: Function declarations

## Source

```basic
DECLARE FUNCTION foo
DECLARE FUNCTION foo%
DECLARE FUNCTION bar(a AS STRING)
```

## Disassembly

```asm
0000:   EOF                             ; 0:0
```

# Test: Function declarations match definition

## Source

```basic
DECLARE FUNCTION foo

FUNCTION foo
END FUNCTION

DECLARE FUNCTION foo
```

## Disassembly

```asm
0000:   JUMP        3                   ; 3:10

;; FOO (BEGIN)
0001:   LOADI       R64, 0              ; 3:10
0002:   RETURN                          ; 4:1
;; FOO (END)

0003:   EOF                             ; 0:0
```

# Test: Function declarations must be top-level

## Source

```basic

FUNCTION foo
    DECLARE FUNCTION bar
END FUNCTION
```

## Compilation errors

```plain
3:22: Cannot nest FUNCTION or SUB declarations nor definitions
```

# Test: Function pre-declaration does not match pre-definition

## Source

```basic
DECLARE FUNCTION foo

FUNCTION foo#
END FUNCTION
```

## Compilation errors

```plain
3:10: Cannot redefine foo#
```

# Test: Function post-declaration does not match definition

## Source

```basic
FUNCTION foo#
END FUNCTION

DECLARE FUNCTION foo
```

## Compilation errors

```plain
4:18: Cannot redefine foo%
```

# Test: Function declarations do not match

## Source

```basic
DECLARE FUNCTION foo
DECLARE FUNCTION foo#
```

## Compilation errors

```plain
2:18: Cannot redefine foo#
```

# Test: Function redeclared as sub

## Source

```basic
DECLARE FUNCTION foo
DECLARE SUB foo
```

## Compilation errors

```plain
2:13: Cannot redefine foo
```
