# Test: Elaborate execution flow

## Source

```basic
a = 10

SUB foo
    a = 20
    OUT "Inside", a
END SUB

OUT "Before", a
foo
OUT "After", a
```

## Disassembly

```asm
0000:   LOADI       R64, 10             ; 1:5
0001:   JUMP        9                   ; 3:5

;; FOO (BEGIN)
0002:   LOADI       R64, 20             ; 4:9
0003:   LOADI       R66, 0              ; 5:9
0004:   LOADI       R65, 291            ; 5:9
0005:   MOVE        R68, R64            ; 5:19
0006:   LOADI       R67, 258            ; 5:19
0007:   UPCALL      0, R65              ; 5:5, OUT
0008:   RETURN                          ; 6:1
;; FOO (END)

0009:   LOADI       R66, 1              ; 8:5
0010:   LOADI       R65, 291            ; 8:5
0011:   MOVE        R68, R64            ; 8:15
0012:   LOADI       R67, 258            ; 8:15
0013:   UPCALL      0, R65              ; 8:1, OUT
0014:   CALL        R65, 2              ; 9:1, FOO
0015:   LOADI       R66, 2              ; 10:5
0016:   LOADI       R65, 291            ; 10:5
0017:   MOVE        R68, R64            ; 10:14
0018:   LOADI       R67, 258            ; 10:14
0019:   UPCALL      0, R65              ; 10:1, OUT
0020:   EOF                             ; 0:0
```

## Output

```plain
0=Before$ , 1=10%
0=Inside$ , 1=20%
0=After$ , 1=10%
```

# Test: Subroutine call requires jumping backwards

## Source

```basic
SUB first
    OUT "first"
END SUB

SUB second
    first
END SUB

second
```

## Disassembly

```asm
0000:   JUMP        5                   ; 1:5

;; FIRST (BEGIN)
0001:   LOADI       R65, 0              ; 2:9
0002:   LOADI       R64, 259            ; 2:9
0003:   UPCALL      0, R64              ; 2:5, OUT
0004:   RETURN                          ; 3:1
;; FIRST (END)

0005:   JUMP        8                   ; 5:5

;; SECOND (BEGIN)
0006:   CALL        R64, 1              ; 6:5, FIRST
0007:   RETURN                          ; 7:1
;; SECOND (END)

0008:   CALL        R64, 6              ; 9:1, SECOND
0009:   EOF                             ; 0:0
```

## Output

```plain
0=first$
```

# Test: Annotation not allowed in subroutine call

## Source

```basic
OUT$ 3
```

## Compilation errors

```plain
1:1: Type annotation not allowed in OUT$
```

# Test: Local variables

## Source

```basic
SUB modify_2
    var = 2
    OUT "Inside modify_2", var
END SUB

SUB modify_1
    var = 1
    OUT "Before modify_2", var
    modify_2
    OUT "After modify_2", var
END SUB

var = 0
OUT "Before modify_1", var
modify_1
OUT "After modify_1", var
```

## Disassembly

```asm
0000:   JUMP        8                   ; 1:5

;; MODIFY_2 (BEGIN)
0001:   LOADI       R64, 2              ; 2:11
0002:   LOADI       R66, 0              ; 3:9
0003:   LOADI       R65, 291            ; 3:9
0004:   MOVE        R68, R64            ; 3:28
0005:   LOADI       R67, 258            ; 3:28
0006:   UPCALL      0, R65              ; 3:5, OUT
0007:   RETURN                          ; 4:1
;; MODIFY_2 (END)

0008:   JUMP        22                  ; 6:5

;; MODIFY_1 (BEGIN)
0009:   LOADI       R64, 1              ; 7:11
0010:   LOADI       R66, 1              ; 8:9
0011:   LOADI       R65, 291            ; 8:9
0012:   MOVE        R68, R64            ; 8:28
0013:   LOADI       R67, 258            ; 8:28
0014:   UPCALL      0, R65              ; 8:5, OUT
0015:   CALL        R65, 1              ; 9:5, MODIFY_2
0016:   LOADI       R66, 2              ; 10:9
0017:   LOADI       R65, 291            ; 10:9
0018:   MOVE        R68, R64            ; 10:27
0019:   LOADI       R67, 258            ; 10:27
0020:   UPCALL      0, R65              ; 10:5, OUT
0021:   RETURN                          ; 11:1
;; MODIFY_1 (END)

0022:   LOADI       R64, 0              ; 13:7
0023:   LOADI       R66, 3              ; 14:5
0024:   LOADI       R65, 291            ; 14:5
0025:   MOVE        R68, R64            ; 14:24
0026:   LOADI       R67, 258            ; 14:24
0027:   UPCALL      0, R65              ; 14:1, OUT
0028:   CALL        R65, 9              ; 15:1, MODIFY_1
0029:   LOADI       R66, 4              ; 16:5
0030:   LOADI       R65, 291            ; 16:5
0031:   MOVE        R68, R64            ; 16:23
0032:   LOADI       R67, 258            ; 16:23
0033:   UPCALL      0, R65              ; 16:1, OUT
0034:   EOF                             ; 0:0
```

## Output

```plain
0=Before modify_1$ , 1=0%
0=Before modify_2$ , 1=1%
0=Inside modify_2$ , 1=2%
0=After modify_2$ , 1=1%
0=After modify_1$ , 1=0%
```

# Test: Local is not global

## Source

```basic
SUB set_local
    local_var = 8
END SUB

set_local
OUT local_var
```

## Compilation errors

```plain
6:5: Undefined symbol local_var
```

# Test: Calling a command as a function with arguments

## Source

```basic
x = OUT(1)
```

## Compilation errors

```plain
1:5: OUT is not an array nor a function
```

# Test: Using a command as an argless function

## Source

```basic
x = OUT
```

## Compilation errors

```plain
1:5: OUT is not an array nor a function
```

# Test: Sub name conflicts with existing global variable

## Source

```basic
DIM SHARED g AS INTEGER
SUB g
END SUB
```

## Compilation errors

```plain
2:5: Cannot redefine g
```

# Test: Sub name conflicts with existing global array

## Source

```basic
DIM SHARED g(3) AS INTEGER
SUB g
END SUB
```

## Compilation errors

```plain
2:5: Cannot redefine g
```

# Test: Early sub exit

## Source

```basic
SUB maybe_exit(i%)
    OUT 1
    IF i > 2 THEN EXIT SUB
    OUT 2
END SUB

FOR i = 0 TO 5
    maybe_exit(i)
NEXT
```

## Disassembly

```asm
0000:   JUMP        13                  ; 1:5

;; MAYBE_EXIT (BEGIN)
0001:   LOADI       R66, 1              ; 2:9
0002:   LOADI       R65, 258            ; 2:9
0003:   UPCALL      0, R65              ; 2:5, OUT
0004:   MOVE        R65, R64            ; 3:8
0005:   LOADI       R66, 2              ; 3:12
0006:   CMPGTI      R65, R65, R66       ; 3:10
0007:   JMPF        R65, 9              ; 3:8
0008:   JUMP        12                  ; 3:19
0009:   LOADI       R66, 2              ; 4:9
0010:   LOADI       R65, 258            ; 4:9
0011:   UPCALL      0, R65              ; 4:5, OUT
0012:   RETURN                          ; 5:1
;; MAYBE_EXIT (END)

0013:   LOADI       R64, 0              ; 7:9
0014:   MOVE        R65, R64            ; 7:5
0015:   LOADI       R66, 5              ; 7:14
0016:   CMPLEI      R65, R65, R66       ; 7:11
0017:   JMPF        R65, 25             ; 7:5
0018:   MOVE        R65, R64            ; 8:16
0019:   CALL        R65, 1              ; 8:5, MAYBE_EXIT
0020:   MOVE        R65, R64            ; 7:5
0021:   LOADI       R66, 1              ; 7:15
0022:   ADDI        R65, R65, R66       ; 7:11
0023:   MOVE        R64, R65            ; 7:5
0024:   JUMP        14                  ; 7:5
0025:   EOF                             ; 0:0
```

## Output

```plain
0=1%
0=2%
0=1%
0=2%
0=1%
0=2%
0=1%
0=1%
0=1%
```

# Test: EXIT SUB outside SUB

## Source

```basic
SUB a
END SUB
EXIT SUB
```

## Compilation errors

```plain
3:1: EXIT SUB outside of SUB
```

# Test: EXIT FUNCTION in SUB

## Source

```basic
SUB a
    EXIT FUNCTION
END SUB
```

## Compilation errors

```plain
2:5: EXIT FUNCTION outside of FUNCTION
```

# Test: Recursive subroutine

## Source

```basic
DIM SHARED counter AS INTEGER
SUB count_down(prefix$)
    OUT prefix; counter
    IF counter > 1 THEN
        counter = counter - 1
        count_down prefix
    END IF
END SUB
counter = 3
count_down "counter is"
```

## Disassembly

```asm
0000:   LOADI       R0, 0               ; 1:12
0001:   JUMP        18                  ; 2:5

;; COUNT_DOWN (BEGIN)
0002:   MOVE        R66, R64            ; 3:9
0003:   LOADI       R65, 275            ; 3:9
0004:   MOVE        R68, R0             ; 3:17
0005:   LOADI       R67, 258            ; 3:17
0006:   UPCALL      0, R65              ; 3:5, OUT
0007:   MOVE        R65, R0             ; 4:8
0008:   LOADI       R66, 1              ; 4:18
0009:   CMPGTI      R65, R65, R66       ; 4:16
0010:   JMPF        R65, 17             ; 4:8
0011:   MOVE        R65, R0             ; 5:19
0012:   LOADI       R66, 1              ; 5:29
0013:   SUBI        R65, R65, R66       ; 5:27
0014:   MOVE        R0, R65             ; 5:9
0015:   MOVE        R65, R64            ; 6:20
0016:   CALL        R65, 2              ; 6:9, COUNT_DOWN
0017:   RETURN                          ; 8:1
;; COUNT_DOWN (END)

0018:   LOADI       R0, 3               ; 9:11
0019:   LOADI       R64, 0              ; 10:12
0020:   CALL        R64, 2              ; 10:1, COUNT_DOWN
0021:   EOF                             ; 0:0
```

## Output

```plain
0=counter is$ ; 1=3%
0=counter is$ ; 1=2%
0=counter is$ ; 1=1%
```

# Test: Function and subroutine call one another

## Source

```basic
DIM SHARED value AS INTEGER

DECLARE SUB bump_value(n%)

FUNCTION count_value(n%)
    value = value + 1
    IF n = 0 THEN
        count_value = value
    ELSE
        bump_value(n - 1)
        count_value = value
    END IF
END FUNCTION

SUB bump_value(n%)
    value = value + 10
    value = count_value(n)
END SUB

OUT count_value(2)
OUT value
```

## Disassembly

```asm
0000:   LOADI       R0, 0               ; 1:12
0001:   JUMP        21                  ; 5:10

;; COUNT_VALUE (BEGIN)
0002:   LOADI       R64, 0              ; 5:10
0003:   MOVE        R66, R0             ; 6:13
0004:   LOADI       R67, 1              ; 6:21
0005:   ADDI        R66, R66, R67       ; 6:19
0006:   MOVE        R0, R66             ; 6:5
0007:   MOVE        R66, R65            ; 7:8
0008:   LOADI       R67, 0              ; 7:12
0009:   CMPEQI      R66, R66, R67       ; 7:10
0010:   JMPF        R66, 13             ; 7:8
0011:   MOVE        R64, R0             ; 8:23
0012:   JUMP        20                  ; 7:8
0013:   LOADI       R66, 1              ; 9:5
0014:   JMPF        R66, 20             ; 9:5
0015:   MOVE        R66, R65            ; 10:20
0016:   LOADI       R67, 1              ; 10:24
0017:   SUBI        R66, R66, R67       ; 10:22
0018:   CALL        R66, 22             ; 10:9, BUMP_VALUE
0019:   MOVE        R64, R0             ; 11:23
0020:   RETURN                          ; 13:1
;; COUNT_VALUE (END)

0021:   JUMP        30                  ; 15:5

;; BUMP_VALUE (BEGIN)
0022:   MOVE        R65, R0             ; 16:13
0023:   LOADI       R66, 10             ; 16:21
0024:   ADDI        R65, R65, R66       ; 16:19
0025:   MOVE        R0, R65             ; 16:5
0026:   MOVE        R66, R64            ; 17:25
0027:   CALL        R65, 2              ; 17:13, COUNT_VALUE
0028:   MOVE        R0, R65             ; 17:13
0029:   RETURN                          ; 18:1
;; BUMP_VALUE (END)

0030:   LOADI       R67, 2              ; 20:17
0031:   CALL        R66, 2              ; 20:5, COUNT_VALUE
0032:   MOVE        R65, R66            ; 20:5
0033:   LOADI       R64, 258            ; 20:5
0034:   UPCALL      0, R64              ; 20:1, OUT
0035:   MOVE        R65, R0             ; 21:5
0036:   LOADI       R64, 258            ; 21:5
0037:   UPCALL      0, R64              ; 21:1, OUT
0038:   EOF                             ; 0:0
```

## Output

```plain
0=23%
0=23%
```

# Test: Calling a subroutine as a function is an error

## Source

```basic
SUB f
END SUB
OUT f
```

## Compilation errors

```plain
3:5: f is not an array nor a function
```

# Test: Sub redefines existing function

## Source

```basic
FUNCTION foo
END FUNCTION

SUB foo
END SUB
```

## Compilation errors

```plain
4:5: Cannot redefine foo
```

# Test: Sub redefines existing sub

## Source

```basic
SUB foo
END SUB

SUB foo
END SUB
```

## Compilation errors

```plain
4:5: Cannot redefine foo
```

# Test: Sub nesting within a sub

## Source

```basic
SUB foo
    SUB bar
    END SUB
END SUB
```

## Compilation errors

```plain
2:5: Cannot nest FUNCTION or SUB definitions
```

# Test: Sub nesting within a function

## Source

```basic
FUNCTION foo
    SUB bar
    END SUB
END FUNCTION
```

## Compilation errors

```plain
2:5: Cannot nest FUNCTION or SUB definitions
```

# Test: Sub declarations

## Source

```basic
DECLARE SUB foo
DECLARE SUB bar(a AS STRING)
```

## Disassembly

```asm
0000:   EOF                             ; 0:0
```

# Test: Sub declarations match definition

## Source

```basic
DECLARE SUB foo

SUB foo
END SUB

DECLARE SUB foo
```

## Disassembly

```asm
0000:   JUMP        2                   ; 3:5

;; FOO (BEGIN)
0001:   RETURN                          ; 4:1
;; FOO (END)

0002:   EOF                             ; 0:0
```

# Test: Sub declarations must be top-level

## Source

```basic

SUB foo
    SUB FUNCTION bar
END SUB
```

## Compilation errors

```plain
3:5: Cannot nest FUNCTION or SUB definitions
```

# Test: Sub pre-declaration does not match pre-definition

## Source

```basic
DECLARE SUB foo

SUB foo(a AS STRING)
END SUB
```

## Compilation errors

```plain
3:5: Cannot redefine foo
```

# Test: Sub post-declaration does not match definition

## Source

```basic
SUB foo
END SUB

DECLARE SUB foo(a AS STRING)
```

## Compilation errors

```plain
4:13: Cannot redefine foo
```

# Test: Sub declarations do not match

## Source

```basic
DECLARE SUB foo
DECLARE SUB foo(a as STRING)
```

## Compilation errors

```plain
2:13: Cannot redefine foo
```

# Test: Sub redeclared as function

## Source

```basic
DECLARE SUB foo
DECLARE FUNCTION foo
```

## Compilation errors

```plain
2:18: Cannot redefine foo%
```
