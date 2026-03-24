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
0000:   ENTER       5                   # 0:0
0001:   LOADI       R64, 10             # 1:5
0002:   JUMP        11                  # 3:5

-- FOO (BEGIN)
0003:   ENTER       5                   # 0:0
0004:   LOADI       R64, 20             # 4:9
0005:   LOADI       R66, 0              # 5:9
0006:   LOADI       R65, 291            # 5:9
0007:   MOVE        R68, R64            # 5:19
0008:   LOADI       R67, 258            # 5:19
0009:   UPCALL      0, R65              # 5:5, OUT
0010:   RETURN                          # 6:1
-- FOO (END)

0011:   LOADI       R66, 1              # 8:5
0012:   LOADI       R65, 291            # 8:5
0013:   MOVE        R68, R64            # 8:15
0014:   LOADI       R67, 258            # 8:15
0015:   UPCALL      0, R65              # 8:1, OUT
0016:   CALL        R65, 3              # 9:1, FOO
0017:   LOADI       R66, 2              # 10:5
0018:   LOADI       R65, 291            # 10:5
0019:   MOVE        R68, R64            # 10:14
0020:   LOADI       R67, 258            # 10:14
0021:   UPCALL      0, R65              # 10:1, OUT
0022:   EOF                             # 0:0
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
0000:   ENTER       0                   # 0:0
0001:   JUMP        7                   # 1:5

-- FIRST (BEGIN)
0002:   ENTER       2                   # 0:0
0003:   LOADI       R65, 0              # 2:9
0004:   LOADI       R64, 259            # 2:9
0005:   UPCALL      0, R64              # 2:5, OUT
0006:   RETURN                          # 3:1
-- FIRST (END)

0007:   JUMP        11                  # 5:5

-- SECOND (BEGIN)
0008:   ENTER       0                   # 0:0
0009:   CALL        R64, 2              # 6:5, FIRST
0010:   RETURN                          # 7:1
-- SECOND (END)

0011:   CALL        R64, 8              # 9:1, SECOND
0012:   EOF                             # 0:0
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
0000:   ENTER       5                   # 0:0
0001:   JUMP        10                  # 1:5

-- MODIFY_2 (BEGIN)
0002:   ENTER       5                   # 0:0
0003:   LOADI       R64, 2              # 2:11
0004:   LOADI       R66, 0              # 3:9
0005:   LOADI       R65, 291            # 3:9
0006:   MOVE        R68, R64            # 3:28
0007:   LOADI       R67, 258            # 3:28
0008:   UPCALL      0, R65              # 3:5, OUT
0009:   RETURN                          # 4:1
-- MODIFY_2 (END)

0010:   JUMP        25                  # 6:5

-- MODIFY_1 (BEGIN)
0011:   ENTER       5                   # 0:0
0012:   LOADI       R64, 1              # 7:11
0013:   LOADI       R66, 1              # 8:9
0014:   LOADI       R65, 291            # 8:9
0015:   MOVE        R68, R64            # 8:28
0016:   LOADI       R67, 258            # 8:28
0017:   UPCALL      0, R65              # 8:5, OUT
0018:   CALL        R65, 2              # 9:5, MODIFY_2
0019:   LOADI       R66, 2              # 10:9
0020:   LOADI       R65, 291            # 10:9
0021:   MOVE        R68, R64            # 10:27
0022:   LOADI       R67, 258            # 10:27
0023:   UPCALL      0, R65              # 10:5, OUT
0024:   RETURN                          # 11:1
-- MODIFY_1 (END)

0025:   LOADI       R64, 0              # 13:7
0026:   LOADI       R66, 3              # 14:5
0027:   LOADI       R65, 291            # 14:5
0028:   MOVE        R68, R64            # 14:24
0029:   LOADI       R67, 258            # 14:24
0030:   UPCALL      0, R65              # 14:1, OUT
0031:   CALL        R65, 11             # 15:1, MODIFY_1
0032:   LOADI       R66, 4              # 16:5
0033:   LOADI       R65, 291            # 16:5
0034:   MOVE        R68, R64            # 16:23
0035:   LOADI       R67, 258            # 16:23
0036:   UPCALL      0, R65              # 16:1, OUT
0037:   EOF                             # 0:0
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
6:5: Undefined global symbol local_var
```

# Test: Calling a command as a function with arguments

## Source

```basic
x = OUT(1)
```

## Compilation errors

```plain
1:5: Cannot call OUT (not a function)
```

# Test: Using a command as an argless function

## Source

```basic
x = OUT
```

## Compilation errors

```plain
1:5: Cannot call OUT (not a function)
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
0000:   ENTER       3                   # 0:0
0001:   JUMP        15                  # 1:5

-- MAYBE_EXIT (BEGIN)
0002:   ENTER       3                   # 0:0
0003:   LOADI       R66, 1              # 2:9
0004:   LOADI       R65, 258            # 2:9
0005:   UPCALL      0, R65              # 2:5, OUT
0006:   MOVE        R65, R64            # 3:8
0007:   LOADI       R66, 2              # 3:12
0008:   CMPGTI      R65, R65, R66       # 3:10
0009:   JMPF        R65, 11             # 3:8
0010:   JUMP        14                  # 3:19
0011:   LOADI       R66, 2              # 4:9
0012:   LOADI       R65, 258            # 4:9
0013:   UPCALL      0, R65              # 4:5, OUT
0014:   RETURN                          # 5:1
-- MAYBE_EXIT (END)

0015:   LOADI       R64, 0              # 7:9
0016:   MOVE        R65, R64            # 7:5
0017:   LOADI       R66, 5              # 7:14
0018:   CMPLEI      R65, R65, R66       # 7:11
0019:   JMPF        R65, 26             # 7:5
0020:   MOVE        R65, R64            # 8:16
0021:   CALL        R65, 2              # 8:5, MAYBE_EXIT
0022:   MOVE        R64, R64            # 7:5
0023:   LOADI       R65, 1              # 7:15
0024:   ADDI        R64, R64, R65       # 7:11
0025:   JUMP        16                  # 7:5
0026:   EOF                             # 0:0
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
0000:   ENTER       1                   # 0:0
0001:   LOADI       R0, 0               # 1:12
0002:   JUMP        19                  # 2:5

-- COUNT_DOWN (BEGIN)
0003:   ENTER       5                   # 0:0
0004:   MOVE        R66, R64            # 3:9
0005:   LOADI       R65, 275            # 3:9
0006:   MOVE        R68, R0             # 3:17
0007:   LOADI       R67, 258            # 3:17
0008:   UPCALL      0, R65              # 3:5, OUT
0009:   MOVE        R65, R0             # 4:8
0010:   LOADI       R66, 1              # 4:18
0011:   CMPGTI      R65, R65, R66       # 4:16
0012:   JMPF        R65, 18             # 4:8
0013:   MOVE        R0, R0              # 5:19
0014:   LOADI       R65, 1              # 5:29
0015:   SUBI        R0, R0, R65         # 5:27
0016:   MOVE        R65, R64            # 6:20
0017:   CALL        R65, 3              # 6:9, COUNT_DOWN
0018:   RETURN                          # 8:1
-- COUNT_DOWN (END)

0019:   LOADI       R0, 3               # 9:11
0020:   LOADI       R64, 0              # 10:12
0021:   CALL        R64, 3              # 10:1, COUNT_DOWN
0022:   EOF                             # 0:0
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
0000:   ENTER       4                   # 0:0
0001:   LOADI       R0, 0               # 1:12
0002:   JUMP        22                  # 5:10

-- COUNT_VALUE (BEGIN)
0003:   LOADI       R64, 0              # 5:10
0004:   ENTER       4                   # 0:0
0005:   MOVE        R0, R0              # 6:13
0006:   LOADI       R66, 1              # 6:21
0007:   ADDI        R0, R0, R66         # 6:19
0008:   MOVE        R66, R65            # 7:8
0009:   LOADI       R67, 0              # 7:12
0010:   CMPEQI      R66, R66, R67       # 7:10
0011:   JMPF        R66, 14             # 7:8
0012:   MOVE        R64, R0             # 8:23
0013:   JUMP        21                  # 7:8
0014:   LOADI       R66, 1              # 9:5
0015:   JMPF        R66, 21             # 9:5
0016:   MOVE        R66, R65            # 10:20
0017:   LOADI       R67, 1              # 10:24
0018:   SUBI        R66, R66, R67       # 10:22
0019:   CALL        R66, 23             # 10:9, BUMP_VALUE
0020:   MOVE        R64, R0             # 11:23
0021:   RETURN                          # 13:1
-- COUNT_VALUE (END)

0022:   JUMP        31                  # 15:5

-- BUMP_VALUE (BEGIN)
0023:   ENTER       3                   # 0:0
0024:   MOVE        R0, R0              # 16:13
0025:   LOADI       R65, 10             # 16:21
0026:   ADDI        R0, R0, R65         # 16:19
0027:   MOVE        R66, R64            # 17:25
0028:   CALL        R65, 3              # 17:13, COUNT_VALUE
0029:   MOVE        R0, R65             # 17:13
0030:   RETURN                          # 18:1
-- BUMP_VALUE (END)

0031:   LOADI       R67, 2              # 20:17
0032:   CALL        R66, 3              # 20:5, COUNT_VALUE
0033:   MOVE        R65, R66            # 20:5
0034:   LOADI       R64, 258            # 20:5
0035:   UPCALL      0, R64              # 20:1, OUT
0036:   MOVE        R65, R0             # 21:5
0037:   LOADI       R64, 258            # 21:5
0038:   UPCALL      0, R64              # 21:1, OUT
0039:   EOF                             # 0:0
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
3:5: Cannot call f (not a function)
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
0000:   ENTER       0                   # 0:0
0001:   EOF                             # 0:0
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
0000:   ENTER       0                   # 0:0
0001:   JUMP        4                   # 3:5

-- FOO (BEGIN)
0002:   ENTER       0                   # 0:0
0003:   RETURN                          # 4:1
-- FOO (END)

0004:   EOF                             # 0:0
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
