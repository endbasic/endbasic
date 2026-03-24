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
0002:   LOADI       R66, 0              # 8:5
0003:   LOADI       R65, 291            # 8:5
0004:   MOVE        R68, R64            # 8:15
0005:   LOADI       R67, 258            # 8:15
0006:   UPCALL      0, R65              # 8:1, OUT
0007:   CALL        R65, 14             # 9:1, FOO
0008:   LOADI       R66, 1              # 10:5
0009:   LOADI       R65, 291            # 10:5
0010:   MOVE        R68, R64            # 10:14
0011:   LOADI       R67, 258            # 10:14
0012:   UPCALL      0, R65              # 10:1, OUT
0013:   EOF                             # 0:0

-- FOO 
0014:   ENTER       5                   # 0:0
0015:   LOADI       R64, 20             # 4:9
0016:   LOADI       R66, 2              # 5:9
0017:   LOADI       R65, 291            # 5:9
0018:   MOVE        R68, R64            # 5:19
0019:   LOADI       R67, 258            # 5:19
0020:   UPCALL      0, R65              # 5:5, OUT
0021:   RETURN                          # 6:1
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
0001:   CALL        R64, 8              # 9:1, SECOND
0002:   EOF                             # 0:0

-- FIRST 
0003:   ENTER       2                   # 0:0
0004:   LOADI       R65, 0              # 2:9
0005:   LOADI       R64, 259            # 2:9
0006:   UPCALL      0, R64              # 2:5, OUT
0007:   RETURN                          # 3:1

-- SECOND 
0008:   ENTER       0                   # 0:0
0009:   CALL        R64, 3              # 6:5, FIRST
0010:   RETURN                          # 7:1
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
0001:   LOADI       R64, 0              # 13:7
0002:   LOADI       R66, 0              # 14:5
0003:   LOADI       R65, 291            # 14:5
0004:   MOVE        R68, R64            # 14:24
0005:   LOADI       R67, 258            # 14:24
0006:   UPCALL      0, R65              # 14:1, OUT
0007:   CALL        R65, 22             # 15:1, MODIFY_1
0008:   LOADI       R66, 1              # 16:5
0009:   LOADI       R65, 291            # 16:5
0010:   MOVE        R68, R64            # 16:23
0011:   LOADI       R67, 258            # 16:23
0012:   UPCALL      0, R65              # 16:1, OUT
0013:   EOF                             # 0:0

-- MODIFY_2 
0014:   ENTER       5                   # 0:0
0015:   LOADI       R64, 2              # 2:11
0016:   LOADI       R66, 2              # 3:9
0017:   LOADI       R65, 291            # 3:9
0018:   MOVE        R68, R64            # 3:28
0019:   LOADI       R67, 258            # 3:28
0020:   UPCALL      0, R65              # 3:5, OUT
0021:   RETURN                          # 4:1

-- MODIFY_1 
0022:   ENTER       5                   # 0:0
0023:   LOADI       R64, 1              # 7:11
0024:   LOADI       R66, 3              # 8:9
0025:   LOADI       R65, 291            # 8:9
0026:   MOVE        R68, R64            # 8:28
0027:   LOADI       R67, 258            # 8:28
0028:   UPCALL      0, R65              # 8:5, OUT
0029:   CALL        R65, 14             # 9:5, MODIFY_2
0030:   LOADI       R66, 4              # 10:9
0031:   LOADI       R65, 291            # 10:9
0032:   MOVE        R68, R64            # 10:27
0033:   LOADI       R67, 258            # 10:27
0034:   UPCALL      0, R65              # 10:5, OUT
0035:   RETURN                          # 11:1
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
0001:   LOADI       R64, 0              # 7:9
0002:   MOVE        R65, R64            # 7:5
0003:   LOADI       R66, 5              # 7:14
0004:   CMPLEI      R65, R65, R66       # 7:11
0005:   JMPF        R65, 12             # 7:5
0006:   MOVE        R65, R64            # 8:16
0007:   CALL        R65, 13             # 8:5, MAYBE_EXIT
0008:   MOVE        R64, R64            # 7:5
0009:   LOADI       R65, 1              # 7:15
0010:   ADDI        R64, R64, R65       # 7:11
0011:   JUMP        2                   # 7:5
0012:   EOF                             # 0:0

-- MAYBE_EXIT 
0013:   ENTER       3                   # 0:0
0014:   LOADI       R66, 1              # 2:9
0015:   LOADI       R65, 258            # 2:9
0016:   UPCALL      0, R65              # 2:5, OUT
0017:   MOVE        R65, R64            # 3:8
0018:   LOADI       R66, 2              # 3:12
0019:   CMPGTI      R65, R65, R66       # 3:10
0020:   JMPF        R65, 22             # 3:8
0021:   JUMP        25                  # 3:19
0022:   LOADI       R66, 2              # 4:9
0023:   LOADI       R65, 258            # 4:9
0024:   UPCALL      0, R65              # 4:5, OUT
0025:   RETURN                          # 5:1
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
0002:   LOADI       R0, 3               # 9:11
0003:   LOADI       R64, 0              # 10:12
0004:   CALL        R64, 6              # 10:1, COUNT_DOWN
0005:   EOF                             # 0:0

-- COUNT_DOWN 
0006:   ENTER       5                   # 0:0
0007:   MOVE        R66, R64            # 3:9
0008:   LOADI       R65, 275            # 3:9
0009:   MOVE        R68, R0             # 3:17
0010:   LOADI       R67, 258            # 3:17
0011:   UPCALL      0, R65              # 3:5, OUT
0012:   MOVE        R65, R0             # 4:8
0013:   LOADI       R66, 1              # 4:18
0014:   CMPGTI      R65, R65, R66       # 4:16
0015:   JMPF        R65, 21             # 4:8
0016:   MOVE        R0, R0              # 5:19
0017:   LOADI       R65, 1              # 5:29
0018:   SUBI        R0, R0, R65         # 5:27
0019:   MOVE        R65, R64            # 6:20
0020:   CALL        R65, 6              # 6:9, COUNT_DOWN
0021:   RETURN                          # 8:1
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
0002:   LOADI       R67, 2              # 18:17
0003:   CALL        R66, 11             # 18:5, COUNT_VALUE
0004:   MOVE        R65, R66            # 18:5
0005:   LOADI       R64, 258            # 18:5
0006:   UPCALL      0, R64              # 18:1, OUT
0007:   MOVE        R65, R0             # 19:5
0008:   LOADI       R64, 258            # 19:5
0009:   UPCALL      0, R64              # 19:1, OUT
0010:   EOF                             # 0:0

-- COUNT_VALUE 
0011:   LOADI       R64, 0              # 3:10
0012:   ENTER       4                   # 0:0
0013:   MOVE        R0, R0              # 4:13
0014:   LOADI       R66, 1              # 4:21
0015:   ADDI        R0, R0, R66         # 4:19
0016:   MOVE        R66, R65            # 5:8
0017:   LOADI       R67, 0              # 5:12
0018:   CMPEQI      R66, R66, R67       # 5:10
0019:   JMPF        R66, 22             # 5:8
0020:   MOVE        R64, R0             # 6:23
0021:   JUMP        29                  # 5:8
0022:   LOADI       R66, 1              # 7:5
0023:   JMPF        R66, 29             # 7:5
0024:   MOVE        R66, R65            # 8:20
0025:   LOADI       R67, 1              # 8:24
0026:   SUBI        R66, R66, R67       # 8:22
0027:   CALL        R66, 30             # 8:9, BUMP_VALUE
0028:   MOVE        R64, R0             # 9:23
0029:   RETURN                          # 11:1

-- BUMP_VALUE 
0030:   ENTER       3                   # 0:0
0031:   MOVE        R0, R0              # 14:13
0032:   LOADI       R65, 10             # 14:21
0033:   ADDI        R0, R0, R65         # 14:19
0034:   MOVE        R66, R64            # 15:25
0035:   CALL        R65, 11             # 15:13, COUNT_VALUE
0036:   MOVE        R0, R65             # 15:13
0037:   RETURN                          # 16:1
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
