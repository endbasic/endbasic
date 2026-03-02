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
0007:   CALL        R65, 15             # 9:1, FOO
0008:   LOADI       R66, 1              # 10:5
0009:   LOADI       R65, 291            # 10:5
0010:   MOVE        R68, R64            # 10:14
0011:   LOADI       R67, 258            # 10:14
0012:   UPCALL      0, R65              # 10:1, OUT
0013:   LOADI       R65, 0              # 0:0
0014:   END         R65                 # 0:0

-- FOO 
0015:   ENTER       5                   # 0:0
0016:   LOADI       R64, 20             # 4:9
0017:   LOADI       R66, 2              # 5:9
0018:   LOADI       R65, 291            # 5:9
0019:   MOVE        R68, R64            # 5:19
0020:   LOADI       R67, 258            # 5:19
0021:   UPCALL      0, R65              # 5:5, OUT
0022:   RETURN                          # 6:1
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
0000:   ENTER       1                   # 0:0
0001:   CALL        R64, 9              # 9:1, SECOND
0002:   LOADI       R64, 0              # 0:0
0003:   END         R64                 # 0:0

-- FIRST 
0004:   ENTER       2                   # 0:0
0005:   LOADI       R65, 0              # 2:9
0006:   LOADI       R64, 259            # 2:9
0007:   UPCALL      0, R64              # 2:5, OUT
0008:   RETURN                          # 3:1

-- SECOND 
0009:   ENTER       0                   # 0:0
0010:   CALL        R64, 4              # 6:5, FIRST
0011:   RETURN                          # 7:1
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
0007:   CALL        R65, 23             # 15:1, MODIFY_1
0008:   LOADI       R66, 1              # 16:5
0009:   LOADI       R65, 291            # 16:5
0010:   MOVE        R68, R64            # 16:23
0011:   LOADI       R67, 258            # 16:23
0012:   UPCALL      0, R65              # 16:1, OUT
0013:   LOADI       R65, 0              # 0:0
0014:   END         R65                 # 0:0

-- MODIFY_2 
0015:   ENTER       5                   # 0:0
0016:   LOADI       R64, 2              # 2:11
0017:   LOADI       R66, 2              # 3:9
0018:   LOADI       R65, 291            # 3:9
0019:   MOVE        R68, R64            # 3:28
0020:   LOADI       R67, 258            # 3:28
0021:   UPCALL      0, R65              # 3:5, OUT
0022:   RETURN                          # 4:1

-- MODIFY_1 
0023:   ENTER       5                   # 0:0
0024:   LOADI       R64, 1              # 7:11
0025:   LOADI       R66, 3              # 8:9
0026:   LOADI       R65, 291            # 8:9
0027:   MOVE        R68, R64            # 8:28
0028:   LOADI       R67, 258            # 8:28
0029:   UPCALL      0, R65              # 8:5, OUT
0030:   CALL        R65, 15             # 9:5, MODIFY_2
0031:   LOADI       R66, 4              # 10:9
0032:   LOADI       R65, 291            # 10:9
0033:   MOVE        R68, R64            # 10:27
0034:   LOADI       R67, 258            # 10:27
0035:   UPCALL      0, R65              # 10:5, OUT
0036:   RETURN                          # 11:1
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
0007:   CALL        R65, 14             # 8:5, MAYBE_EXIT
0008:   MOVE        R64, R64            # 7:5
0009:   LOADI       R65, 1              # 7:15
0010:   ADDI        R64, R64, R65       # 7:11
0011:   JUMP        2                   # 7:5
0012:   LOADI       R65, 0              # 0:0
0013:   END         R65                 # 0:0

-- MAYBE_EXIT 
0014:   ENTER       3                   # 0:0
0015:   LOADI       R66, 1              # 2:9
0016:   LOADI       R65, 258            # 2:9
0017:   UPCALL      0, R65              # 2:5, OUT
0018:   MOVE        R65, R64            # 3:8
0019:   LOADI       R66, 2              # 3:12
0020:   CMPGTI      R65, R65, R66       # 3:10
0021:   JMPF        R65, 23             # 3:8
0022:   JUMP        26                  # 3:19
0023:   LOADI       R66, 2              # 4:9
0024:   LOADI       R65, 258            # 4:9
0025:   UPCALL      0, R65              # 4:5, OUT
0026:   RETURN                          # 5:1
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
