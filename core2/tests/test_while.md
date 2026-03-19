# Test: WHILE loop with iterations

## Source

```basic
n = 3
WHILE n > 0
    OUT n
    n = n - 1
WEND
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R64, 3              # 1:5
0002:   MOVE        R65, R64            # 2:7
0003:   LOADI       R66, 0              # 2:11
0004:   CMPGTI      R65, R65, R66       # 2:9
0005:   JMPF        R65, 13             # 2:7
0006:   MOVE        R66, R64            # 3:9
0007:   LOADI       R65, 258            # 3:9
0008:   UPCALL      0, R65              # 3:5, OUT
0009:   MOVE        R64, R64            # 4:9
0010:   LOADI       R65, 1              # 4:13
0011:   SUBI        R64, R64, R65       # 4:11
0012:   JUMP        2                   # 2:7
0013:   EOF                             # 0:0
```

## Output

```plain
0=3%
0=2%
0=1%
```

# Test: WHILE loop with zero iterations

## Source

```basic
WHILE FALSE
    OUT 1
WEND
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADI       R64, 0              # 1:7
0002:   JMPF        R64, 7              # 1:7
0003:   LOADI       R65, 1              # 2:9
0004:   LOADI       R64, 258            # 2:9
0005:   UPCALL      0, R64              # 2:5, OUT
0006:   JUMP        1                   # 1:7
0007:   EOF                             # 0:0
```

# Test: WHILE guard must be boolean

## Source

```basic
WHILE 2
    OUT 1
WEND
```

## Compilation errors

```plain
1:7: Expected BOOLEAN but found INTEGER
```

# Test: WHILE requires an expression

## Source

```basic
WHILE
WEND
```

## Compilation errors

```plain
1:6: No expression in WHILE statement
```

# Test: WHILE requires matching WEND

## Source

```basic
WHILE TRUE
END
```

## Compilation errors

```plain
1:1: WHILE without WEND
```

# Test: EXIT DO outside DO in WHILE

## Source

```basic
WHILE TRUE
    EXIT DO
WEND
```

## Compilation errors

```plain
2:5: EXIT DO outside of DO
```

# Test: EXIT DO in WHILE nested in DO exits DO

## Source

```basic
i = 2
DO WHILE i > 0
    WHILE TRUE
        EXIT DO
    WEND
    OUT i
    i = i - 1
LOOP
OUT 9
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R64, 2              # 1:5
0002:   MOVE        R65, R64            # 2:10
0003:   LOADI       R66, 0              # 2:14
0004:   CMPGTI      R65, R65, R66       # 2:12
0005:   JMPF        R65, 17             # 2:10
0006:   LOADI       R65, 1              # 3:11
0007:   JMPF        R65, 10             # 3:11
0008:   JUMP        17                  # 4:9
0009:   JUMP        6                   # 3:11
0010:   MOVE        R66, R64            # 6:9
0011:   LOADI       R65, 258            # 6:9
0012:   UPCALL      0, R65              # 6:5, OUT
0013:   MOVE        R64, R64            # 7:9
0014:   LOADI       R65, 1              # 7:13
0015:   SUBI        R64, R64, R65       # 7:11
0016:   JUMP        2                   # 2:10
0017:   LOADI       R66, 9              # 9:5
0018:   LOADI       R65, 258            # 9:5
0019:   UPCALL      0, R65              # 9:1, OUT
0020:   EOF                             # 0:0
```

## Output

```plain
0=9%
```
