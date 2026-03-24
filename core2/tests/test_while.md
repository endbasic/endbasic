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
0000:   LOADI       R64, 3              ; 1:5
0001:   MOVE        R65, R64            ; 2:7
0002:   LOADI       R66, 0              ; 2:11
0003:   CMPGTI      R65, R65, R66       ; 2:9
0004:   JMPF        R65, 12             ; 2:7
0005:   MOVE        R66, R64            ; 3:9
0006:   LOADI       R65, 258            ; 3:9
0007:   UPCALL      0, R65              ; 3:5, OUT
0008:   MOVE        R64, R64            ; 4:9
0009:   LOADI       R65, 1              ; 4:13
0010:   SUBI        R64, R64, R65       ; 4:11
0011:   JUMP        1                   ; 2:7
0012:   EOF                             ; 0:0
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
0000:   LOADI       R64, 0              ; 1:7
0001:   JMPF        R64, 6              ; 1:7
0002:   LOADI       R65, 1              ; 2:9
0003:   LOADI       R64, 258            ; 2:9
0004:   UPCALL      0, R64              ; 2:5, OUT
0005:   JUMP        0                   ; 1:7
0006:   EOF                             ; 0:0
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
0000:   LOADI       R64, 2              ; 1:5
0001:   MOVE        R65, R64            ; 2:10
0002:   LOADI       R66, 0              ; 2:14
0003:   CMPGTI      R65, R65, R66       ; 2:12
0004:   JMPF        R65, 16             ; 2:10
0005:   LOADI       R65, 1              ; 3:11
0006:   JMPF        R65, 9              ; 3:11
0007:   JUMP        16                  ; 4:9
0008:   JUMP        5                   ; 3:11
0009:   MOVE        R66, R64            ; 6:9
0010:   LOADI       R65, 258            ; 6:9
0011:   UPCALL      0, R65              ; 6:5, OUT
0012:   MOVE        R64, R64            ; 7:9
0013:   LOADI       R65, 1              ; 7:13
0014:   SUBI        R64, R64, R65       ; 7:11
0015:   JUMP        1                   ; 2:10
0016:   LOADI       R66, 9              ; 9:5
0017:   LOADI       R65, 258            ; 9:5
0018:   UPCALL      0, R65              ; 9:1, OUT
0019:   EOF                             ; 0:0
```

## Output

```plain
0=9%
```
