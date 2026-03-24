# Test: Infinite DO with EXIT DO

## Source

```basic
DO
    OUT "start"
    EXIT DO
    OUT "after"
LOOP
```

## Disassembly

```asm
0000:   LOADI       R65, 0              ; 2:9
0001:   LOADI       R64, 259            ; 2:9
0002:   UPCALL      0, R64              ; 2:5, OUT
0003:   JUMP        8                   ; 3:5
0004:   LOADI       R65, 1              ; 4:9
0005:   LOADI       R64, 259            ; 4:9
0006:   UPCALL      0, R64              ; 4:5, OUT
0007:   JUMP        0                   ; 0:0
0008:   EOF                             ; 0:0
```

## Output

```plain
0=start$
```

# Test: Pre UNTIL DO loop with zero iterations

## Source

```basic
n = 0
DO UNTIL n = 0
    OUT n
    n = n - 1
LOOP
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:5
0001:   MOVE        R65, R64            ; 2:10
0002:   LOADI       R66, 0              ; 2:14
0003:   CMPEQI      R65, R65, R66       ; 2:12
0004:   JMPF        R65, 6              ; 2:10
0005:   JUMP        13                  ; 2:10
0006:   MOVE        R66, R64            ; 3:9
0007:   LOADI       R65, 258            ; 3:9
0008:   UPCALL      0, R65              ; 3:5, OUT
0009:   MOVE        R64, R64            ; 4:9
0010:   LOADI       R65, 1              ; 4:13
0011:   SUBI        R64, R64, R65       ; 4:11
0012:   JUMP        1                   ; 2:10
0013:   EOF                             ; 0:0
```

# Test: Pre UNTIL DO loop with iterations

## Source

```basic
n = 3
DO UNTIL n = 0
    OUT n
    n = n - 1
LOOP
```

## Disassembly

```asm
0000:   LOADI       R64, 3              ; 1:5
0001:   MOVE        R65, R64            ; 2:10
0002:   LOADI       R66, 0              ; 2:14
0003:   CMPEQI      R65, R65, R66       ; 2:12
0004:   JMPF        R65, 6              ; 2:10
0005:   JUMP        13                  ; 2:10
0006:   MOVE        R66, R64            ; 3:9
0007:   LOADI       R65, 258            ; 3:9
0008:   UPCALL      0, R65              ; 3:5, OUT
0009:   MOVE        R64, R64            ; 4:9
0010:   LOADI       R65, 1              ; 4:13
0011:   SUBI        R64, R64, R65       ; 4:11
0012:   JUMP        1                   ; 2:10
0013:   EOF                             ; 0:0
```

## Output

```plain
0=3%
0=2%
0=1%
```

# Test: Pre WHILE DO loop with zero iterations

## Source

```basic
n = 0
DO WHILE n > 0
    OUT n
    n = n - 1
LOOP
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:5
0001:   MOVE        R65, R64            ; 2:10
0002:   LOADI       R66, 0              ; 2:14
0003:   CMPGTI      R65, R65, R66       ; 2:12
0004:   JMPF        R65, 12             ; 2:10
0005:   MOVE        R66, R64            ; 3:9
0006:   LOADI       R65, 258            ; 3:9
0007:   UPCALL      0, R65              ; 3:5, OUT
0008:   MOVE        R64, R64            ; 4:9
0009:   LOADI       R65, 1              ; 4:13
0010:   SUBI        R64, R64, R65       ; 4:11
0011:   JUMP        1                   ; 2:10
0012:   EOF                             ; 0:0
```

# Test: Pre WHILE DO loop with iterations

## Source

```basic
n = 3
DO WHILE n > 0
    OUT n
    n = n - 1
LOOP
```

## Disassembly

```asm
0000:   LOADI       R64, 3              ; 1:5
0001:   MOVE        R65, R64            ; 2:10
0002:   LOADI       R66, 0              ; 2:14
0003:   CMPGTI      R65, R65, R66       ; 2:12
0004:   JMPF        R65, 12             ; 2:10
0005:   MOVE        R66, R64            ; 3:9
0006:   LOADI       R65, 258            ; 3:9
0007:   UPCALL      0, R65              ; 3:5, OUT
0008:   MOVE        R64, R64            ; 4:9
0009:   LOADI       R65, 1              ; 4:13
0010:   SUBI        R64, R64, R65       ; 4:11
0011:   JUMP        1                   ; 2:10
0012:   EOF                             ; 0:0
```

## Output

```plain
0=3%
0=2%
0=1%
```

# Test: Post UNTIL DO loop with single iteration

## Source

```basic
n = 1
DO
    OUT n
    n = n - 1
LOOP UNTIL n = 0
```

## Disassembly

```asm
0000:   LOADI       R64, 1              ; 1:5
0001:   MOVE        R66, R64            ; 3:9
0002:   LOADI       R65, 258            ; 3:9
0003:   UPCALL      0, R65              ; 3:5, OUT
0004:   MOVE        R64, R64            ; 4:9
0005:   LOADI       R65, 1              ; 4:13
0006:   SUBI        R64, R64, R65       ; 4:11
0007:   MOVE        R65, R64            ; 5:12
0008:   LOADI       R66, 0              ; 5:16
0009:   CMPEQI      R65, R65, R66       ; 5:14
0010:   JMPF        R65, 1              ; 5:12
0011:   EOF                             ; 0:0
```

## Output

```plain
0=1%
```

# Test: Post UNTIL DO loop with iterations

## Source

```basic
n = 3
DO
    OUT n
    n = n - 1
LOOP UNTIL n = 0
```

## Disassembly

```asm
0000:   LOADI       R64, 3              ; 1:5
0001:   MOVE        R66, R64            ; 3:9
0002:   LOADI       R65, 258            ; 3:9
0003:   UPCALL      0, R65              ; 3:5, OUT
0004:   MOVE        R64, R64            ; 4:9
0005:   LOADI       R65, 1              ; 4:13
0006:   SUBI        R64, R64, R65       ; 4:11
0007:   MOVE        R65, R64            ; 5:12
0008:   LOADI       R66, 0              ; 5:16
0009:   CMPEQI      R65, R65, R66       ; 5:14
0010:   JMPF        R65, 1              ; 5:12
0011:   EOF                             ; 0:0
```

## Output

```plain
0=3%
0=2%
0=1%
```

# Test: Post WHILE DO loop with single iteration

## Source

```basic
n = 1
DO
    OUT n
    n = n - 1
LOOP WHILE n > 0
```

## Disassembly

```asm
0000:   LOADI       R64, 1              ; 1:5
0001:   MOVE        R66, R64            ; 3:9
0002:   LOADI       R65, 258            ; 3:9
0003:   UPCALL      0, R65              ; 3:5, OUT
0004:   MOVE        R64, R64            ; 4:9
0005:   LOADI       R65, 1              ; 4:13
0006:   SUBI        R64, R64, R65       ; 4:11
0007:   MOVE        R65, R64            ; 5:12
0008:   LOADI       R66, 0              ; 5:16
0009:   CMPGTI      R65, R65, R66       ; 5:14
0010:   JMPF        R65, 12             ; 5:12
0011:   JUMP        1                   ; 5:12
0012:   EOF                             ; 0:0
```

## Output

```plain
0=1%
```

# Test: Post WHILE DO loop with iterations

## Source

```basic
n = 3
DO
    OUT n
    n = n - 1
LOOP WHILE n > 0
```

## Disassembly

```asm
0000:   LOADI       R64, 3              ; 1:5
0001:   MOVE        R66, R64            ; 3:9
0002:   LOADI       R65, 258            ; 3:9
0003:   UPCALL      0, R65              ; 3:5, OUT
0004:   MOVE        R64, R64            ; 4:9
0005:   LOADI       R65, 1              ; 4:13
0006:   SUBI        R64, R64, R65       ; 4:11
0007:   MOVE        R65, R64            ; 5:12
0008:   LOADI       R66, 0              ; 5:16
0009:   CMPGTI      R65, R65, R66       ; 5:14
0010:   JMPF        R65, 12             ; 5:12
0011:   JUMP        1                   ; 5:12
0012:   EOF                             ; 0:0
```

## Output

```plain
0=3%
0=2%
0=1%
```

# Test: Nested DO loops with EXIT DO

## Source

```basic
i = 3
DO WHILE i > 0
    j = 2
    DO UNTIL j = 0
        OUT i; j
        IF i = 2 AND j = 2 THEN: EXIT DO: END IF
        j = j - 1
    LOOP
    IF i = 1 THEN: EXIT DO: END IF
    i = i - 1
LOOP
```

## Disassembly

```asm
0000:   LOADI       R64, 3              ; 1:5
0001:   MOVE        R65, R64            ; 2:10
0002:   LOADI       R66, 0              ; 2:14
0003:   CMPGTI      R65, R65, R66       ; 2:12
0004:   JMPF        R65, 38             ; 2:10
0005:   LOADI       R65, 2              ; 3:9
0006:   MOVE        R66, R65            ; 4:14
0007:   LOADI       R67, 0              ; 4:18
0008:   CMPEQI      R66, R66, R67       ; 4:16
0009:   JMPF        R66, 11             ; 4:14
0010:   JUMP        29                  ; 4:14
0011:   MOVE        R67, R64            ; 5:13
0012:   LOADI       R66, 274            ; 5:13
0013:   MOVE        R69, R65            ; 5:16
0014:   LOADI       R68, 258            ; 5:16
0015:   UPCALL      0, R66              ; 5:9, OUT
0016:   MOVE        R66, R64            ; 6:12
0017:   LOADI       R67, 2              ; 6:16
0018:   CMPEQI      R66, R66, R67       ; 6:14
0019:   MOVE        R67, R65            ; 6:22
0020:   LOADI       R68, 2              ; 6:26
0021:   CMPEQI      R67, R67, R68       ; 6:24
0022:   AND         R66, R66, R67       ; 6:18
0023:   JMPF        R66, 25             ; 6:12
0024:   JUMP        29                  ; 6:34
0025:   MOVE        R65, R65            ; 7:13
0026:   LOADI       R66, 1              ; 7:17
0027:   SUBI        R65, R65, R66       ; 7:15
0028:   JUMP        6                   ; 4:14
0029:   MOVE        R66, R64            ; 9:8
0030:   LOADI       R67, 1              ; 9:12
0031:   CMPEQI      R66, R66, R67       ; 9:10
0032:   JMPF        R66, 34             ; 9:8
0033:   JUMP        38                  ; 9:20
0034:   MOVE        R64, R64            ; 10:9
0035:   LOADI       R66, 1              ; 10:13
0036:   SUBI        R64, R64, R66       ; 10:11
0037:   JUMP        1                   ; 2:10
0038:   EOF                             ; 0:0
```

## Output

```plain
0=3% ; 1=2%
0=3% ; 1=1%
0=2% ; 1=2%
0=1% ; 1=2%
0=1% ; 1=1%
```

# Test: Nested DO loop EXIT DO exits inner only

## Source

```basic
i = 2
DO WHILE i > 0
    j = 3
    DO WHILE j > 0
        OUT i; j
        EXIT DO
        j = j - 1
    LOOP
    OUT "after"; i
    i = i - 1
LOOP
```

## Disassembly

```asm
0000:   LOADI       R64, 2              ; 1:5
0001:   MOVE        R65, R64            ; 2:10
0002:   LOADI       R66, 0              ; 2:14
0003:   CMPGTI      R65, R65, R66       ; 2:12
0004:   JMPF        R65, 29             ; 2:10
0005:   LOADI       R65, 3              ; 3:9
0006:   MOVE        R66, R65            ; 4:14
0007:   LOADI       R67, 0              ; 4:18
0008:   CMPGTI      R66, R66, R67       ; 4:16
0009:   JMPF        R66, 20             ; 4:14
0010:   MOVE        R67, R64            ; 5:13
0011:   LOADI       R66, 274            ; 5:13
0012:   MOVE        R69, R65            ; 5:16
0013:   LOADI       R68, 258            ; 5:16
0014:   UPCALL      0, R66              ; 5:9, OUT
0015:   JUMP        20                  ; 6:9
0016:   MOVE        R65, R65            ; 7:13
0017:   LOADI       R66, 1              ; 7:17
0018:   SUBI        R65, R65, R66       ; 7:15
0019:   JUMP        6                   ; 4:14
0020:   LOADI       R67, 0              ; 9:9
0021:   LOADI       R66, 275            ; 9:9
0022:   MOVE        R69, R64            ; 9:18
0023:   LOADI       R68, 258            ; 9:18
0024:   UPCALL      0, R66              ; 9:5, OUT
0025:   MOVE        R64, R64            ; 10:9
0026:   LOADI       R66, 1              ; 10:13
0027:   SUBI        R64, R64, R66       ; 10:11
0028:   JUMP        1                   ; 2:10
0029:   EOF                             ; 0:0
```

## Output

```plain
0=2% ; 1=3%
0=after$ ; 1=2%
0=1% ; 1=3%
0=after$ ; 1=1%
```

# Test: Nested DO loop with multiple EXIT DO

## Source

```basic
i = 2
DO WHILE i > 0
    j = 2
    DO WHILE j > 0
        IF i = 2 THEN: EXIT DO: END IF
        IF j = 1 THEN: EXIT DO: END IF
        j = j - 1
    LOOP
    OUT i
    i = i - 1
LOOP
```

## Disassembly

```asm
0000:   LOADI       R64, 2              ; 1:5
0001:   MOVE        R65, R64            ; 2:10
0002:   LOADI       R66, 0              ; 2:14
0003:   CMPGTI      R65, R65, R66       ; 2:12
0004:   JMPF        R65, 31             ; 2:10
0005:   LOADI       R65, 2              ; 3:9
0006:   MOVE        R66, R65            ; 4:14
0007:   LOADI       R67, 0              ; 4:18
0008:   CMPGTI      R66, R66, R67       ; 4:16
0009:   JMPF        R66, 24             ; 4:14
0010:   MOVE        R66, R64            ; 5:12
0011:   LOADI       R67, 2              ; 5:16
0012:   CMPEQI      R66, R66, R67       ; 5:14
0013:   JMPF        R66, 15             ; 5:12
0014:   JUMP        24                  ; 5:24
0015:   MOVE        R66, R65            ; 6:12
0016:   LOADI       R67, 1              ; 6:16
0017:   CMPEQI      R66, R66, R67       ; 6:14
0018:   JMPF        R66, 20             ; 6:12
0019:   JUMP        24                  ; 6:24
0020:   MOVE        R65, R65            ; 7:13
0021:   LOADI       R66, 1              ; 7:17
0022:   SUBI        R65, R65, R66       ; 7:15
0023:   JUMP        6                   ; 4:14
0024:   MOVE        R67, R64            ; 9:9
0025:   LOADI       R66, 258            ; 9:9
0026:   UPCALL      0, R66              ; 9:5, OUT
0027:   MOVE        R64, R64            ; 10:9
0028:   LOADI       R66, 1              ; 10:13
0029:   SUBI        R64, R64, R66       ; 10:11
0030:   JUMP        1                   ; 2:10
0031:   EOF                             ; 0:0
```

## Output

```plain
0=2%
0=1%
```

# Test: Nested DO with inner post guard EXIT DO

## Source

```basic
i = 2
DO WHILE i > 0
    j = 2
    DO
        OUT i; j
        EXIT DO
        j = j - 1
    LOOP UNTIL j = 0
    i = i - 1
LOOP
```

## Disassembly

```asm
0000:   LOADI       R64, 2              ; 1:5
0001:   MOVE        R65, R64            ; 2:10
0002:   LOADI       R66, 0              ; 2:14
0003:   CMPGTI      R65, R65, R66       ; 2:12
0004:   JMPF        R65, 23             ; 2:10
0005:   LOADI       R65, 2              ; 3:9
0006:   MOVE        R67, R64            ; 5:13
0007:   LOADI       R66, 274            ; 5:13
0008:   MOVE        R69, R65            ; 5:16
0009:   LOADI       R68, 258            ; 5:16
0010:   UPCALL      0, R66              ; 5:9, OUT
0011:   JUMP        19                  ; 6:9
0012:   MOVE        R65, R65            ; 7:13
0013:   LOADI       R66, 1              ; 7:17
0014:   SUBI        R65, R65, R66       ; 7:15
0015:   MOVE        R66, R65            ; 8:16
0016:   LOADI       R67, 0              ; 8:20
0017:   CMPEQI      R66, R66, R67       ; 8:18
0018:   JMPF        R66, 6              ; 8:16
0019:   MOVE        R64, R64            ; 9:9
0020:   LOADI       R66, 1              ; 9:13
0021:   SUBI        R64, R64, R66       ; 9:11
0022:   JUMP        1                   ; 2:10
0023:   EOF                             ; 0:0
```

## Output

```plain
0=2% ; 1=2%
0=1% ; 1=2%
```

# Test: Nested DO with inner infinite EXIT DO

## Source

```basic
i = 2
DO WHILE i > 0
    j = 1
    DO
        OUT i; j
        EXIT DO
    LOOP
    i = i - 1
LOOP
```

## Disassembly

```asm
0000:   LOADI       R64, 2              ; 1:5
0001:   MOVE        R65, R64            ; 2:10
0002:   LOADI       R66, 0              ; 2:14
0003:   CMPGTI      R65, R65, R66       ; 2:12
0004:   JMPF        R65, 17             ; 2:10
0005:   LOADI       R65, 1              ; 3:9
0006:   MOVE        R67, R64            ; 5:13
0007:   LOADI       R66, 274            ; 5:13
0008:   MOVE        R69, R65            ; 5:16
0009:   LOADI       R68, 258            ; 5:16
0010:   UPCALL      0, R66              ; 5:9, OUT
0011:   JUMP        13                  ; 6:9
0012:   JUMP        6                   ; 0:0
0013:   MOVE        R64, R64            ; 8:9
0014:   LOADI       R66, 1              ; 8:13
0015:   SUBI        R64, R64, R66       ; 8:11
0016:   JUMP        1                   ; 2:10
0017:   EOF                             ; 0:0
```

## Output

```plain
0=2% ; 1=1%
0=1% ; 1=1%
```

# Test: Nested DO with single-line EXIT DO

## Source

```basic
i = 2
DO WHILE i > 0
    j = 2
    DO WHILE j > 0: OUT i; j: EXIT DO: j = j - 1: LOOP
    OUT "after"; i
    i = i - 1
LOOP
```

## Disassembly

```asm
0000:   LOADI       R64, 2              ; 1:5
0001:   MOVE        R65, R64            ; 2:10
0002:   LOADI       R66, 0              ; 2:14
0003:   CMPGTI      R65, R65, R66       ; 2:12
0004:   JMPF        R65, 29             ; 2:10
0005:   LOADI       R65, 2              ; 3:9
0006:   MOVE        R66, R65            ; 4:14
0007:   LOADI       R67, 0              ; 4:18
0008:   CMPGTI      R66, R66, R67       ; 4:16
0009:   JMPF        R66, 20             ; 4:14
0010:   MOVE        R67, R64            ; 4:25
0011:   LOADI       R66, 274            ; 4:25
0012:   MOVE        R69, R65            ; 4:28
0013:   LOADI       R68, 258            ; 4:28
0014:   UPCALL      0, R66              ; 4:21, OUT
0015:   JUMP        20                  ; 4:31
0016:   MOVE        R65, R65            ; 4:44
0017:   LOADI       R66, 1              ; 4:48
0018:   SUBI        R65, R65, R66       ; 4:46
0019:   JUMP        6                   ; 4:14
0020:   LOADI       R67, 0              ; 5:9
0021:   LOADI       R66, 275            ; 5:9
0022:   MOVE        R69, R64            ; 5:18
0023:   LOADI       R68, 258            ; 5:18
0024:   UPCALL      0, R66              ; 5:5, OUT
0025:   MOVE        R64, R64            ; 6:9
0026:   LOADI       R66, 1              ; 6:13
0027:   SUBI        R64, R64, R66       ; 6:11
0028:   JUMP        1                   ; 2:10
0029:   EOF                             ; 0:0
```

## Output

```plain
0=2% ; 1=2%
0=after$ ; 1=2%
0=1% ; 1=2%
0=after$ ; 1=1%
```

# Test: Sequential DO loops with EXIT DO

## Source

```basic
i = 2
DO WHILE i > 0
    OUT "First"; i
    i = i - 1
LOOP

i = 2
DO WHILE i > 0
    OUT "Second"; i
    i = i - 1
LOOP
```

## Disassembly

```asm
0000:   LOADI       R64, 2              ; 1:5
0001:   MOVE        R65, R64            ; 2:10
0002:   LOADI       R66, 0              ; 2:14
0003:   CMPGTI      R65, R65, R66       ; 2:12
0004:   JMPF        R65, 14             ; 2:10
0005:   LOADI       R66, 0              ; 3:9
0006:   LOADI       R65, 275            ; 3:9
0007:   MOVE        R68, R64            ; 3:18
0008:   LOADI       R67, 258            ; 3:18
0009:   UPCALL      0, R65              ; 3:5, OUT
0010:   MOVE        R64, R64            ; 4:9
0011:   LOADI       R65, 1              ; 4:13
0012:   SUBI        R64, R64, R65       ; 4:11
0013:   JUMP        1                   ; 2:10
0014:   LOADI       R64, 2              ; 7:5
0015:   MOVE        R65, R64            ; 8:10
0016:   LOADI       R66, 0              ; 8:14
0017:   CMPGTI      R65, R65, R66       ; 8:12
0018:   JMPF        R65, 28             ; 8:10
0019:   LOADI       R66, 1              ; 9:9
0020:   LOADI       R65, 275            ; 9:9
0021:   MOVE        R68, R64            ; 9:19
0022:   LOADI       R67, 258            ; 9:19
0023:   UPCALL      0, R65              ; 9:5, OUT
0024:   MOVE        R64, R64            ; 10:9
0025:   LOADI       R65, 1              ; 10:13
0026:   SUBI        R64, R64, R65       ; 10:11
0027:   JUMP        15                  ; 8:10
0028:   EOF                             ; 0:0
```

## Output

```plain
0=First$ ; 1=2%
0=First$ ; 1=1%
0=Second$ ; 1=2%
0=Second$ ; 1=1%
```

# Test: EXIT DO from nested subroutine DO loop

## Source

```basic
i = 3
DO WHILE i > 0
    GOSUB @another
    IF i = 1 THEN: EXIT DO: END IF
    i = i - 1
LOOP
GOTO @end
@another
j = 2
DO UNTIL j = 0
    OUT i; j
    IF i = 2 AND j = 2 THEN: EXIT DO: END IF
    j = j - 1
LOOP
RETURN
@end
```

## Disassembly

```asm
0000:   LOADI       R64, 3              ; 1:5
0001:   MOVE        R65, R64            ; 2:10
0002:   LOADI       R66, 0              ; 2:14
0003:   CMPGTI      R65, R65, R66       ; 2:12
0004:   JMPF        R65, 15             ; 2:10
0005:   GOSUB       16                  ; 3:11
0006:   MOVE        R65, R64            ; 4:8
0007:   LOADI       R66, 1              ; 4:12
0008:   CMPEQI      R65, R65, R66       ; 4:10
0009:   JMPF        R65, 11             ; 4:8
0010:   JUMP        15                  ; 4:20
0011:   MOVE        R64, R64            ; 5:9
0012:   LOADI       R65, 1              ; 5:13
0013:   SUBI        R64, R64, R65       ; 5:11
0014:   JUMP        1                   ; 2:10
0015:   JUMP        41                  ; 7:6
0016:   LOADI       R65, 2              ; 9:5
0017:   MOVE        R66, R65            ; 10:10
0018:   LOADI       R67, 0              ; 10:14
0019:   CMPEQI      R66, R66, R67       ; 10:12
0020:   JMPF        R66, 22             ; 10:10
0021:   JUMP        40                  ; 10:10
0022:   MOVE        R67, R64            ; 11:9
0023:   LOADI       R66, 274            ; 11:9
0024:   MOVE        R69, R65            ; 11:12
0025:   LOADI       R68, 258            ; 11:12
0026:   UPCALL      0, R66              ; 11:5, OUT
0027:   MOVE        R66, R64            ; 12:8
0028:   LOADI       R67, 2              ; 12:12
0029:   CMPEQI      R66, R66, R67       ; 12:10
0030:   MOVE        R67, R65            ; 12:18
0031:   LOADI       R68, 2              ; 12:22
0032:   CMPEQI      R67, R67, R68       ; 12:20
0033:   AND         R66, R66, R67       ; 12:14
0034:   JMPF        R66, 36             ; 12:8
0035:   JUMP        40                  ; 12:30
0036:   MOVE        R65, R65            ; 13:9
0037:   LOADI       R66, 1              ; 13:13
0038:   SUBI        R65, R65, R66       ; 13:11
0039:   JUMP        17                  ; 10:10
0040:   RETURN                          ; 15:1
0041:   EOF                             ; 0:0
```

## Output

```plain
0=3% ; 1=2%
0=3% ; 1=1%
0=2% ; 1=2%
0=1% ; 1=2%
0=1% ; 1=1%
```

# Test: DO guard must be boolean

## Source

```basic
DO WHILE 2
    OUT 1
LOOP
```

## Compilation errors

```plain
1:10: Expected BOOLEAN but found INTEGER
```

# Test: EXIT DO outside of DO

## Source

```basic
EXIT DO
```

## Compilation errors

```plain
1:1: EXIT DO outside of DO
```
