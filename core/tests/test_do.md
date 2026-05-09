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
0005:   JUMP        14                  ; 2:10
0006:   MOVE        R66, R64            ; 3:9
0007:   LOADI       R65, 258            ; 3:9
0008:   UPCALL      0, R65              ; 3:5, OUT
0009:   MOVE        R65, R64            ; 4:9
0010:   LOADI       R66, 1              ; 4:13
0011:   SUBI        R65, R65, R66       ; 4:11
0012:   MOVE        R64, R65            ; 4:5
0013:   JUMP        1                   ; 2:10
0014:   EOF                             ; 0:0
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
0005:   JUMP        14                  ; 2:10
0006:   MOVE        R66, R64            ; 3:9
0007:   LOADI       R65, 258            ; 3:9
0008:   UPCALL      0, R65              ; 3:5, OUT
0009:   MOVE        R65, R64            ; 4:9
0010:   LOADI       R66, 1              ; 4:13
0011:   SUBI        R65, R65, R66       ; 4:11
0012:   MOVE        R64, R65            ; 4:5
0013:   JUMP        1                   ; 2:10
0014:   EOF                             ; 0:0
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
0004:   JMPF        R65, 13             ; 2:10
0005:   MOVE        R66, R64            ; 3:9
0006:   LOADI       R65, 258            ; 3:9
0007:   UPCALL      0, R65              ; 3:5, OUT
0008:   MOVE        R65, R64            ; 4:9
0009:   LOADI       R66, 1              ; 4:13
0010:   SUBI        R65, R65, R66       ; 4:11
0011:   MOVE        R64, R65            ; 4:5
0012:   JUMP        1                   ; 2:10
0013:   EOF                             ; 0:0
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
0004:   JMPF        R65, 13             ; 2:10
0005:   MOVE        R66, R64            ; 3:9
0006:   LOADI       R65, 258            ; 3:9
0007:   UPCALL      0, R65              ; 3:5, OUT
0008:   MOVE        R65, R64            ; 4:9
0009:   LOADI       R66, 1              ; 4:13
0010:   SUBI        R65, R65, R66       ; 4:11
0011:   MOVE        R64, R65            ; 4:5
0012:   JUMP        1                   ; 2:10
0013:   EOF                             ; 0:0
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
0004:   MOVE        R65, R64            ; 4:9
0005:   LOADI       R66, 1              ; 4:13
0006:   SUBI        R65, R65, R66       ; 4:11
0007:   MOVE        R64, R65            ; 4:5
0008:   MOVE        R65, R64            ; 5:12
0009:   LOADI       R66, 0              ; 5:16
0010:   CMPEQI      R65, R65, R66       ; 5:14
0011:   JMPF        R65, 1              ; 5:12
0012:   EOF                             ; 0:0
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
0004:   MOVE        R65, R64            ; 4:9
0005:   LOADI       R66, 1              ; 4:13
0006:   SUBI        R65, R65, R66       ; 4:11
0007:   MOVE        R64, R65            ; 4:5
0008:   MOVE        R65, R64            ; 5:12
0009:   LOADI       R66, 0              ; 5:16
0010:   CMPEQI      R65, R65, R66       ; 5:14
0011:   JMPF        R65, 1              ; 5:12
0012:   EOF                             ; 0:0
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
0004:   MOVE        R65, R64            ; 4:9
0005:   LOADI       R66, 1              ; 4:13
0006:   SUBI        R65, R65, R66       ; 4:11
0007:   MOVE        R64, R65            ; 4:5
0008:   MOVE        R65, R64            ; 5:12
0009:   LOADI       R66, 0              ; 5:16
0010:   CMPGTI      R65, R65, R66       ; 5:14
0011:   JMPF        R65, 13             ; 5:12
0012:   JUMP        1                   ; 5:12
0013:   EOF                             ; 0:0
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
0004:   MOVE        R65, R64            ; 4:9
0005:   LOADI       R66, 1              ; 4:13
0006:   SUBI        R65, R65, R66       ; 4:11
0007:   MOVE        R64, R65            ; 4:5
0008:   MOVE        R65, R64            ; 5:12
0009:   LOADI       R66, 0              ; 5:16
0010:   CMPGTI      R65, R65, R66       ; 5:14
0011:   JMPF        R65, 13             ; 5:12
0012:   JUMP        1                   ; 5:12
0013:   EOF                             ; 0:0
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
0004:   JMPF        R65, 40             ; 2:10
0005:   LOADI       R65, 2              ; 3:9
0006:   MOVE        R66, R65            ; 4:14
0007:   LOADI       R67, 0              ; 4:18
0008:   CMPEQI      R66, R66, R67       ; 4:16
0009:   JMPF        R66, 11             ; 4:14
0010:   JUMP        30                  ; 4:14
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
0024:   JUMP        30                  ; 6:34
0025:   MOVE        R66, R65            ; 7:13
0026:   LOADI       R67, 1              ; 7:17
0027:   SUBI        R66, R66, R67       ; 7:15
0028:   MOVE        R65, R66            ; 7:9
0029:   JUMP        6                   ; 4:14
0030:   MOVE        R66, R64            ; 9:8
0031:   LOADI       R67, 1              ; 9:12
0032:   CMPEQI      R66, R66, R67       ; 9:10
0033:   JMPF        R66, 35             ; 9:8
0034:   JUMP        40                  ; 9:20
0035:   MOVE        R66, R64            ; 10:9
0036:   LOADI       R67, 1              ; 10:13
0037:   SUBI        R66, R66, R67       ; 10:11
0038:   MOVE        R64, R66            ; 10:5
0039:   JUMP        1                   ; 2:10
0040:   EOF                             ; 0:0
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
0004:   JMPF        R65, 31             ; 2:10
0005:   LOADI       R65, 3              ; 3:9
0006:   MOVE        R66, R65            ; 4:14
0007:   LOADI       R67, 0              ; 4:18
0008:   CMPGTI      R66, R66, R67       ; 4:16
0009:   JMPF        R66, 21             ; 4:14
0010:   MOVE        R67, R64            ; 5:13
0011:   LOADI       R66, 274            ; 5:13
0012:   MOVE        R69, R65            ; 5:16
0013:   LOADI       R68, 258            ; 5:16
0014:   UPCALL      0, R66              ; 5:9, OUT
0015:   JUMP        21                  ; 6:9
0016:   MOVE        R66, R65            ; 7:13
0017:   LOADI       R67, 1              ; 7:17
0018:   SUBI        R66, R66, R67       ; 7:15
0019:   MOVE        R65, R66            ; 7:9
0020:   JUMP        6                   ; 4:14
0021:   LOADI       R67, 0              ; 9:9
0022:   LOADI       R66, 275            ; 9:9
0023:   MOVE        R69, R64            ; 9:18
0024:   LOADI       R68, 258            ; 9:18
0025:   UPCALL      0, R66              ; 9:5, OUT
0026:   MOVE        R66, R64            ; 10:9
0027:   LOADI       R67, 1              ; 10:13
0028:   SUBI        R66, R66, R67       ; 10:11
0029:   MOVE        R64, R66            ; 10:5
0030:   JUMP        1                   ; 2:10
0031:   EOF                             ; 0:0
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
0004:   JMPF        R65, 33             ; 2:10
0005:   LOADI       R65, 2              ; 3:9
0006:   MOVE        R66, R65            ; 4:14
0007:   LOADI       R67, 0              ; 4:18
0008:   CMPGTI      R66, R66, R67       ; 4:16
0009:   JMPF        R66, 25             ; 4:14
0010:   MOVE        R66, R64            ; 5:12
0011:   LOADI       R67, 2              ; 5:16
0012:   CMPEQI      R66, R66, R67       ; 5:14
0013:   JMPF        R66, 15             ; 5:12
0014:   JUMP        25                  ; 5:24
0015:   MOVE        R66, R65            ; 6:12
0016:   LOADI       R67, 1              ; 6:16
0017:   CMPEQI      R66, R66, R67       ; 6:14
0018:   JMPF        R66, 20             ; 6:12
0019:   JUMP        25                  ; 6:24
0020:   MOVE        R66, R65            ; 7:13
0021:   LOADI       R67, 1              ; 7:17
0022:   SUBI        R66, R66, R67       ; 7:15
0023:   MOVE        R65, R66            ; 7:9
0024:   JUMP        6                   ; 4:14
0025:   MOVE        R67, R64            ; 9:9
0026:   LOADI       R66, 258            ; 9:9
0027:   UPCALL      0, R66              ; 9:5, OUT
0028:   MOVE        R66, R64            ; 10:9
0029:   LOADI       R67, 1              ; 10:13
0030:   SUBI        R66, R66, R67       ; 10:11
0031:   MOVE        R64, R66            ; 10:5
0032:   JUMP        1                   ; 2:10
0033:   EOF                             ; 0:0
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
0004:   JMPF        R65, 25             ; 2:10
0005:   LOADI       R65, 2              ; 3:9
0006:   MOVE        R67, R64            ; 5:13
0007:   LOADI       R66, 274            ; 5:13
0008:   MOVE        R69, R65            ; 5:16
0009:   LOADI       R68, 258            ; 5:16
0010:   UPCALL      0, R66              ; 5:9, OUT
0011:   JUMP        20                  ; 6:9
0012:   MOVE        R66, R65            ; 7:13
0013:   LOADI       R67, 1              ; 7:17
0014:   SUBI        R66, R66, R67       ; 7:15
0015:   MOVE        R65, R66            ; 7:9
0016:   MOVE        R66, R65            ; 8:16
0017:   LOADI       R67, 0              ; 8:20
0018:   CMPEQI      R66, R66, R67       ; 8:18
0019:   JMPF        R66, 6              ; 8:16
0020:   MOVE        R66, R64            ; 9:9
0021:   LOADI       R67, 1              ; 9:13
0022:   SUBI        R66, R66, R67       ; 9:11
0023:   MOVE        R64, R66            ; 9:5
0024:   JUMP        1                   ; 2:10
0025:   EOF                             ; 0:0
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
0004:   JMPF        R65, 18             ; 2:10
0005:   LOADI       R65, 1              ; 3:9
0006:   MOVE        R67, R64            ; 5:13
0007:   LOADI       R66, 274            ; 5:13
0008:   MOVE        R69, R65            ; 5:16
0009:   LOADI       R68, 258            ; 5:16
0010:   UPCALL      0, R66              ; 5:9, OUT
0011:   JUMP        13                  ; 6:9
0012:   JUMP        6                   ; 0:0
0013:   MOVE        R66, R64            ; 8:9
0014:   LOADI       R67, 1              ; 8:13
0015:   SUBI        R66, R66, R67       ; 8:11
0016:   MOVE        R64, R66            ; 8:5
0017:   JUMP        1                   ; 2:10
0018:   EOF                             ; 0:0
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
0004:   JMPF        R65, 31             ; 2:10
0005:   LOADI       R65, 2              ; 3:9
0006:   MOVE        R66, R65            ; 4:14
0007:   LOADI       R67, 0              ; 4:18
0008:   CMPGTI      R66, R66, R67       ; 4:16
0009:   JMPF        R66, 21             ; 4:14
0010:   MOVE        R67, R64            ; 4:25
0011:   LOADI       R66, 274            ; 4:25
0012:   MOVE        R69, R65            ; 4:28
0013:   LOADI       R68, 258            ; 4:28
0014:   UPCALL      0, R66              ; 4:21, OUT
0015:   JUMP        21                  ; 4:31
0016:   MOVE        R66, R65            ; 4:44
0017:   LOADI       R67, 1              ; 4:48
0018:   SUBI        R66, R66, R67       ; 4:46
0019:   MOVE        R65, R66            ; 4:40
0020:   JUMP        6                   ; 4:14
0021:   LOADI       R67, 0              ; 5:9
0022:   LOADI       R66, 275            ; 5:9
0023:   MOVE        R69, R64            ; 5:18
0024:   LOADI       R68, 258            ; 5:18
0025:   UPCALL      0, R66              ; 5:5, OUT
0026:   MOVE        R66, R64            ; 6:9
0027:   LOADI       R67, 1              ; 6:13
0028:   SUBI        R66, R66, R67       ; 6:11
0029:   MOVE        R64, R66            ; 6:5
0030:   JUMP        1                   ; 2:10
0031:   EOF                             ; 0:0
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
0004:   JMPF        R65, 15             ; 2:10
0005:   LOADI       R66, 0              ; 3:9
0006:   LOADI       R65, 275            ; 3:9
0007:   MOVE        R68, R64            ; 3:18
0008:   LOADI       R67, 258            ; 3:18
0009:   UPCALL      0, R65              ; 3:5, OUT
0010:   MOVE        R65, R64            ; 4:9
0011:   LOADI       R66, 1              ; 4:13
0012:   SUBI        R65, R65, R66       ; 4:11
0013:   MOVE        R64, R65            ; 4:5
0014:   JUMP        1                   ; 2:10
0015:   LOADI       R64, 2              ; 7:5
0016:   MOVE        R65, R64            ; 8:10
0017:   LOADI       R66, 0              ; 8:14
0018:   CMPGTI      R65, R65, R66       ; 8:12
0019:   JMPF        R65, 30             ; 8:10
0020:   LOADI       R66, 1              ; 9:9
0021:   LOADI       R65, 275            ; 9:9
0022:   MOVE        R68, R64            ; 9:19
0023:   LOADI       R67, 258            ; 9:19
0024:   UPCALL      0, R65              ; 9:5, OUT
0025:   MOVE        R65, R64            ; 10:9
0026:   LOADI       R66, 1              ; 10:13
0027:   SUBI        R65, R65, R66       ; 10:11
0028:   MOVE        R64, R65            ; 10:5
0029:   JUMP        16                  ; 8:10
0030:   EOF                             ; 0:0
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
0004:   JMPF        R65, 16             ; 2:10
0005:   GOSUB       17                  ; 3:11
0006:   MOVE        R65, R64            ; 4:8
0007:   LOADI       R66, 1              ; 4:12
0008:   CMPEQI      R65, R65, R66       ; 4:10
0009:   JMPF        R65, 11             ; 4:8
0010:   JUMP        16                  ; 4:20
0011:   MOVE        R65, R64            ; 5:9
0012:   LOADI       R66, 1              ; 5:13
0013:   SUBI        R65, R65, R66       ; 5:11
0014:   MOVE        R64, R65            ; 5:5
0015:   JUMP        1                   ; 2:10
0016:   JUMP        43                  ; 7:6
0017:   LOADI       R65, 2              ; 9:5
0018:   MOVE        R66, R65            ; 10:10
0019:   LOADI       R67, 0              ; 10:14
0020:   CMPEQI      R66, R66, R67       ; 10:12
0021:   JMPF        R66, 23             ; 10:10
0022:   JUMP        42                  ; 10:10
0023:   MOVE        R67, R64            ; 11:9
0024:   LOADI       R66, 274            ; 11:9
0025:   MOVE        R69, R65            ; 11:12
0026:   LOADI       R68, 258            ; 11:12
0027:   UPCALL      0, R66              ; 11:5, OUT
0028:   MOVE        R66, R64            ; 12:8
0029:   LOADI       R67, 2              ; 12:12
0030:   CMPEQI      R66, R66, R67       ; 12:10
0031:   MOVE        R67, R65            ; 12:18
0032:   LOADI       R68, 2              ; 12:22
0033:   CMPEQI      R67, R67, R68       ; 12:20
0034:   AND         R66, R66, R67       ; 12:14
0035:   JMPF        R66, 37             ; 12:8
0036:   JUMP        42                  ; 12:30
0037:   MOVE        R66, R65            ; 13:9
0038:   LOADI       R67, 1              ; 13:13
0039:   SUBI        R66, R66, R67       ; 13:11
0040:   MOVE        R65, R66            ; 13:5
0041:   JUMP        18                  ; 10:10
0042:   RETURN                          ; 15:1
0043:   EOF                             ; 0:0
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
