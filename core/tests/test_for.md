# Test: Basic FOR incrementing loop

## Source

```basic
FOR a = 0 TO 3
    OUT a
NEXT
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:9
0001:   MOVE        R65, R64            ; 1:5
0002:   LOADI       R66, 3              ; 1:14
0003:   CMPLEI      R65, R65, R66       ; 1:11
0004:   JMPF        R65, 13             ; 1:5
0005:   MOVE        R66, R64            ; 2:9
0006:   LOADI       R65, 258            ; 2:9
0007:   UPCALL      0, R65              ; 2:5, OUT
0008:   MOVE        R65, R64            ; 1:5
0009:   LOADI       R66, 1              ; 1:1
0010:   ADDI        R65, R65, R66       ; 1:11
0011:   MOVE        R64, R65            ; 1:5
0012:   JUMP        1                   ; 1:5
0013:   EOF                             ; 0:0
```

## Output

```plain
0=0%
0=1%
0=2%
0=3%
```

# Test: FOR incrementing loop with STEP

## Source

```basic
FOR a = 0 TO 10 STEP 3
    OUT a
NEXT
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:9
0001:   MOVE        R65, R64            ; 1:5
0002:   LOADI       R66, 10             ; 1:14
0003:   CMPLEI      R65, R65, R66       ; 1:11
0004:   JMPF        R65, 13             ; 1:5
0005:   MOVE        R66, R64            ; 2:9
0006:   LOADI       R65, 258            ; 2:9
0007:   UPCALL      0, R65              ; 2:5, OUT
0008:   MOVE        R65, R64            ; 1:5
0009:   LOADI       R66, 3              ; 1:22
0010:   ADDI        R65, R65, R66       ; 1:11
0011:   MOVE        R64, R65            ; 1:5
0012:   JUMP        1                   ; 1:5
0013:   EOF                             ; 0:0
```

## Output

```plain
0=0%
0=3%
0=6%
0=9%
```

# Test: FOR decrementing loop with negative STEP

## Source

```basic
FOR a = 10 TO 1 STEP -2
    OUT a
NEXT
```

## Disassembly

```asm
0000:   LOADI       R64, 10             ; 1:9
0001:   MOVE        R65, R64            ; 1:5
0002:   LOADI       R66, 1              ; 1:15
0003:   CMPGEI      R65, R65, R66       ; 1:12
0004:   JMPF        R65, 13             ; 1:5
0005:   MOVE        R66, R64            ; 2:9
0006:   LOADI       R65, 258            ; 2:9
0007:   UPCALL      0, R65              ; 2:5, OUT
0008:   MOVE        R65, R64            ; 1:5
0009:   LOADC       R66, 0              ; 1:23
0010:   ADDI        R65, R65, R66       ; 1:12
0011:   MOVE        R64, R65            ; 1:5
0012:   JUMP        1                   ; 1:5
0013:   EOF                             ; 0:0
```

## Output

```plain
0=10%
0=8%
0=6%
0=4%
0=2%
```

# Test: FOR loop can have zero iterations

## Source

```basic
FOR i = 10 TO 9
    OUT i
NEXT
```

## Disassembly

```asm
0000:   LOADI       R64, 10             ; 1:9
0001:   MOVE        R65, R64            ; 1:5
0002:   LOADI       R66, 9              ; 1:15
0003:   CMPLEI      R65, R65, R66       ; 1:12
0004:   JMPF        R65, 13             ; 1:5
0005:   MOVE        R66, R64            ; 2:9
0006:   LOADI       R65, 258            ; 2:9
0007:   UPCALL      0, R65              ; 2:5, OUT
0008:   MOVE        R65, R64            ; 1:5
0009:   LOADI       R66, 1              ; 1:1
0010:   ADDI        R65, R65, R66       ; 1:12
0011:   MOVE        R64, R65            ; 1:5
0012:   JUMP        1                   ; 1:5
0013:   EOF                             ; 0:0
```

# Test: FOR loop with invalid direction has zero iterations

## Source

```basic
FOR i = 9 TO 10 STEP -1
    OUT i
NEXT
```

## Disassembly

```asm
0000:   LOADI       R64, 9              ; 1:9
0001:   MOVE        R65, R64            ; 1:5
0002:   LOADI       R66, 10             ; 1:14
0003:   CMPGEI      R65, R65, R66       ; 1:11
0004:   JMPF        R65, 13             ; 1:5
0005:   MOVE        R66, R64            ; 2:9
0006:   LOADI       R65, 258            ; 2:9
0007:   UPCALL      0, R65              ; 2:5, OUT
0008:   MOVE        R65, R64            ; 1:5
0009:   LOADC       R66, 0              ; 1:23
0010:   ADDI        R65, R65, R66       ; 1:11
0011:   MOVE        R64, R65            ; 1:5
0012:   JUMP        1                   ; 1:5
0013:   EOF                             ; 0:0
```

# Test: FOR iterator is visible after NEXT

## Source

```basic
FOR something = 1 TO 10 STEP 8
NEXT
OUT something
```

## Disassembly

```asm
0000:   LOADI       R64, 1              ; 1:17
0001:   MOVE        R65, R64            ; 1:5
0002:   LOADI       R66, 10             ; 1:22
0003:   CMPLEI      R65, R65, R66       ; 1:19
0004:   JMPF        R65, 10             ; 1:5
0005:   MOVE        R65, R64            ; 1:5
0006:   LOADI       R66, 8              ; 1:30
0007:   ADDI        R65, R65, R66       ; 1:19
0008:   MOVE        R64, R65            ; 1:5
0009:   JUMP        1                   ; 1:5
0010:   MOVE        R66, R64            ; 3:5
0011:   LOADI       R65, 258            ; 3:5
0012:   UPCALL      0, R65              ; 3:1, OUT
0013:   EOF                             ; 0:0
```

## Output

```plain
0=17%
```

# Test: FOR iterator can be modified in body

## Source

```basic
FOR something = 1 TO 5
    OUT something
    something = something + 1
NEXT
```

## Disassembly

```asm
0000:   LOADI       R64, 1              ; 1:17
0001:   MOVE        R65, R64            ; 1:5
0002:   LOADI       R66, 5              ; 1:22
0003:   CMPLEI      R65, R65, R66       ; 1:19
0004:   JMPF        R65, 17             ; 1:5
0005:   MOVE        R66, R64            ; 2:9
0006:   LOADI       R65, 258            ; 2:9
0007:   UPCALL      0, R65              ; 2:5, OUT
0008:   MOVE        R65, R64            ; 3:17
0009:   LOADI       R66, 1              ; 3:29
0010:   ADDI        R65, R65, R66       ; 3:27
0011:   MOVE        R64, R65            ; 3:5
0012:   MOVE        R65, R64            ; 1:5
0013:   LOADI       R66, 1              ; 1:1
0014:   ADDI        R65, R65, R66       ; 1:19
0015:   MOVE        R64, R65            ; 1:5
0016:   JUMP        1                   ; 1:5
0017:   EOF                             ; 0:0
```

## Output

```plain
0=1%
0=3%
0=5%
```

# Test: FOR with floating point bounds and integer sink

## Source

```basic
FOR a = 1.1 TO 2.1
    b% = (a * 10)
    OUT b
NEXT
```

## Disassembly

```asm
0000:   LOADC       R64, 0              ; 1:9
0001:   MOVE        R65, R64            ; 1:5
0002:   LOADC       R66, 1              ; 1:16
0003:   CMPLED      R65, R65, R66       ; 1:13
0004:   JMPF        R65, 19             ; 1:5
0005:   MOVE        R65, R64            ; 2:11
0006:   LOADI       R66, 10             ; 2:15
0007:   ITOD        R66                 ; 2:15
0008:   MULD        R65, R65, R66       ; 2:13
0009:   DTOI        R65                 ; 2:11
0010:   MOVE        R67, R65            ; 3:9
0011:   LOADI       R66, 258            ; 3:9
0012:   UPCALL      0, R66              ; 3:5, OUT
0013:   MOVE        R66, R64            ; 1:5
0014:   LOADI       R67, 1              ; 1:1
0015:   ITOD        R67                 ; 1:1
0016:   ADDD        R66, R66, R67       ; 1:13
0017:   MOVE        R64, R66            ; 1:5
0018:   JUMP        1                   ; 1:5
0019:   EOF                             ; 0:0
```

## Output

```plain
0=11%
0=21%
```

# Test: FOR with untyped iterator and floating STEP uses double arithmetic

## Source

```basic
i = 0
FOR iter = 0 TO 2 STEP 0.1
    i = i + 1
    IF i = 5 THEN EXIT FOR
NEXT
b% = (iter * 10)
OUT i; b
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:5
0001:   LOADI       R65, 0              ; 2:12
0002:   ITOD        R65                 ; 2:12
0003:   MOVE        R66, R65            ; 2:5
0004:   LOADI       R67, 2              ; 2:17
0005:   ITOD        R67                 ; 2:17
0006:   CMPLED      R66, R66, R67       ; 2:14
0007:   JMPF        R66, 22             ; 2:5
0008:   MOVE        R66, R64            ; 3:9
0009:   LOADI       R67, 1              ; 3:13
0010:   ADDI        R66, R66, R67       ; 3:11
0011:   MOVE        R64, R66            ; 3:5
0012:   MOVE        R66, R64            ; 4:8
0013:   LOADI       R67, 5              ; 4:12
0014:   CMPEQI      R66, R66, R67       ; 4:10
0015:   JMPF        R66, 17             ; 4:8
0016:   JUMP        22                  ; 4:19
0017:   MOVE        R66, R65            ; 2:5
0018:   LOADC       R67, 0              ; 2:24
0019:   ADDD        R66, R66, R67       ; 2:14
0020:   MOVE        R65, R66            ; 2:5
0021:   JUMP        3                   ; 2:5
0022:   MOVE        R66, R65            ; 6:7
0023:   LOADI       R67, 10             ; 6:14
0024:   ITOD        R67                 ; 6:14
0025:   MULD        R66, R66, R67       ; 6:12
0026:   DTOI        R66                 ; 6:7
0027:   MOVE        R68, R64            ; 7:5
0028:   LOADI       R67, 274            ; 7:5
0029:   MOVE        R70, R66            ; 7:8
0030:   LOADI       R69, 258            ; 7:8
0031:   UPCALL      0, R67              ; 7:1, OUT
0032:   EOF                             ; 0:0
```

## Output

```plain
0=5% ; 1=4%
```

# Test: FOR with integer iterator and floating STEP can get stuck

## Source

```basic
i = 0
DIM a AS INTEGER
FOR a = 1.0 TO 2.0 STEP 0.4
    i = i + 1
    IF i = 100 THEN
        GOTO @out
    END IF
NEXT
@out:
OUT i
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:5
0001:   LOADI       R65, 0              ; 2:5
0002:   LOADC       R65, 0              ; 3:9
0003:   DTOI        R65                 ; 3:9
0004:   MOVE        R66, R65            ; 3:5
0005:   LOADC       R67, 1              ; 3:16
0006:   ITOD        R66                 ; 3:13
0007:   CMPLED      R66, R66, R67       ; 3:13
0008:   JMPF        R66, 25             ; 3:5
0009:   MOVE        R66, R64            ; 4:9
0010:   LOADI       R67, 1              ; 4:13
0011:   ADDI        R66, R66, R67       ; 4:11
0012:   MOVE        R64, R66            ; 4:5
0013:   MOVE        R66, R64            ; 5:8
0014:   LOADI       R67, 100            ; 5:12
0015:   CMPEQI      R66, R66, R67       ; 5:10
0016:   JMPF        R66, 18             ; 5:8
0017:   JUMP        25                  ; 6:14
0018:   MOVE        R66, R65            ; 3:5
0019:   LOADC       R67, 2              ; 3:25
0020:   ITOD        R66                 ; 3:13
0021:   ADDD        R66, R66, R67       ; 3:13
0022:   DTOI        R66                 ; 3:5
0023:   MOVE        R65, R66            ; 3:5
0024:   JUMP        4                   ; 3:5
0025:   MOVE        R67, R64            ; 10:5
0026:   LOADI       R66, 258            ; 10:5
0027:   UPCALL      0, R66              ; 10:1, OUT
0028:   EOF                             ; 0:0
```

## Output

```plain
0=100%
```

# Test: EXIT FOR exits innermost FOR

## Source

```basic
FOR i = 1 TO 10
    IF i = 5 THEN EXIT FOR
    OUT i
NEXT
```

## Disassembly

```asm
0000:   LOADI       R64, 1              ; 1:9
0001:   MOVE        R65, R64            ; 1:5
0002:   LOADI       R66, 10             ; 1:14
0003:   CMPLEI      R65, R65, R66       ; 1:11
0004:   JMPF        R65, 18             ; 1:5
0005:   MOVE        R65, R64            ; 2:8
0006:   LOADI       R66, 5              ; 2:12
0007:   CMPEQI      R65, R65, R66       ; 2:10
0008:   JMPF        R65, 10             ; 2:8
0009:   JUMP        18                  ; 2:19
0010:   MOVE        R66, R64            ; 3:9
0011:   LOADI       R65, 258            ; 3:9
0012:   UPCALL      0, R65              ; 3:5, OUT
0013:   MOVE        R65, R64            ; 1:5
0014:   LOADI       R66, 1              ; 1:1
0015:   ADDI        R65, R65, R66       ; 1:11
0016:   MOVE        R64, R65            ; 1:5
0017:   JUMP        1                   ; 1:5
0018:   EOF                             ; 0:0
```

## Output

```plain
0=1%
0=2%
0=3%
0=4%
```

# Test: EXIT DO and EXIT FOR in nested loops

## Source

```basic
FOR i = 1 TO 10
    j = 5
    DO WHILE j > 0
        IF j = 2 THEN EXIT DO
        IF i = 4 THEN EXIT FOR
        OUT i; j
        j = j - 1
    LOOP
NEXT
```

## Disassembly

```asm
0000:   LOADI       R64, 1              ; 1:9
0001:   MOVE        R65, R64            ; 1:5
0002:   LOADI       R66, 10             ; 1:14
0003:   CMPLEI      R65, R65, R66       ; 1:11
0004:   JMPF        R65, 35             ; 1:5
0005:   LOADI       R65, 5              ; 2:9
0006:   MOVE        R66, R65            ; 3:14
0007:   LOADI       R67, 0              ; 3:18
0008:   CMPGTI      R66, R66, R67       ; 3:16
0009:   JMPF        R66, 30             ; 3:14
0010:   MOVE        R66, R65            ; 4:12
0011:   LOADI       R67, 2              ; 4:16
0012:   CMPEQI      R66, R66, R67       ; 4:14
0013:   JMPF        R66, 15             ; 4:12
0014:   JUMP        30                  ; 4:23
0015:   MOVE        R66, R64            ; 5:12
0016:   LOADI       R67, 4              ; 5:16
0017:   CMPEQI      R66, R66, R67       ; 5:14
0018:   JMPF        R66, 20             ; 5:12
0019:   JUMP        35                  ; 5:23
0020:   MOVE        R67, R64            ; 6:13
0021:   LOADI       R66, 274            ; 6:13
0022:   MOVE        R69, R65            ; 6:16
0023:   LOADI       R68, 258            ; 6:16
0024:   UPCALL      0, R66              ; 6:9, OUT
0025:   MOVE        R66, R65            ; 7:13
0026:   LOADI       R67, 1              ; 7:17
0027:   SUBI        R66, R66, R67       ; 7:15
0028:   MOVE        R65, R66            ; 7:9
0029:   JUMP        6                   ; 3:14
0030:   MOVE        R66, R64            ; 1:5
0031:   LOADI       R67, 1              ; 1:1
0032:   ADDI        R66, R66, R67       ; 1:11
0033:   MOVE        R64, R66            ; 1:5
0034:   JUMP        1                   ; 1:5
0035:   EOF                             ; 0:0
```

## Output

```plain
0=1% ; 1=5%
0=1% ; 1=4%
0=1% ; 1=3%
0=2% ; 1=5%
0=2% ; 1=4%
0=2% ; 1=3%
0=3% ; 1=5%
0=3% ; 1=4%
0=3% ; 1=3%
```

# Test: EXIT FOR outside FOR is an error

## Source

```basic
EXIT FOR
```

## Compilation errors

```plain
1:1: EXIT FOR outside of FOR
```

# Test: EXIT FOR in WHILE is an error

## Source

```basic
WHILE TRUE
    EXIT FOR
WEND
```

## Compilation errors

```plain
2:5: EXIT FOR outside of FOR
```

# Test: FOR guard errors with incompatible types and positive STEP

## Source

```basic
FOR i = "a" TO 3
NEXT
```

## Compilation errors

```plain
1:13: Cannot <= STRING and INTEGER
```

# Test: FOR guard errors with incompatible types and negative STEP

## Source

```basic
FOR i = 1 TO "b" STEP -8
NEXT
```

## Compilation errors

```plain
1:11: Cannot >= INTEGER and STRING
```
