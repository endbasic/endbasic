# Test: Execute IF branch when condition is true

## Source

```basic
IF TRUE THEN
    OUT "yes"
END IF
```

## Disassembly

```asm
0000:   LOADI       R64, 1              ; 1:4
0001:   JMPF        R64, 5              ; 1:4
0002:   LOADI       R65, 0              ; 2:9
0003:   LOADI       R64, 259            ; 2:9
0004:   UPCALL      0, R64              ; 2:5, OUT
0005:   EOF                             ; 0:0
```

## Output

```plain
0=yes$
```

# Test: Skip IF branch when condition is false

## Source

```basic
IF FALSE THEN
    OUT "yes"
END IF
OUT "after"
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:4
0001:   JMPF        R64, 5              ; 1:4
0002:   LOADI       R65, 0              ; 2:9
0003:   LOADI       R64, 259            ; 2:9
0004:   UPCALL      0, R64              ; 2:5, OUT
0005:   LOADI       R65, 1              ; 4:5
0006:   LOADI       R64, 259            ; 4:5
0007:   UPCALL      0, R64              ; 4:1, OUT
0008:   EOF                             ; 0:0
```

## Output

```plain
0=after$
```

# Test: Take ELSEIF branch in IF ELSEIF ELSE chain

## Source

```basic
cond1 = FALSE
cond2 = TRUE
IF cond1 THEN
    OUT "first"
ELSEIF cond2 THEN
    OUT "second"
ELSE
    OUT "other"
END IF
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:9
0001:   LOADI       R65, 1              ; 2:9
0002:   MOVE        R66, R64            ; 3:4
0003:   JMPF        R66, 8              ; 3:4
0004:   LOADI       R67, 0              ; 4:9
0005:   LOADI       R66, 259            ; 4:9
0006:   UPCALL      0, R66              ; 4:5, OUT
0007:   JUMP        19                  ; 3:4
0008:   MOVE        R66, R65            ; 5:8
0009:   JMPF        R66, 14             ; 5:8
0010:   LOADI       R67, 1              ; 6:9
0011:   LOADI       R66, 259            ; 6:9
0012:   UPCALL      0, R66              ; 6:5, OUT
0013:   JUMP        19                  ; 5:8
0014:   LOADI       R66, 1              ; 7:1
0015:   JMPF        R66, 19             ; 7:1
0016:   LOADI       R67, 2              ; 8:9
0017:   LOADI       R66, 259            ; 8:9
0018:   UPCALL      0, R66              ; 8:5, OUT
0019:   EOF                             ; 0:0
```

## Output

```plain
0=second$
```

# Test: Take IF branch in IF ELSEIF chain

## Source

```basic
cond1 = TRUE
cond2 = FALSE
IF cond1 THEN
    OUT "first"
ELSEIF cond2 THEN
    OUT "second"
END IF
```

## Disassembly

```asm
0000:   LOADI       R64, 1              ; 1:9
0001:   LOADI       R65, 0              ; 2:9
0002:   MOVE        R66, R64            ; 3:4
0003:   JMPF        R66, 8              ; 3:4
0004:   LOADI       R67, 0              ; 4:9
0005:   LOADI       R66, 259            ; 4:9
0006:   UPCALL      0, R66              ; 4:5, OUT
0007:   JUMP        13                  ; 3:4
0008:   MOVE        R66, R65            ; 5:8
0009:   JMPF        R66, 13             ; 5:8
0010:   LOADI       R67, 1              ; 6:9
0011:   LOADI       R66, 259            ; 6:9
0012:   UPCALL      0, R66              ; 6:5, OUT
0013:   EOF                             ; 0:0
```

## Output

```plain
0=first$
```

# Test: Take ELSE branch in IF ELSE block

## Source

```basic
cond = FALSE
IF cond THEN
    OUT "yes"
ELSE
    OUT "no"
END IF
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:8
0001:   MOVE        R65, R64            ; 2:4
0002:   JMPF        R65, 7              ; 2:4
0003:   LOADI       R66, 0              ; 3:9
0004:   LOADI       R65, 259            ; 3:9
0005:   UPCALL      0, R65              ; 3:5, OUT
0006:   JUMP        12                  ; 2:4
0007:   LOADI       R65, 1              ; 4:1
0008:   JMPF        R65, 12             ; 4:1
0009:   LOADI       R66, 1              ; 5:9
0010:   LOADI       R65, 259            ; 5:9
0011:   UPCALL      0, R65              ; 5:5, OUT
0012:   EOF                             ; 0:0
```

## Output

```plain
0=no$
```

# Test: Execute nested IF blocks

## Source

```basic
outer = TRUE
inner = TRUE
IF outer THEN
    IF inner THEN
        OUT "both"
    END IF
END IF
```

## Disassembly

```asm
0000:   LOADI       R64, 1              ; 1:9
0001:   LOADI       R65, 1              ; 2:9
0002:   MOVE        R66, R64            ; 3:4
0003:   JMPF        R66, 9              ; 3:4
0004:   MOVE        R66, R65            ; 4:8
0005:   JMPF        R66, 9              ; 4:8
0006:   LOADI       R67, 0              ; 5:13
0007:   LOADI       R66, 259            ; 5:13
0008:   UPCALL      0, R66              ; 5:9, OUT
0009:   EOF                             ; 0:0
```

## Output

```plain
0=both$
```

# Test: Evaluate nested IF with variables and ELSE

## Source

```basic
a = TRUE
b = FALSE
IF a THEN
    IF b THEN
        OUT "a and b"
    ELSE
        OUT "only a"
    END IF
END IF
```

## Disassembly

```asm
0000:   LOADI       R64, 1              ; 1:5
0001:   LOADI       R65, 0              ; 2:5
0002:   MOVE        R66, R64            ; 3:4
0003:   JMPF        R66, 15             ; 3:4
0004:   MOVE        R66, R65            ; 4:8
0005:   JMPF        R66, 10             ; 4:8
0006:   LOADI       R67, 0              ; 5:13
0007:   LOADI       R66, 259            ; 5:13
0008:   UPCALL      0, R66              ; 5:9, OUT
0009:   JUMP        15                  ; 4:8
0010:   LOADI       R66, 1              ; 6:5
0011:   JMPF        R66, 15             ; 6:5
0012:   LOADI       R67, 1              ; 7:13
0013:   LOADI       R66, 259            ; 7:13
0014:   UPCALL      0, R66              ; 7:9, OUT
0015:   EOF                             ; 0:0
```

## Output

```plain
0=only a$
```

# Test: Evaluate two IF guards when first guard matches

## Source

```basic
n = 3
IF n = 3 THEN
    OUT "match"
END IF
IF n <> 3 THEN
    OUT "no match"
END IF
```

## Disassembly

```asm
0000:   LOADI       R64, 3              ; 1:5
0001:   MOVE        R65, R64            ; 2:4
0002:   LOADI       R66, 3              ; 2:8
0003:   CMPEQI      R65, R65, R66       ; 2:6
0004:   JMPF        R65, 8              ; 2:4
0005:   LOADI       R66, 0              ; 3:9
0006:   LOADI       R65, 259            ; 3:9
0007:   UPCALL      0, R65              ; 3:5, OUT
0008:   MOVE        R65, R64            ; 5:4
0009:   LOADI       R66, 3              ; 5:9
0010:   CMPNEI      R65, R65, R66       ; 5:6
0011:   JMPF        R65, 15             ; 5:4
0012:   LOADI       R66, 1              ; 6:9
0013:   LOADI       R65, 259            ; 6:9
0014:   UPCALL      0, R65              ; 6:5, OUT
0015:   EOF                             ; 0:0
```

## Output

```plain
0=match$
```

# Test: Evaluate two IF guards when second guard matches

## Source

```basic
n = 5
IF n = 3 THEN
    OUT "match"
END IF
IF n <> 3 THEN
    OUT "no match"
END IF
```

## Disassembly

```asm
0000:   LOADI       R64, 5              ; 1:5
0001:   MOVE        R65, R64            ; 2:4
0002:   LOADI       R66, 3              ; 2:8
0003:   CMPEQI      R65, R65, R66       ; 2:6
0004:   JMPF        R65, 8              ; 2:4
0005:   LOADI       R66, 0              ; 3:9
0006:   LOADI       R65, 259            ; 3:9
0007:   UPCALL      0, R65              ; 3:5, OUT
0008:   MOVE        R65, R64            ; 5:4
0009:   LOADI       R66, 3              ; 5:9
0010:   CMPNEI      R65, R65, R66       ; 5:6
0011:   JMPF        R65, 15             ; 5:4
0012:   LOADI       R66, 1              ; 6:9
0013:   LOADI       R65, 259            ; 6:9
0014:   UPCALL      0, R65              ; 6:5, OUT
0015:   EOF                             ; 0:0
```

## Output

```plain
0=no match$
```

# Test: Take third ELSEIF branch in multi-branch IF chain

## Source

```basic
n = 3
IF n = 1 THEN
    OUT "first"
ELSEIF n = 2 THEN
    OUT "second"
ELSEIF n = 3 THEN
    OUT "third"
ELSE
    OUT "fourth"
END IF
```

## Disassembly

```asm
0000:   LOADI       R64, 3              ; 1:5
0001:   MOVE        R65, R64            ; 2:4
0002:   LOADI       R66, 1              ; 2:8
0003:   CMPEQI      R65, R65, R66       ; 2:6
0004:   JMPF        R65, 9              ; 2:4
0005:   LOADI       R66, 0              ; 3:9
0006:   LOADI       R65, 259            ; 3:9
0007:   UPCALL      0, R65              ; 3:5, OUT
0008:   JUMP        30                  ; 2:4
0009:   MOVE        R65, R64            ; 4:8
0010:   LOADI       R66, 2              ; 4:12
0011:   CMPEQI      R65, R65, R66       ; 4:10
0012:   JMPF        R65, 17             ; 4:8
0013:   LOADI       R66, 1              ; 5:9
0014:   LOADI       R65, 259            ; 5:9
0015:   UPCALL      0, R65              ; 5:5, OUT
0016:   JUMP        30                  ; 4:8
0017:   MOVE        R65, R64            ; 6:8
0018:   LOADI       R66, 3              ; 6:12
0019:   CMPEQI      R65, R65, R66       ; 6:10
0020:   JMPF        R65, 25             ; 6:8
0021:   LOADI       R66, 2              ; 7:9
0022:   LOADI       R65, 259            ; 7:9
0023:   UPCALL      0, R65              ; 7:5, OUT
0024:   JUMP        30                  ; 6:8
0025:   LOADI       R65, 1              ; 8:1
0026:   JMPF        R65, 30             ; 8:1
0027:   LOADI       R66, 3              ; 9:9
0028:   LOADI       R65, 259            ; 9:9
0029:   UPCALL      0, R65              ; 9:5, OUT
0030:   EOF                             ; 0:0
```

## Output

```plain
0=third$
```

# Test: Take ELSE branch in multi-branch IF chain

## Source

```basic
n = 4
IF n = 1 THEN
    OUT "first"
ELSEIF n = 2 THEN
    OUT "second"
ELSEIF n = 3 THEN
    OUT "third"
ELSE
    OUT "fourth"
END IF
```

## Disassembly

```asm
0000:   LOADI       R64, 4              ; 1:5
0001:   MOVE        R65, R64            ; 2:4
0002:   LOADI       R66, 1              ; 2:8
0003:   CMPEQI      R65, R65, R66       ; 2:6
0004:   JMPF        R65, 9              ; 2:4
0005:   LOADI       R66, 0              ; 3:9
0006:   LOADI       R65, 259            ; 3:9
0007:   UPCALL      0, R65              ; 3:5, OUT
0008:   JUMP        30                  ; 2:4
0009:   MOVE        R65, R64            ; 4:8
0010:   LOADI       R66, 2              ; 4:12
0011:   CMPEQI      R65, R65, R66       ; 4:10
0012:   JMPF        R65, 17             ; 4:8
0013:   LOADI       R66, 1              ; 5:9
0014:   LOADI       R65, 259            ; 5:9
0015:   UPCALL      0, R65              ; 5:5, OUT
0016:   JUMP        30                  ; 4:8
0017:   MOVE        R65, R64            ; 6:8
0018:   LOADI       R66, 3              ; 6:12
0019:   CMPEQI      R65, R65, R66       ; 6:10
0020:   JMPF        R65, 25             ; 6:8
0021:   LOADI       R66, 2              ; 7:9
0022:   LOADI       R65, 259            ; 7:9
0023:   UPCALL      0, R65              ; 7:5, OUT
0024:   JUMP        30                  ; 6:8
0025:   LOADI       R65, 1              ; 8:1
0026:   JMPF        R65, 30             ; 8:1
0027:   LOADI       R66, 3              ; 9:9
0028:   LOADI       R65, 259            ; 9:9
0029:   UPCALL      0, R65              ; 9:5, OUT
0030:   EOF                             ; 0:0
```

## Output

```plain
0=fourth$
```

# Test: Fail when ELSEIF guard is not boolean

## Source

```basic
n = 5
IF n = 3 THEN
    OUT "match"
ELSEIF "foo" THEN
    OUT "no match"
END IF
```

## Compilation errors

```plain
4:8: Expected BOOLEAN but found STRING
```

# Test: Fail on invalid ELSE IF syntax

## Source

```basic
IF TRUE THEN
ELSE IF TRUE THEN
END IF
```

## Compilation errors

```plain
2:6: Expecting newline after ELSE
```

# Test: Fail on END IF without matching IF

## Source

```basic
IF TRUE THEN END IF
```

## Compilation errors

```plain
1:14: END IF without IF
```

# Test: Fail when IF condition lacks THEN

## Source

```basic
IF 2
END IF
```

## Compilation errors

```plain
1:5: No THEN in IF statement
```

# Test: Fail when TRUE condition lacks THEN

## Source

```basic
IF TRUE
END IF
OUT 3
```

## Compilation errors

```plain
1:8: No THEN in IF statement
```

# Test: Fail when IF condition is not boolean

## Source

```basic
IF 2 THEN
END IF
```

## Compilation errors

```plain
1:4: Expected BOOLEAN but found INTEGER
```

# Test: Fail when ELSEIF condition is not boolean

## Source

```basic
IF FALSE THEN
ELSEIF 2 THEN
END IF
```

## Compilation errors

```plain
2:8: Expected BOOLEAN but found INTEGER
```
