# Test: Produce and consume empty strings

## Source

```basic
s$ = ""
FOR i% = 1 TO 100000
    ' Produce a new string by _consuming_ an earlier one.
    s$ = s$ + ""
NEXT
OUT "success"
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:6
0001:   LOADI       R65, 1              ; 2:10
0002:   MOVE        R66, R65            ; 2:5
0003:   LOADC       R67, 1              ; 2:15
0004:   CMPLEI      R66, R66, R67       ; 2:12
0005:   JMPF        R66, 15             ; 2:5
0006:   MOVE        R66, R64            ; 4:10
0007:   LOADI       R67, 0              ; 4:15
0008:   CONCAT      R66, R66, R67       ; 4:13
0009:   MOVE        R64, R66            ; 4:5
0010:   MOVE        R66, R65            ; 2:5
0011:   LOADI       R67, 1              ; 2:21
0012:   ADDI        R66, R66, R67       ; 2:12
0013:   MOVE        R65, R66            ; 2:5
0014:   JUMP        2                   ; 2:5
0015:   LOADI       R67, 2              ; 6:5
0016:   LOADI       R66, 259            ; 6:5
0017:   UPCALL      0, R66              ; 6:1, OUT
0018:   EOF                             ; 0:0
```

## Output

```plain
0=success$
```

# Test: Produce and consume non-empty strings

## Source

```basic
s$ = ""
FOR i% = 1 TO 100000
    ' Produce a new string by _consuming_ an earlier one.
    s$ = s$ + "x"
    ' But keep overall memory bounded.
    s$ = ""
NEXT
OUT "success"
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:6
0001:   LOADI       R65, 1              ; 2:10
0002:   MOVE        R66, R65            ; 2:5
0003:   LOADC       R67, 1              ; 2:15
0004:   CMPLEI      R66, R66, R67       ; 2:12
0005:   JMPF        R66, 16             ; 2:5
0006:   MOVE        R66, R64            ; 4:10
0007:   LOADI       R67, 2              ; 4:15
0008:   CONCAT      R66, R66, R67       ; 4:13
0009:   MOVE        R64, R66            ; 4:5
0010:   LOADI       R64, 0              ; 6:10
0011:   MOVE        R66, R65            ; 2:5
0012:   LOADI       R67, 1              ; 2:21
0013:   ADDI        R66, R66, R67       ; 2:12
0014:   MOVE        R65, R66            ; 2:5
0015:   JUMP        2                   ; 2:5
0016:   LOADI       R67, 3              ; 8:5
0017:   LOADI       R66, 259            ; 8:5
0018:   UPCALL      0, R66              ; 8:1, OUT
0019:   EOF                             ; 0:0
```

## Runtime errors

```plain
4:13: Out of heap space
```

# Test: Recursive subroutine runs out of call stack

## Source

```basic
SUB recurse(n%)
    IF n < 5000 THEN
        recurse n + 1
    END IF
END SUB

recurse 0
OUT 123
```

## Disassembly

```asm
0000:   JUMP        10                  ; 1:5

;; RECURSE (BEGIN)
0001:   MOVE        R65, R64            ; 2:8
0002:   LOADI       R66, 5000           ; 2:12
0003:   CMPLTI      R65, R65, R66       ; 2:10
0004:   JMPF        R65, 9              ; 2:8
0005:   MOVE        R65, R64            ; 3:17
0006:   LOADI       R66, 1              ; 3:21
0007:   ADDI        R65, R65, R66       ; 3:19
0008:   CALL        R65, 1              ; 3:9, RECURSE
0009:   RETURN                          ; 5:1
;; RECURSE (END)

0010:   LOADI       R64, 0              ; 7:9
0011:   CALL        R64, 1              ; 7:1, RECURSE
0012:   LOADI       R65, 123            ; 8:5
0013:   LOADI       R64, 258            ; 8:5
0014:   UPCALL      0, R64              ; 8:1, OUT
0015:   EOF                             ; 0:0
```

## Runtime errors

```plain
3:9: Out of call stack space
```

# Test: Recursive GOSUB runs out of call stack

## Source

```basic
count% = 0
GOSUB @recurse
OUT 123

@recurse
count% = count% + 1
IF count < 5000 THEN GOSUB @recurse
RETURN
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:10
0001:   GOSUB       5                   ; 2:7
0002:   LOADI       R66, 123            ; 3:5
0003:   LOADI       R65, 258            ; 3:5
0004:   UPCALL      0, R65              ; 3:1, OUT
0005:   MOVE        R65, R64            ; 6:10
0006:   LOADI       R66, 1              ; 6:19
0007:   ADDI        R65, R65, R66       ; 6:17
0008:   MOVE        R64, R65            ; 6:1
0009:   MOVE        R65, R64            ; 7:4
0010:   LOADI       R66, 5000           ; 7:12
0011:   CMPLTI      R65, R65, R66       ; 7:10
0012:   JMPF        R65, 14             ; 7:4
0013:   GOSUB       5                   ; 7:28
0014:   RETURN                          ; 8:1
0015:   EOF                             ; 0:0
```

## Runtime errors

```plain
7:28: Out of call stack space
```
