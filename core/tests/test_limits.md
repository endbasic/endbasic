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
0003:   LOADC       R67, 1              ; 2:15, 100000
0004:   CMPLEI      R66, R66, R67       ; 2:12
0005:   JMPF        R66, 15             ; 2:5
0006:   MOVE        R66, R64            ; 4:10
0007:   LOADI       R67, 0              ; 4:15
0008:   CONCAT      R66, R66, R67       ; 4:13
0009:   MOVE        R64, R66            ; 4:5
0010:   MOVE        R66, R65            ; 2:5
0011:   LOADI       R67, 1              ; 2:1
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
0003:   LOADC       R67, 1              ; 2:15, 100000
0004:   CMPLEI      R66, R66, R67       ; 2:12
0005:   JMPF        R66, 16             ; 2:5
0006:   MOVE        R66, R64            ; 4:10
0007:   LOADI       R67, 2              ; 4:15
0008:   CONCAT      R66, R66, R67       ; 4:13
0009:   MOVE        R64, R66            ; 4:5
0010:   LOADI       R64, 0              ; 6:10
0011:   MOVE        R66, R65            ; 2:5
0012:   LOADI       R67, 1              ; 2:1
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

# Test: ON ERROR GOTO can catch a stack overflow once

## Source

```basic
ON ERROR GOTO @handler
GOSUB @recurse
OUT 123
END

@recurse
count% = count% + 1
IF count% < 5000 THEN GOSUB @recurse
RETURN

@handler
OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       JUMP, 16            ; 1:1
0001:   GOSUB       7                   ; 2:7
0002:   LOADI       R65, 123            ; 3:5
0003:   LOADI       R64, 258            ; 3:5
0004:   UPCALL      0, R64              ; 3:1, OUT
0005:   LOADI       R64, 0              ; 4:1
0006:   END         R64                 ; 4:1
0007:   MOVE        R64, R64            ; 7:10
0008:   LOADI       R65, 1              ; 7:19
0009:   ADDI        R64, R64, R65       ; 7:17
0010:   MOVE        R65, R64            ; 8:4
0011:   LOADI       R66, 5000           ; 8:13
0012:   CMPLTI      R65, R65, R66       ; 8:11
0013:   JMPF        R65, 15             ; 8:4
0014:   GOSUB       7                   ; 8:29
0015:   RETURN                          ; 9:1
0016:   UPCALL      1, R66              ; 12:5, LAST_ERROR
0017:   LOADI       R65, 259            ; 12:5
0018:   UPCALL      0, R65              ; 12:1, OUT
0019:   EOF                             ; 0:0
```

## Output

```plain
0=8:29: Out of call stack space$
```

# Test: ON ERROR GOTO must be re-armed after stack overflow

## Source

```basic
ON ERROR GOTO @handler1
GOSUB @recurse1
OUT 123
END

@recurse1
count1% = count1% + 1
IF count1% < 5000 THEN GOSUB @recurse1
RETURN

@handler1
OUT LAST_ERROR
ON ERROR GOTO @handler2
GOSUB @recurse2
END

@recurse2
count2% = count2% + 1
IF count2% < 5000 THEN GOSUB @recurse2
RETURN

@handler2
OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       JUMP, 16            ; 1:1
0001:   GOSUB       7                   ; 2:7
0002:   LOADI       R65, 123            ; 3:5
0003:   LOADI       R64, 258            ; 3:5
0004:   UPCALL      0, R64              ; 3:1, OUT
0005:   LOADI       R64, 0              ; 4:1
0006:   END         R64                 ; 4:1
0007:   MOVE        R64, R64            ; 7:11
0008:   LOADI       R65, 1              ; 7:21
0009:   ADDI        R64, R64, R65       ; 7:19
0010:   MOVE        R65, R64            ; 8:4
0011:   LOADI       R66, 5000           ; 8:14
0012:   CMPLTI      R65, R65, R66       ; 8:12
0013:   JMPF        R65, 15             ; 8:4
0014:   GOSUB       7                   ; 8:30
0015:   RETURN                          ; 9:1
0016:   UPCALL      1, R66              ; 12:5, LAST_ERROR
0017:   LOADI       R65, 259            ; 12:5
0018:   UPCALL      0, R65              ; 12:1, OUT
0019:   SETEH       JUMP, 32            ; 13:1
0020:   GOSUB       23                  ; 14:7
0021:   LOADI       R65, 0              ; 15:1
0022:   END         R65                 ; 15:1
0023:   MOVE        R65, R65            ; 18:11
0024:   LOADI       R66, 1              ; 18:21
0025:   ADDI        R65, R65, R66       ; 18:19
0026:   MOVE        R66, R65            ; 19:4
0027:   LOADI       R67, 5000           ; 19:14
0028:   CMPLTI      R66, R66, R67       ; 19:12
0029:   JMPF        R66, 31             ; 19:4
0030:   GOSUB       23                  ; 19:30
0031:   RETURN                          ; 20:1
0032:   UPCALL      1, R67              ; 23:5, LAST_ERROR
0033:   LOADI       R66, 259            ; 23:5
0034:   UPCALL      0, R66              ; 23:1, OUT
0035:   EOF                             ; 0:0
```

## Output

```plain
0=8:30: Out of call stack space$
0=14:7: Out of call stack space$
```

# Test: ON ERROR GOTO is not reentrant after stack overflow

## Source

```basic
ON ERROR GOTO @handler
GOSUB @recurse1
OUT 123
END

@recurse1
count1% = count1% + 1
IF count1% < 5000 THEN GOSUB @recurse1
RETURN

@handler
OUT LAST_ERROR
GOSUB @recurse2
END

@recurse2
count2% = count2% + 1
IF count2% < 5000 THEN GOSUB @recurse2
RETURN
```

## Disassembly

```asm
0000:   SETEH       JUMP, 16            ; 1:1
0001:   GOSUB       7                   ; 2:7
0002:   LOADI       R65, 123            ; 3:5
0003:   LOADI       R64, 258            ; 3:5
0004:   UPCALL      0, R64              ; 3:1, OUT
0005:   LOADI       R64, 0              ; 4:1
0006:   END         R64                 ; 4:1
0007:   MOVE        R64, R64            ; 7:11
0008:   LOADI       R65, 1              ; 7:21
0009:   ADDI        R64, R64, R65       ; 7:19
0010:   MOVE        R65, R64            ; 8:4
0011:   LOADI       R66, 5000           ; 8:14
0012:   CMPLTI      R65, R65, R66       ; 8:12
0013:   JMPF        R65, 15             ; 8:4
0014:   GOSUB       7                   ; 8:30
0015:   RETURN                          ; 9:1
0016:   UPCALL      1, R66              ; 12:5, LAST_ERROR
0017:   LOADI       R65, 259            ; 12:5
0018:   UPCALL      0, R65              ; 12:1, OUT
0019:   GOSUB       22                  ; 13:7
0020:   LOADI       R65, 0              ; 14:1
0021:   END         R65                 ; 14:1
0022:   MOVE        R65, R65            ; 17:11
0023:   LOADI       R66, 1              ; 17:21
0024:   ADDI        R65, R65, R66       ; 17:19
0025:   MOVE        R66, R65            ; 18:4
0026:   LOADI       R67, 5000           ; 18:14
0027:   CMPLTI      R66, R66, R67       ; 18:12
0028:   JMPF        R66, 30             ; 18:4
0029:   GOSUB       22                  ; 18:30
0030:   RETURN                          ; 19:1
0031:   EOF                             ; 0:0
```

## Runtime errors

```plain
13:7: Out of call stack space
```

## Output

```plain
0=8:30: Out of call stack space$
```
