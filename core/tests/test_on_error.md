# Test: ON ERROR GOTO line

## Source

```basic
ON ERROR GOTO 100
OUT 1
OUT RAISEF("internal")
OUT 2
100 OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       JUMP, 12            ; 1:1
0001:   LOADI       R65, 1              ; 2:5
0002:   LOADI       R64, 258            ; 2:5
0003:   UPCALL      0, R64              ; 2:1, OUT
0004:   LOADI       R67, 0              ; 3:12
0005:   UPCALL      1, R66              ; 3:5, RAISEF
0006:   MOVE        R65, R66            ; 3:5
0007:   LOADI       R64, 256            ; 3:5
0008:   UPCALL      0, R64              ; 3:1, OUT
0009:   LOADI       R65, 2              ; 4:5
0010:   LOADI       R64, 258            ; 4:5
0011:   UPCALL      0, R64              ; 4:1, OUT
0012:   UPCALL      2, R65              ; 5:9, LAST_ERROR
0013:   LOADI       R64, 259            ; 5:9
0014:   UPCALL      0, R64              ; 5:5, OUT
0015:   EOF                             ; 0:0
```

## Output

```plain
0=1%
0=3:5: Some internal error$
```

# Test: ON ERROR GOTO label

## Source

```basic
ON ERROR GOTO @foo
OUT 1
OUT RAISEF("internal")
OUT 2
@foo
OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       JUMP, 12            ; 1:1
0001:   LOADI       R65, 1              ; 2:5
0002:   LOADI       R64, 258            ; 2:5
0003:   UPCALL      0, R64              ; 2:1, OUT
0004:   LOADI       R67, 0              ; 3:12
0005:   UPCALL      1, R66              ; 3:5, RAISEF
0006:   MOVE        R65, R66            ; 3:5
0007:   LOADI       R64, 256            ; 3:5
0008:   UPCALL      0, R64              ; 3:1, OUT
0009:   LOADI       R65, 2              ; 4:5
0010:   LOADI       R64, 258            ; 4:5
0011:   UPCALL      0, R64              ; 4:1, OUT
0012:   UPCALL      2, R65              ; 6:5, LAST_ERROR
0013:   LOADI       R64, 259            ; 6:5
0014:   UPCALL      0, R64              ; 6:1, OUT
0015:   EOF                             ; 0:0
```

## Output

```plain
0=1%
0=3:5: Some internal error$
```

# Test: ON ERROR reset

## Source

```basic
ON ERROR GOTO @foo
OUT 1
OUT RAISEF("internal")
@foo
ON ERROR GOTO 0
OUT 2
OUT RAISEF("internal")
```

## Disassembly

```asm
0000:   SETEH       JUMP, 9             ; 1:1
0001:   LOADI       R65, 1              ; 2:5
0002:   LOADI       R64, 258            ; 2:5
0003:   UPCALL      0, R64              ; 2:1, OUT
0004:   LOADI       R67, 0              ; 3:12
0005:   UPCALL      1, R66              ; 3:5, RAISEF
0006:   MOVE        R65, R66            ; 3:5
0007:   LOADI       R64, 256            ; 3:5
0008:   UPCALL      0, R64              ; 3:1, OUT
0009:   SETEH       NONE, 0             ; 5:1
0010:   LOADI       R65, 2              ; 6:5
0011:   LOADI       R64, 258            ; 6:5
0012:   UPCALL      0, R64              ; 6:1, OUT
0013:   LOADI       R67, 0              ; 7:12
0014:   UPCALL      1, R66              ; 7:5, RAISEF
0015:   MOVE        R65, R66            ; 7:5
0016:   LOADI       R64, 256            ; 7:5
0017:   UPCALL      0, R64              ; 7:1, OUT
0018:   EOF                             ; 0:0
```

## Runtime errors

```plain
7:5: Some internal error
```

## Output

```plain
0=1%
0=2%
```

# Test: ON ERROR GOTO must be re-armed after handling an error

## Source

```basic
ON ERROR GOTO @handler1
RAISE "internal"
OUT 1
END

@handler1
OUT LAST_ERROR
ON ERROR GOTO @handler2
RAISE "syntax"
END

@handler2
OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       JUMP, 8             ; 1:1
0001:   LOADI       R64, 0              ; 2:7
0002:   UPCALL      0, R64              ; 2:1, RAISE
0003:   LOADI       R65, 1              ; 3:5
0004:   LOADI       R64, 258            ; 3:5
0005:   UPCALL      1, R64              ; 3:1, OUT
0006:   LOADI       R64, 0              ; 4:1
0007:   END         R64                 ; 4:1
0008:   UPCALL      2, R65              ; 7:5, LAST_ERROR
0009:   LOADI       R64, 259            ; 7:5
0010:   UPCALL      1, R64              ; 7:1, OUT
0011:   SETEH       JUMP, 16            ; 8:1
0012:   LOADI       R64, 1              ; 9:7
0013:   UPCALL      0, R64              ; 9:1, RAISE
0014:   LOADI       R64, 0              ; 10:1
0015:   END         R64                 ; 10:1
0016:   UPCALL      2, R65              ; 13:5, LAST_ERROR
0017:   LOADI       R64, 259            ; 13:5
0018:   UPCALL      1, R64              ; 13:1, OUT
0019:   EOF                             ; 0:0
```

## Output

```plain
0=2:1: Some internal error$
0=9:7: Some syntax error$
```

# Test: ON ERROR GOTO is not reentrant after handling an error

## Source

```basic
ON ERROR GOTO @handler
RAISE "internal"
OUT 1
END

@handler
OUT LAST_ERROR
RAISE "syntax"
END
```

## Disassembly

```asm
0000:   SETEH       JUMP, 8             ; 1:1
0001:   LOADI       R64, 0              ; 2:7
0002:   UPCALL      0, R64              ; 2:1, RAISE
0003:   LOADI       R65, 1              ; 3:5
0004:   LOADI       R64, 258            ; 3:5
0005:   UPCALL      1, R64              ; 3:1, OUT
0006:   LOADI       R64, 0              ; 4:1
0007:   END         R64                 ; 4:1
0008:   UPCALL      2, R65              ; 7:5, LAST_ERROR
0009:   LOADI       R64, 259            ; 7:5
0010:   UPCALL      1, R64              ; 7:1, OUT
0011:   LOADI       R64, 1              ; 8:7
0012:   UPCALL      0, R64              ; 8:1, RAISE
0013:   LOADI       R64, 0              ; 9:1
0014:   END         R64                 ; 9:1
0015:   EOF                             ; 0:0
```

## Runtime errors

```plain
8:7: Some syntax error
```

## Output

```plain
0=2:1: Some internal error$
```

# Test: ON ERROR RESUME NEXT function failure

## Source

```basic
ON ERROR RESUME NEXT
OUT 1
OUT RAISEF("internal")
OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       RESUME_NEXT, 0      ; 1:1
0001:   LOADI       R65, 1              ; 2:5
0002:   LOADI       R64, 258            ; 2:5
0003:   UPCALL      0, R64              ; 2:1, OUT
0004:   LOADI       R67, 0              ; 3:12
0005:   UPCALL      1, R66              ; 3:5, RAISEF
0006:   MOVE        R65, R66            ; 3:5
0007:   LOADI       R64, 256            ; 3:5
0008:   UPCALL      0, R64              ; 3:1, OUT
0009:   UPCALL      2, R65              ; 4:5, LAST_ERROR
0010:   LOADI       R64, 259            ; 4:5
0011:   UPCALL      0, R64              ; 4:1, OUT
0012:   EOF                             ; 0:0
```

## Output

```plain
0=1%
0=3:5: Some internal error$
```

# Test: ON ERROR RESUME NEXT command failure

## Source

```basic
ON ERROR RESUME NEXT
OUT 1
RAISE "internal"
OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       RESUME_NEXT, 0      ; 1:1
0001:   LOADI       R65, 1              ; 2:5
0002:   LOADI       R64, 258            ; 2:5
0003:   UPCALL      0, R64              ; 2:1, OUT
0004:   LOADI       R64, 0              ; 3:7
0005:   UPCALL      1, R64              ; 3:1, RAISE
0006:   UPCALL      2, R65              ; 4:5, LAST_ERROR
0007:   LOADI       R64, 259            ; 4:5
0008:   UPCALL      0, R64              ; 4:1, OUT
0009:   EOF                             ; 0:0
```

## Output

```plain
0=1%
0=3:1: Some internal error$
```

# Test: ON ERROR RESUME NEXT handles multiple failures without re-arming

## Source

```basic
ON ERROR RESUME NEXT
RAISE "internal"
OUT LAST_ERROR
RAISE "syntax"
OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       RESUME_NEXT, 0      ; 1:1
0001:   LOADI       R64, 0              ; 2:7
0002:   UPCALL      0, R64              ; 2:1, RAISE
0003:   UPCALL      1, R65              ; 3:5, LAST_ERROR
0004:   LOADI       R64, 259            ; 3:5
0005:   UPCALL      2, R64              ; 3:1, OUT
0006:   LOADI       R64, 1              ; 4:7
0007:   UPCALL      0, R64              ; 4:1, RAISE
0008:   UPCALL      1, R65              ; 5:5, LAST_ERROR
0009:   LOADI       R64, 259            ; 5:5
0010:   UPCALL      2, R64              ; 5:1, OUT
0011:   EOF                             ; 0:0
```

## Output

```plain
0=2:1: Some internal error$
0=4:7: Some syntax error$
```

# Test: ON ERROR RESUME NEXT function failure in statement

## Source

```basic
ON ERROR RESUME NEXT
OUT 1: OUT RAISEF("internal"): OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       RESUME_NEXT, 0      ; 1:1
0001:   LOADI       R65, 1              ; 2:5
0002:   LOADI       R64, 258            ; 2:5
0003:   UPCALL      0, R64              ; 2:1, OUT
0004:   LOADI       R67, 0              ; 2:19
0005:   UPCALL      1, R66              ; 2:12, RAISEF
0006:   MOVE        R65, R66            ; 2:12
0007:   LOADI       R64, 256            ; 2:12
0008:   UPCALL      0, R64              ; 2:8, OUT
0009:   UPCALL      2, R65              ; 2:36, LAST_ERROR
0010:   LOADI       R64, 259            ; 2:36
0011:   UPCALL      0, R64              ; 2:32, OUT
0012:   EOF                             ; 0:0
```

## Output

```plain
0=1%
0=2:12: Some internal error$
```

# Test: ON ERROR RESUME NEXT command failure in statement

## Source

```basic
ON ERROR RESUME NEXT
OUT 1: RAISE "internal": OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       RESUME_NEXT, 0      ; 1:1
0001:   LOADI       R65, 1              ; 2:5
0002:   LOADI       R64, 258            ; 2:5
0003:   UPCALL      0, R64              ; 2:1, OUT
0004:   LOADI       R64, 0              ; 2:14
0005:   UPCALL      1, R64              ; 2:8, RAISE
0006:   UPCALL      2, R65              ; 2:30, LAST_ERROR
0007:   LOADI       R64, 259            ; 2:30
0008:   UPCALL      0, R64              ; 2:26, OUT
0009:   EOF                             ; 0:0
```

## Output

```plain
0=1%
0=2:8: Some internal error$
```

# Test: ON ERROR RESUME NEXT argument error

## Source

```basic
ON ERROR RESUME NEXT: OUT RAISEF("argument"): OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       RESUME_NEXT, 0      ; 1:1
0001:   LOADI       R67, 0              ; 1:34
0002:   UPCALL      0, R66              ; 1:27, RAISEF
0003:   MOVE        R65, R66            ; 1:27
0004:   LOADI       R64, 256            ; 1:27
0005:   UPCALL      1, R64              ; 1:23, OUT
0006:   UPCALL      2, R65              ; 1:51, LAST_ERROR
0007:   LOADI       R64, 259            ; 1:51
0008:   UPCALL      1, R64              ; 1:47, OUT
0009:   EOF                             ; 0:0
```

## Output

```plain
0=1:27: Bad argument$
```

# Test: ON ERROR RESUME NEXT eval error

## Source

```basic
ON ERROR RESUME NEXT: OUT RAISEF("eval"): OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       RESUME_NEXT, 0      ; 1:1
0001:   LOADI       R67, 0              ; 1:34
0002:   UPCALL      0, R66              ; 1:27, RAISEF
0003:   MOVE        R65, R66            ; 1:27
0004:   LOADI       R64, 256            ; 1:27
0005:   UPCALL      1, R64              ; 1:23, OUT
0006:   UPCALL      2, R65              ; 1:47, LAST_ERROR
0007:   LOADI       R64, 259            ; 1:47
0008:   UPCALL      1, R64              ; 1:43, OUT
0009:   EOF                             ; 0:0
```

## Output

```plain
0=1:27: Some eval error$
```

# Test: ON ERROR RESUME NEXT internal error

## Source

```basic
ON ERROR RESUME NEXT: OUT RAISEF("internal"): OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       RESUME_NEXT, 0      ; 1:1
0001:   LOADI       R67, 0              ; 1:34
0002:   UPCALL      0, R66              ; 1:27, RAISEF
0003:   MOVE        R65, R66            ; 1:27
0004:   LOADI       R64, 256            ; 1:27
0005:   UPCALL      1, R64              ; 1:23, OUT
0006:   UPCALL      2, R65              ; 1:51, LAST_ERROR
0007:   LOADI       R64, 259            ; 1:51
0008:   UPCALL      1, R64              ; 1:47, OUT
0009:   EOF                             ; 0:0
```

## Output

```plain
0=1:27: Some internal error$
```

# Test: ON ERROR RESUME NEXT I/O error

## Source

```basic
ON ERROR RESUME NEXT: OUT RAISEF("io"): OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       RESUME_NEXT, 0      ; 1:1
0001:   LOADI       R67, 0              ; 1:34
0002:   UPCALL      0, R66              ; 1:27, RAISEF
0003:   MOVE        R65, R66            ; 1:27
0004:   LOADI       R64, 256            ; 1:27
0005:   UPCALL      1, R64              ; 1:23, OUT
0006:   UPCALL      2, R65              ; 1:45, LAST_ERROR
0007:   LOADI       R64, 259            ; 1:45
0008:   UPCALL      1, R64              ; 1:41, OUT
0009:   EOF                             ; 0:0
```

## Output

```plain
0=1:27: Some I/O error$
```

# Test: ON ERROR GOTO unknown label

## Source

```basic
ON ERROR GOTO @foo
```

## Compilation errors

```plain
1:1: Unknown label foo
```
