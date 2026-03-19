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
0000:   ENTER       4                   # 0:0
0001:   SETEH       JUMP, 13            # 1:1
0002:   LOADI       R65, 1              # 2:5
0003:   LOADI       R64, 258            # 2:5
0004:   UPCALL      0, R64              # 2:1, OUT
0005:   LOADI       R67, 0              # 3:12
0006:   UPCALL      1, R66              # 3:5, RAISEF
0007:   MOVE        R65, R66            # 3:5
0008:   LOADI       R64, 256            # 3:5
0009:   UPCALL      0, R64              # 3:1, OUT
0010:   LOADI       R65, 2              # 4:5
0011:   LOADI       R64, 258            # 4:5
0012:   UPCALL      0, R64              # 4:1, OUT
0013:   UPCALL      2, R65              # 5:9, LAST_ERROR
0014:   LOADI       R64, 259            # 5:9
0015:   UPCALL      0, R64              # 5:5, OUT
0016:   EOF                             # 0:0
```

## Output

```plain
0=1%
0=3:12: Some internal error$
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
0000:   ENTER       4                   # 0:0
0001:   SETEH       JUMP, 13            # 1:1
0002:   LOADI       R65, 1              # 2:5
0003:   LOADI       R64, 258            # 2:5
0004:   UPCALL      0, R64              # 2:1, OUT
0005:   LOADI       R67, 0              # 3:12
0006:   UPCALL      1, R66              # 3:5, RAISEF
0007:   MOVE        R65, R66            # 3:5
0008:   LOADI       R64, 256            # 3:5
0009:   UPCALL      0, R64              # 3:1, OUT
0010:   LOADI       R65, 2              # 4:5
0011:   LOADI       R64, 258            # 4:5
0012:   UPCALL      0, R64              # 4:1, OUT
0013:   UPCALL      2, R65              # 6:5, LAST_ERROR
0014:   LOADI       R64, 259            # 6:5
0015:   UPCALL      0, R64              # 6:1, OUT
0016:   EOF                             # 0:0
```

## Output

```plain
0=1%
0=3:12: Some internal error$
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
0000:   ENTER       4                   # 0:0
0001:   SETEH       JUMP, 10            # 1:1
0002:   LOADI       R65, 1              # 2:5
0003:   LOADI       R64, 258            # 2:5
0004:   UPCALL      0, R64              # 2:1, OUT
0005:   LOADI       R67, 0              # 3:12
0006:   UPCALL      1, R66              # 3:5, RAISEF
0007:   MOVE        R65, R66            # 3:5
0008:   LOADI       R64, 256            # 3:5
0009:   UPCALL      0, R64              # 3:1, OUT
0010:   SETEH       NONE, 0             # 5:1
0011:   LOADI       R65, 2              # 6:5
0012:   LOADI       R64, 258            # 6:5
0013:   UPCALL      0, R64              # 6:1, OUT
0014:   LOADI       R67, 0              # 7:12
0015:   UPCALL      1, R66              # 7:5, RAISEF
0016:   MOVE        R65, R66            # 7:5
0017:   LOADI       R64, 256            # 7:5
0018:   UPCALL      0, R64              # 7:1, OUT
0019:   EOF                             # 0:0
```

## Runtime errors

```plain
7:12: Some internal error
```

## Output

```plain
0=1%
0=2%
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
0000:   ENTER       4                   # 0:0
0001:   SETEH       RESUME_NEXT, 0      # 1:1
0002:   LOADI       R65, 1              # 2:5
0003:   LOADI       R64, 258            # 2:5
0004:   UPCALL      0, R64              # 2:1, OUT
0005:   LOADI       R67, 0              # 3:12
0006:   UPCALL      1, R66              # 3:5, RAISEF
0007:   MOVE        R65, R66            # 3:5
0008:   LOADI       R64, 256            # 3:5
0009:   UPCALL      0, R64              # 3:1, OUT
0010:   UPCALL      2, R65              # 4:5, LAST_ERROR
0011:   LOADI       R64, 259            # 4:5
0012:   UPCALL      0, R64              # 4:1, OUT
0013:   EOF                             # 0:0
```

## Output

```plain
0=1%
0=3:12: Some internal error$
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
0000:   ENTER       2                   # 0:0
0001:   SETEH       RESUME_NEXT, 0      # 1:1
0002:   LOADI       R65, 1              # 2:5
0003:   LOADI       R64, 258            # 2:5
0004:   UPCALL      0, R64              # 2:1, OUT
0005:   LOADI       R64, 0              # 3:7
0006:   UPCALL      1, R64              # 3:1, RAISE
0007:   UPCALL      2, R65              # 4:5, LAST_ERROR
0008:   LOADI       R64, 259            # 4:5
0009:   UPCALL      0, R64              # 4:1, OUT
0010:   EOF                             # 0:0
```

## Output

```plain
0=1%
0=3:7: Some internal error$
```

# Test: ON ERROR RESUME NEXT function failure in statement

## Source

```basic
ON ERROR RESUME NEXT
OUT 1: OUT RAISEF("internal"): OUT LAST_ERROR
```

## Disassembly

```asm
0000:   ENTER       4                   # 0:0
0001:   SETEH       RESUME_NEXT, 0      # 1:1
0002:   LOADI       R65, 1              # 2:5
0003:   LOADI       R64, 258            # 2:5
0004:   UPCALL      0, R64              # 2:1, OUT
0005:   LOADI       R67, 0              # 2:19
0006:   UPCALL      1, R66              # 2:12, RAISEF
0007:   MOVE        R65, R66            # 2:12
0008:   LOADI       R64, 256            # 2:12
0009:   UPCALL      0, R64              # 2:8, OUT
0010:   UPCALL      2, R65              # 2:36, LAST_ERROR
0011:   LOADI       R64, 259            # 2:36
0012:   UPCALL      0, R64              # 2:32, OUT
0013:   EOF                             # 0:0
```

## Output

```plain
0=1%
0=2:19: Some internal error$
```

# Test: ON ERROR RESUME NEXT command failure in statement

## Source

```basic
ON ERROR RESUME NEXT
OUT 1: RAISE "internal": OUT LAST_ERROR
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   SETEH       RESUME_NEXT, 0      # 1:1
0002:   LOADI       R65, 1              # 2:5
0003:   LOADI       R64, 258            # 2:5
0004:   UPCALL      0, R64              # 2:1, OUT
0005:   LOADI       R64, 0              # 2:14
0006:   UPCALL      1, R64              # 2:8, RAISE
0007:   UPCALL      2, R65              # 2:30, LAST_ERROR
0008:   LOADI       R64, 259            # 2:30
0009:   UPCALL      0, R64              # 2:26, OUT
0010:   EOF                             # 0:0
```

## Output

```plain
0=1%
0=2:14: Some internal error$
```

# Test: ON ERROR RESUME NEXT argument error

## Source

```basic
ON ERROR RESUME NEXT: OUT RAISEF("argument"): OUT LAST_ERROR
```

## Disassembly

```asm
0000:   ENTER       4                   # 0:0
0001:   SETEH       RESUME_NEXT, 0      # 1:1
0002:   LOADI       R67, 0              # 1:34
0003:   UPCALL      0, R66              # 1:27, RAISEF
0004:   MOVE        R65, R66            # 1:27
0005:   LOADI       R64, 256            # 1:27
0006:   UPCALL      1, R64              # 1:23, OUT
0007:   UPCALL      2, R65              # 1:51, LAST_ERROR
0008:   LOADI       R64, 259            # 1:51
0009:   UPCALL      1, R64              # 1:47, OUT
0010:   EOF                             # 0:0
```

## Output

```plain
0=1:34: Bad argument$
```

# Test: ON ERROR RESUME NEXT eval error

## Source

```basic
ON ERROR RESUME NEXT: OUT RAISEF("eval"): OUT LAST_ERROR
```

## Disassembly

```asm
0000:   ENTER       4                   # 0:0
0001:   SETEH       RESUME_NEXT, 0      # 1:1
0002:   LOADI       R67, 0              # 1:34
0003:   UPCALL      0, R66              # 1:27, RAISEF
0004:   MOVE        R65, R66            # 1:27
0005:   LOADI       R64, 256            # 1:27
0006:   UPCALL      1, R64              # 1:23, OUT
0007:   UPCALL      2, R65              # 1:47, LAST_ERROR
0008:   LOADI       R64, 259            # 1:47
0009:   UPCALL      1, R64              # 1:43, OUT
0010:   EOF                             # 0:0
```

## Output

```plain
0=1:34: Some eval error$
```

# Test: ON ERROR RESUME NEXT internal error

## Source

```basic
ON ERROR RESUME NEXT: OUT RAISEF("internal"): OUT LAST_ERROR
```

## Disassembly

```asm
0000:   ENTER       4                   # 0:0
0001:   SETEH       RESUME_NEXT, 0      # 1:1
0002:   LOADI       R67, 0              # 1:34
0003:   UPCALL      0, R66              # 1:27, RAISEF
0004:   MOVE        R65, R66            # 1:27
0005:   LOADI       R64, 256            # 1:27
0006:   UPCALL      1, R64              # 1:23, OUT
0007:   UPCALL      2, R65              # 1:51, LAST_ERROR
0008:   LOADI       R64, 259            # 1:51
0009:   UPCALL      1, R64              # 1:47, OUT
0010:   EOF                             # 0:0
```

## Output

```plain
0=1:34: Some internal error$
```

# Test: ON ERROR RESUME NEXT I/O error

## Source

```basic
ON ERROR RESUME NEXT: OUT RAISEF("io"): OUT LAST_ERROR
```

## Disassembly

```asm
0000:   ENTER       4                   # 0:0
0001:   SETEH       RESUME_NEXT, 0      # 1:1
0002:   LOADI       R67, 0              # 1:34
0003:   UPCALL      0, R66              # 1:27, RAISEF
0004:   MOVE        R65, R66            # 1:27
0005:   LOADI       R64, 256            # 1:27
0006:   UPCALL      1, R64              # 1:23, OUT
0007:   UPCALL      2, R65              # 1:45, LAST_ERROR
0008:   LOADI       R64, 259            # 1:45
0009:   UPCALL      1, R64              # 1:41, OUT
0010:   EOF                             # 0:0
```

## Output

```plain
0=1:34: Some I/O error$
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
