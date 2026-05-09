# Test: Command syntax error from single arg

## Source

```basic
RAISE "syntax"
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:7
0001:   UPCALL      0, R64              ; 1:1, RAISE
0002:   EOF                             ; 0:0
```

## Runtime errors

```plain
1:7: Some syntax error
```

# Test: Command syntax error pointing at first arg

## Source

```basic
RAISE "syntax0", 5
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:7
0001:   LOADI       R65, 5              ; 1:18
0002:   UPCALL      0, R64              ; 1:1, RAISE
0003:   EOF                             ; 0:0
```

## Runtime errors

```plain
1:7: Some syntax error
```

# Test: Command syntax error pointing at second arg

## Source

```basic
RAISE "syntax1", 5
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:7
0001:   LOADI       R65, 5              ; 1:18
0002:   UPCALL      0, R64              ; 1:1, RAISE
0003:   EOF                             ; 0:0
```

## Runtime errors

```plain
1:18: Some syntax error
```

# Test: Command syntax error at second arg with ON ERROR RESUME NEXT

## Source

```basic
ON ERROR RESUME NEXT: RAISE "syntax1", 5: OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       RESUME_NEXT, 0      ; 1:1
0001:   LOADI       R64, 0              ; 1:29
0002:   LOADI       R65, 5              ; 1:40
0003:   UPCALL      0, R64              ; 1:23, RAISE
0004:   UPCALL      1, R65              ; 1:47, LAST_ERROR
0005:   LOADI       R64, 259            ; 1:47
0006:   UPCALL      2, R64              ; 1:43, OUT
0007:   EOF                             ; 0:0
```

## Output

```plain
0=1:40: Some syntax error$
```

# Test: Command syntax error at first arg with ON ERROR RESUME NEXT

## Source

```basic
ON ERROR RESUME NEXT: RAISE "syntax0", 5: OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       RESUME_NEXT, 0      ; 1:1
0001:   LOADI       R64, 0              ; 1:29
0002:   LOADI       R65, 5              ; 1:40
0003:   UPCALL      0, R64              ; 1:23, RAISE
0004:   UPCALL      1, R65              ; 1:47, LAST_ERROR
0005:   LOADI       R64, 259            ; 1:47
0006:   UPCALL      2, R64              ; 1:43, OUT
0007:   EOF                             ; 0:0
```

## Output

```plain
0=1:29: Some syntax error$
```

# Test: Command syntax error with ON ERROR GOTO

## Source

```basic
ON ERROR GOTO @handler
RAISE "syntax"
OUT 1
@handler
OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       JUMP, 6             ; 1:1
0001:   LOADI       R64, 0              ; 2:7
0002:   UPCALL      0, R64              ; 2:1, RAISE
0003:   LOADI       R65, 1              ; 3:5
0004:   LOADI       R64, 258            ; 3:5
0005:   UPCALL      1, R64              ; 3:1, OUT
0006:   UPCALL      2, R65              ; 5:5, LAST_ERROR
0007:   LOADI       R64, 259            ; 5:5
0008:   UPCALL      1, R64              ; 5:1, OUT
0009:   EOF                             ; 0:0
```

## Output

```plain
0=2:7: Some syntax error$
```

# Test: Function syntax error from single arg

## Source

```basic
OUT RAISEF("syntax")
```

## Disassembly

```asm
0000:   LOADI       R67, 0              ; 1:12
0001:   UPCALL      0, R66              ; 1:5, RAISEF
0002:   MOVE        R65, R66            ; 1:5
0003:   LOADI       R64, 256            ; 1:5
0004:   UPCALL      1, R64              ; 1:1, OUT
0005:   EOF                             ; 0:0
```

## Runtime errors

```plain
1:12: Some syntax error
```

# Test: Function syntax error pointing at second arg

## Source

```basic
OUT RAISEF("syntax1", 5)
```

## Disassembly

```asm
0000:   LOADI       R67, 0              ; 1:12
0001:   LOADI       R68, 5              ; 1:23
0002:   UPCALL      0, R66              ; 1:5, RAISEF
0003:   MOVE        R65, R66            ; 1:5
0004:   LOADI       R64, 256            ; 1:5
0005:   UPCALL      1, R64              ; 1:1, OUT
0006:   EOF                             ; 0:0
```

## Runtime errors

```plain
1:23: Some syntax error
```

# Test: Function syntax error with ON ERROR RESUME NEXT

## Source

```basic
ON ERROR RESUME NEXT: OUT RAISEF("syntax"): OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       RESUME_NEXT, 0      ; 1:1
0001:   LOADI       R67, 0              ; 1:34
0002:   UPCALL      0, R66              ; 1:27, RAISEF
0003:   MOVE        R65, R66            ; 1:27
0004:   LOADI       R64, 256            ; 1:27
0005:   UPCALL      1, R64              ; 1:23, OUT
0006:   UPCALL      2, R65              ; 1:49, LAST_ERROR
0007:   LOADI       R64, 259            ; 1:49
0008:   UPCALL      1, R64              ; 1:45, OUT
0009:   EOF                             ; 0:0
```

## Output

```plain
0=1:34: Some syntax error$
```

# Test: Function syntax error at second arg with ON ERROR RESUME NEXT

## Source

```basic
ON ERROR RESUME NEXT: OUT RAISEF("syntax1", 5): OUT LAST_ERROR
```

## Disassembly

```asm
0000:   SETEH       RESUME_NEXT, 0      ; 1:1
0001:   LOADI       R67, 0              ; 1:34
0002:   LOADI       R68, 5              ; 1:45
0003:   UPCALL      0, R66              ; 1:27, RAISEF
0004:   MOVE        R65, R66            ; 1:27
0005:   LOADI       R64, 256            ; 1:27
0006:   UPCALL      1, R64              ; 1:23, OUT
0007:   UPCALL      2, R65              ; 1:53, LAST_ERROR
0008:   LOADI       R64, 259            ; 1:53
0009:   UPCALL      1, R64              ; 1:49, OUT
0010:   EOF                             ; 0:0
```

## Output

```plain
0=1:45: Some syntax error$
```
