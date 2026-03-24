# Test: Basic flow

## Source

```basic
OUT "a"
GOSUB @sub
OUT "c"
END

@sub:
OUT "b"
RETURN
```

## Disassembly

```asm
0000:   LOADI       R65, 0              ; 1:5
0001:   LOADI       R64, 259            ; 1:5
0002:   UPCALL      0, R64              ; 1:1, OUT
0003:   GOSUB       9                   ; 2:7
0004:   LOADI       R65, 1              ; 3:5
0005:   LOADI       R64, 259            ; 3:5
0006:   UPCALL      0, R64              ; 3:1, OUT
0007:   LOADI       R64, 0              ; 4:1
0008:   END         R64                 ; 4:1
0009:   LOADI       R65, 2              ; 7:5
0010:   LOADI       R64, 259            ; 7:5
0011:   UPCALL      0, R64              ; 7:1, OUT
0012:   RETURN                          ; 8:1
0013:   EOF                             ; 0:0
```

## Output

```plain
0=a$
0=b$
0=c$
```

# Test: GOSUB with numeric label

## Source

```basic
GOSUB 100
END
100 OUT "in gosub"
RETURN
```

## Disassembly

```asm
0000:   GOSUB       3                   ; 1:7
0001:   LOADI       R64, 0              ; 2:1
0002:   END         R64                 ; 2:1
0003:   LOADI       R65, 0              ; 3:9
0004:   LOADI       R64, 259            ; 3:9
0005:   UPCALL      0, R64              ; 3:5, OUT
0006:   RETURN                          ; 4:1
0007:   EOF                             ; 0:0
```

## Output

```plain
0=in gosub$
```

# Test: Nested GOSUB calls and returns

## Source

```basic
OUT "a"
GOSUB @sub1
OUT "f"
END

@sub1:
OUT "b"
GOSUB @sub2
OUT "e"
RETURN

@sub2:
OUT "c"
GOSUB @sub3
OUT "d"
RETURN

@sub3:
OUT "hello"
RETURN
```

## Disassembly

```asm
0000:   LOADI       R65, 0              ; 1:5
0001:   LOADI       R64, 259            ; 1:5
0002:   UPCALL      0, R64              ; 1:1, OUT
0003:   GOSUB       9                   ; 2:7
0004:   LOADI       R65, 1              ; 3:5
0005:   LOADI       R64, 259            ; 3:5
0006:   UPCALL      0, R64              ; 3:1, OUT
0007:   LOADI       R64, 0              ; 4:1
0008:   END         R64                 ; 4:1
0009:   LOADI       R65, 2              ; 7:5
0010:   LOADI       R64, 259            ; 7:5
0011:   UPCALL      0, R64              ; 7:1, OUT
0012:   GOSUB       17                  ; 8:7
0013:   LOADI       R65, 3              ; 9:5
0014:   LOADI       R64, 259            ; 9:5
0015:   UPCALL      0, R64              ; 9:1, OUT
0016:   RETURN                          ; 10:1
0017:   LOADI       R65, 4              ; 13:5
0018:   LOADI       R64, 259            ; 13:5
0019:   UPCALL      0, R64              ; 13:1, OUT
0020:   GOSUB       25                  ; 14:7
0021:   LOADI       R65, 5              ; 15:5
0022:   LOADI       R64, 259            ; 15:5
0023:   UPCALL      0, R64              ; 15:1, OUT
0024:   RETURN                          ; 16:1
0025:   LOADI       R65, 6              ; 19:5
0026:   LOADI       R64, 259            ; 19:5
0027:   UPCALL      0, R64              ; 19:1, OUT
0028:   RETURN                          ; 20:1
0029:   EOF                             ; 0:0
```

## Output

```plain
0=a$
0=b$
0=c$
0=hello$
0=d$
0=e$
0=f$
```

# Test: RETURN without GOSUB

## Source

```basic
RETURN
```

## Disassembly

```asm
0000:   RETURN                          ; 1:1
0001:   EOF                             ; 0:0
```

## Runtime errors

```plain
1:1: RETURN without GOSUB or FUNCTION call
```

# Test: GOSUB target requires backwards jump

## Source

```basic
GOTO @skip

@s:
OUT "In target"
RETURN

@skip:
GOSUB @s
```

## Disassembly

```asm
0000:   JUMP        5                   ; 1:6
0001:   LOADI       R65, 0              ; 4:5
0002:   LOADI       R64, 259            ; 4:5
0003:   UPCALL      0, R64              ; 4:1, OUT
0004:   RETURN                          ; 5:1
0005:   GOSUB       1                   ; 8:7
0006:   EOF                             ; 0:0
```

## Output

```plain
0=In target$
```

# Test: GOSUB without RETURN still runs target

## Source

```basic
GOSUB @sub: @sub: OUT 1
```

## Disassembly

```asm
0000:   GOSUB       1                   ; 1:7
0001:   LOADI       R65, 1              ; 1:23
0002:   LOADI       R64, 258            ; 1:23
0003:   UPCALL      0, R64              ; 1:19, OUT
0004:   EOF                             ; 0:0
```

## Output

```plain
0=1%
```

# Test: RETURN reached by GOTO fails

## Source

```basic
GOTO @foo
@foo:
RETURN
```

## Disassembly

```asm
0000:   JUMP        1                   ; 1:6
0001:   RETURN                          ; 3:1
0002:   EOF                             ; 0:0
```

## Runtime errors

```plain
3:1: RETURN without GOSUB or FUNCTION call
```
