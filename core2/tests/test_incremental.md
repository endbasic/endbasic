# Test: Smoke test

## Source (partial)

```basic
OUT 1
```

## Disassembly (full)

```asm
0000:   LOADI       R65, 1              ; 1:5
0001:   LOADI       R64, 258            ; 1:5
0002:   UPCALL      0, R64              ; 1:1, OUT
0003:   EOF                             ; 0:0
```

## Output (partial)

```plain
0=1%
```

## Source (partial)

```basic
OUT 2
```

## Disassembly (full)

```asm
0000:   LOADI       R65, 1              ; 1:5
0001:   LOADI       R64, 258            ; 1:5
0002:   UPCALL      0, R64              ; 1:1, OUT
0003:   LOADI       R65, 2              ; 1:5
0004:   LOADI       R64, 258            ; 1:5
0005:   UPCALL      0, R64              ; 1:1, OUT
0006:   EOF                             ; 0:0
```

## Output (partial)

```plain
0=2%
```

# Test: Program-scope variables persist across compiles

## Source (partial)

```basic
a = 3
OUT a
```

## Disassembly (full)

```asm
0000:   LOADI       R64, 3              ; 1:5
0001:   MOVE        R66, R64            ; 2:5
0002:   LOADI       R65, 258            ; 2:5
0003:   UPCALL      0, R65              ; 2:1, OUT
0004:   EOF                             ; 0:0
```

## Output (partial)

```plain
0=3%
```

## Source (partial)

```basic
OUT a
```

## Disassembly (full)

```asm
0000:   LOADI       R64, 3              ; 1:5
0001:   MOVE        R66, R64            ; 2:5
0002:   LOADI       R65, 258            ; 2:5
0003:   UPCALL      0, R65              ; 2:1, OUT
0004:   MOVE        R66, R64            ; 1:5
0005:   LOADI       R65, 258            ; 1:5
0006:   UPCALL      0, R65              ; 1:1, OUT
0007:   EOF                             ; 0:0
```

## Output (partial)

```plain
0=3%
```

# Test: Program-scope variables do not leak into functions

## Source (partial)

```basic
a = 3
```

## Disassembly (full)

```asm
0000:   LOADI       R64, 3              ; 1:5
0001:   EOF                             ; 0:0
```

## Source (partial)

```basic
FUNCTION get_a
    OUT a
END FUNCTION
```

## Compiler errors (partial)

```plain
2:9: Undefined symbol a
```

## Source (partial)

```basic
OUT a
```

## Disassembly (full)

```asm
0000:   LOADI       R64, 3              ; 1:5
0001:   MOVE        R66, R64            ; 1:5
0002:   LOADI       R65, 258            ; 1:5
0003:   UPCALL      0, R65              ; 1:1, OUT
0004:   EOF                             ; 0:0
```

## Output (partial)

```plain
0=3%
```

# Test: User-defined callables are available in later compiles

## Source (partial)

```basic
FUNCTION double_it(n AS INTEGER)
    double_it = n * 2
END FUNCTION

SUB say_hello
    OUT "hello"
END SUB
```

## Disassembly (full)

```asm
0000:   JUMP        6                   ; 1:10

;; DOUBLE_IT (BEGIN)
0001:   LOADI       R64, 0              ; 1:10
0002:   MOVE        R64, R65            ; 2:17
0003:   LOADI       R66, 2              ; 2:21
0004:   MULI        R64, R64, R66       ; 2:19
0005:   RETURN                          ; 3:1
;; DOUBLE_IT (END)

0006:   JUMP        11                  ; 5:5

;; SAY_HELLO (BEGIN)
0007:   LOADI       R65, 0              ; 6:9
0008:   LOADI       R64, 259            ; 6:9
0009:   UPCALL      0, R64              ; 6:5, OUT
0010:   RETURN                          ; 7:1
;; SAY_HELLO (END)

0011:   EOF                             ; 0:0
```

## Source (partial)

```basic
OUT double_it(4)
say_hello
```

## Disassembly (full)

```asm
0000:   JUMP        6                   ; 1:10

;; DOUBLE_IT (BEGIN)
0001:   LOADI       R64, 0              ; 1:10
0002:   MOVE        R64, R65            ; 2:17
0003:   LOADI       R66, 2              ; 2:21
0004:   MULI        R64, R64, R66       ; 2:19
0005:   RETURN                          ; 3:1
;; DOUBLE_IT (END)

0006:   JUMP        11                  ; 5:5

;; SAY_HELLO (BEGIN)
0007:   LOADI       R65, 0              ; 6:9
0008:   LOADI       R64, 259            ; 6:9
0009:   UPCALL      0, R64              ; 6:5, OUT
0010:   RETURN                          ; 7:1
;; SAY_HELLO (END)

0011:   LOADI       R67, 4              ; 1:15
0012:   CALL        R66, 1              ; 1:5, DOUBLE_IT
0013:   MOVE        R65, R66            ; 1:5
0014:   LOADI       R64, 258            ; 1:5
0015:   UPCALL      0, R64              ; 1:1, OUT
0016:   CALL        R64, 7              ; 2:1, SAY_HELLO
0017:   EOF                             ; 0:0
```

## Output (partial)

```plain
0=8%
0=hello$
```

# Test: DATA accumulates across later compiles

## Source (partial)

```basic
DATA 1
```

## Disassembly (full)

```asm
0000:   EOF                             ; 0:0
```

## Source (partial)

```basic
DATA 2
GETDATA
```

## Disassembly (full)

```asm
0000:   UPCALL      0, R64              ; 2:1, GETDATA
0001:   EOF                             ; 0:0
```

## Output (partial)

```plain
0=1% 1=2%
```

## Source (partial)

```basic
DATA 3
GETDATA
```

## Disassembly (full)

```asm
0000:   UPCALL      0, R64              ; 2:1, GETDATA
0001:   UPCALL      0, R64              ; 2:1, GETDATA
0002:   EOF                             ; 0:0
```

## Output (partial)

```plain
0=1% 1=2% 2=3%
```

# Test: Failed compile does not define ghost program variables

## Source (partial)

```basic
a = 5
```

## Disassembly (full)

```asm
0000:   LOADI       R64, 5              ; 1:5
0001:   EOF                             ; 0:0
```

## Source (partial)

```basic
c = b + 3
```

## Compiler errors (partial)

```plain
1:5: Undefined symbol b
```

## Source (partial)

```basic
OUT a, c
```

## Compiler errors (partial)

```plain
1:8: Undefined symbol c
```

## Source (partial)

```basic
OUT a
```

## Disassembly (full)

```asm
0000:   LOADI       R64, 5              ; 1:5
0001:   MOVE        R66, R64            ; 1:5
0002:   LOADI       R65, 258            ; 1:5
0003:   UPCALL      0, R65              ; 1:1, OUT
0004:   EOF                             ; 0:0
```

## Output (partial)

```plain
0=5%
```

# Test: Failed compile does not define ghost callables

## Source (partial)

```basic
FUNCTION stable
    stable = 7
END FUNCTION
```

## Disassembly (full)

```asm
0000:   JUMP        4                   ; 1:10

;; STABLE (BEGIN)
0001:   LOADI       R64, 0              ; 1:10
0002:   LOADI       R64, 7              ; 2:14
0003:   RETURN                          ; 3:1
;; STABLE (END)

0004:   EOF                             ; 0:0
```

## Source (partial)

```basic
FUNCTION broken
    broken = missing + 1
END FUNCTION
```

## Compiler errors (partial)

```plain
2:14: Undefined symbol missing
```

## Source (partial)

```basic
OUT stable, broken
```

## Compiler errors (partial)

```plain
1:13: Undefined symbol broken
```

## Source (partial)

```basic
OUT stable
```

## Disassembly (full)

```asm
0000:   JUMP        4                   ; 1:10

;; STABLE (BEGIN)
0001:   LOADI       R64, 0              ; 1:10
0002:   LOADI       R64, 7              ; 2:14
0003:   RETURN                          ; 3:1
;; STABLE (END)

0004:   CALL        R65, 1              ; 1:5, STABLE
0005:   LOADI       R64, 258            ; 1:5
0006:   UPCALL      0, R64              ; 1:1, OUT
0007:   EOF                             ; 0:0
```

## Output (partial)

```plain
0=7%
```

# Test: Failed DATA chunk does not taint prior state

## Source (partial)

```basic
DATA 9
```

## Disassembly (full)

```asm
0000:   EOF                             ; 0:0
```

## Source (partial)

```basic
DATA 1 + 2
```

## Compiler errors (partial)

```plain
1:8: Expected comma after datum but found +
```

## Source (partial)

```basic
DATA 10
GETDATA
```

## Disassembly (full)

```asm
0000:   UPCALL      0, R64              ; 2:1, GETDATA
0001:   EOF                             ; 0:0
```

## Output (partial)

```plain
0=9% 1=10%
```

# Test: Explicit END does not block later compiles

## Source (partial)

```basic
OUT 1
```

## Disassembly (full)

```asm
0000:   LOADI       R65, 1              ; 1:5
0001:   LOADI       R64, 258            ; 1:5
0002:   UPCALL      0, R64              ; 1:1, OUT
0003:   EOF                             ; 0:0
```

## Output (partial)

```plain
0=1%
```

## Source (partial)

```basic
END 3
```

## Disassembly (full)

```asm
0000:   LOADI       R65, 1              ; 1:5
0001:   LOADI       R64, 258            ; 1:5
0002:   UPCALL      0, R64              ; 1:1, OUT
0003:   LOADI       R64, 3              ; 1:5
0004:   END         R64                 ; 1:1
0005:   EOF                             ; 0:0
```

## Exit code (partial)

```plain
3
```

## Source (partial)

```basic
OUT 2
```

## Disassembly (full)

```asm
0000:   LOADI       R65, 1              ; 1:5
0001:   LOADI       R64, 258            ; 1:5
0002:   UPCALL      0, R64              ; 1:1, OUT
0003:   LOADI       R64, 3              ; 1:5
0004:   END         R64                 ; 1:1
0005:   LOADI       R65, 2              ; 1:5
0006:   LOADI       R64, 258            ; 1:5
0007:   UPCALL      0, R64              ; 1:1, OUT
0008:   EOF                             ; 0:0
```

## Output (partial)

```plain
0=2%
```

# Test: Runtime errors do not block later compiles

## Source (partial)

```basic
OUT 1
```

## Disassembly (full)

```asm
0000:   LOADI       R65, 1              ; 1:5
0001:   LOADI       R64, 258            ; 1:5
0002:   UPCALL      0, R64              ; 1:1, OUT
0003:   EOF                             ; 0:0
```

## Output (partial)

```plain
0=1%
```

## Source (partial)

```basic
a = 1 / 0
```

## Disassembly (full)

```asm
0000:   LOADI       R65, 1              ; 1:5
0001:   LOADI       R64, 258            ; 1:5
0002:   UPCALL      0, R64              ; 1:1, OUT
0003:   LOADI       R64, 1              ; 1:5
0004:   LOADI       R65, 0              ; 1:9
0005:   DIVI        R64, R64, R65       ; 1:7
0006:   EOF                             ; 0:0
```

## Runtime errors (partial)

```plain
1:7: Division by zero
```

## Source (partial)

```basic
OUT 2
```

## Disassembly (full)

```asm
0000:   LOADI       R65, 1              ; 1:5
0001:   LOADI       R64, 258            ; 1:5
0002:   UPCALL      0, R64              ; 1:1, OUT
0003:   LOADI       R64, 1              ; 1:5
0004:   LOADI       R65, 0              ; 1:9
0005:   DIVI        R64, R64, R65       ; 1:7
0006:   LOADI       R66, 2              ; 1:5
0007:   LOADI       R65, 258            ; 1:5
0008:   UPCALL      0, R65              ; 1:1, OUT
0009:   EOF                             ; 0:0
```

## Output (partial)

```plain
0=2%
```

# Test: Labels

## Source (partial)

```basic
OUT "before"
a = 0
@first
a = a + 1
OUT a
IF a = 5 THEN END
```

## Disassembly (full)

```asm
0000:   LOADI       R65, 0              ; 1:5
0001:   LOADI       R64, 259            ; 1:5
0002:   UPCALL      0, R64              ; 1:1, OUT
0003:   LOADI       R64, 0              ; 2:5
0004:   MOVE        R65, R64            ; 4:5
0005:   LOADI       R66, 1              ; 4:9
0006:   ADDI        R65, R65, R66       ; 4:7
0007:   MOVE        R64, R65            ; 4:1
0008:   MOVE        R66, R64            ; 5:5
0009:   LOADI       R65, 258            ; 5:5
0010:   UPCALL      0, R65              ; 5:1, OUT
0011:   MOVE        R65, R64            ; 6:4
0012:   LOADI       R66, 5              ; 6:8
0013:   CMPEQI      R65, R65, R66       ; 6:6
0014:   JMPF        R65, 17             ; 6:4
0015:   LOADI       R65, 0              ; 6:15
0016:   END         R65                 ; 6:15
0017:   EOF                             ; 0:0
```

## Output (partial)

```plain
0=before$
0=1%
```

## Source (partial)

```basic
GOTO @first
OUT "done"
```

## Disassembly (full)

```asm
0000:   LOADI       R65, 0              ; 1:5
0001:   LOADI       R64, 259            ; 1:5
0002:   UPCALL      0, R64              ; 1:1, OUT
0003:   LOADI       R64, 0              ; 2:5
0004:   MOVE        R65, R64            ; 4:5
0005:   LOADI       R66, 1              ; 4:9
0006:   ADDI        R65, R65, R66       ; 4:7
0007:   MOVE        R64, R65            ; 4:1
0008:   MOVE        R66, R64            ; 5:5
0009:   LOADI       R65, 258            ; 5:5
0010:   UPCALL      0, R65              ; 5:1, OUT
0011:   MOVE        R65, R64            ; 6:4
0012:   LOADI       R66, 5              ; 6:8
0013:   CMPEQI      R65, R65, R66       ; 6:6
0014:   JMPF        R65, 17             ; 6:4
0015:   LOADI       R65, 0              ; 6:15
0016:   END         R65                 ; 6:15
0017:   JUMP        4                   ; 1:6
0018:   LOADI       R66, 1              ; 2:5
0019:   LOADI       R65, 259            ; 2:5
0020:   UPCALL      0, R65              ; 2:1, OUT
0021:   EOF                             ; 0:0
```

## Output (partial)

```plain
0=2%
0=3%
0=4%
0=5%
```
