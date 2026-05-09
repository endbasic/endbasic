# Test: Variable names are case insensitive

## Source

```basic
A = 1
OUT a
a = 2
OUT A
```

## Disassembly

```asm
0000:   LOADI       R64, 1              ; 1:5
0001:   MOVE        R66, R64            ; 2:5
0002:   LOADI       R65, 258            ; 2:5
0003:   UPCALL      0, R65              ; 2:1, OUT
0004:   LOADI       R64, 2              ; 3:5
0005:   MOVE        R66, R64            ; 4:5
0006:   LOADI       R65, 258            ; 4:5
0007:   UPCALL      0, R65              ; 4:1, OUT
0008:   EOF                             ; 0:0
```

## Output

```plain
0=1%
0=2%
```

# Test: Array names are case insensitive

## Source

```basic
DIM A(3)
a(0) = 10
A(1) = 20
OUT A(0), a(1)
```

## Disassembly

```asm
0000:   LOADI       R65, 3              ; 1:7
0001:   ALLOCA      R64, [1]%, R65      ; 1:5
0002:   LOADI       R65, 10             ; 2:8
0003:   LOADI       R66, 0              ; 2:3
0004:   STOREA      R64, R65, R66       ; 2:1
0005:   LOADI       R65, 20             ; 3:8
0006:   LOADI       R66, 1              ; 3:3
0007:   STOREA      R64, R65, R66       ; 3:1
0008:   LOADI       R67, 0              ; 4:7
0009:   LOADA       R66, R64, R67       ; 4:5
0010:   LOADI       R65, 290            ; 4:5
0011:   LOADI       R69, 1              ; 4:13
0012:   LOADA       R68, R64, R69       ; 4:11
0013:   LOADI       R67, 258            ; 4:11
0014:   UPCALL      0, R65              ; 4:1, OUT
0015:   EOF                             ; 0:0
```

## Output

```plain
0=10% , 1=20%
```

# Test: DIM conflicts with existing variable of different case

## Source

```basic
a = 5
DIM A
```

## Compilation errors

```plain
2:5: Cannot redefine A
```

# Test: DIM SHARED conflicts with existing global of different case

## Source

```basic
DIM SHARED a
DIM SHARED A
```

## Compilation errors

```plain
2:12: Cannot redefine A
```

# Test: Global variable name is case insensitive

## Source

```basic
DIM SHARED A
A = 1
a = 2
OUT A, a
```

## Disassembly

```asm
0000:   LOADI       R0, 0               ; 1:12
0001:   LOADI       R0, 1               ; 2:5
0002:   LOADI       R0, 2               ; 3:5
0003:   MOVE        R65, R0             ; 4:5
0004:   LOADI       R64, 290            ; 4:5
0005:   MOVE        R67, R0             ; 4:8
0006:   LOADI       R66, 258            ; 4:8
0007:   UPCALL      0, R64              ; 4:1, OUT
0008:   EOF                             ; 0:0
```

## Output

```plain
0=2% , 1=2%
```

# Test: Function name is case insensitive

## Source

```basic
FUNCTION Foo
    foo = 42
END FUNCTION

OUT FOO
```

## Disassembly

```asm
0000:   JUMP        4                   ; 1:10

;; FOO (BEGIN)
0001:   LOADI       R64, 0              ; 1:10
0002:   LOADI       R64, 42             ; 2:11
0003:   RETURN                          ; 3:1
;; FOO (END)

0004:   CALL        R65, 1              ; 5:5, FOO
0005:   LOADI       R64, 258            ; 5:5
0006:   UPCALL      0, R64              ; 5:1, OUT
0007:   EOF                             ; 0:0
```

## Output

```plain
0=42%
```

# Test: Sub name is case insensitive

## Source

```basic
SUB Foo
    OUT "hello"
END SUB

FOO
```

## Disassembly

```asm
0000:   JUMP        5                   ; 1:5

;; FOO (BEGIN)
0001:   LOADI       R65, 0              ; 2:9
0002:   LOADI       R64, 259            ; 2:9
0003:   UPCALL      0, R64              ; 2:5, OUT
0004:   RETURN                          ; 3:1
;; FOO (END)

0005:   CALL        R64, 1              ; 5:1, FOO
0006:   EOF                             ; 0:0
```

## Output

```plain
0=hello$
```

# Test: Label name is case insensitive

## Source

```basic
GOTO @FOO
OUT "skipped"
@foo:
OUT "done"
```

## Disassembly

```asm
0000:   JUMP        4                   ; 1:6
0001:   LOADI       R65, 0              ; 2:5
0002:   LOADI       R64, 259            ; 2:5
0003:   UPCALL      0, R64              ; 2:1, OUT
0004:   LOADI       R65, 1              ; 4:5
0005:   LOADI       R64, 259            ; 4:5
0006:   UPCALL      0, R64              ; 4:1, OUT
0007:   EOF                             ; 0:0
```

## Output

```plain
0=done$
```

# Test: GOSUB target is case insensitive

## Source

```basic
GOSUB @FOO
END
@foo:
OUT "in gosub"
RETURN
```

## Disassembly

```asm
0000:   GOSUB       3                   ; 1:7
0001:   LOADI       R64, 0              ; 2:1
0002:   END         R64                 ; 2:1
0003:   LOADI       R65, 0              ; 4:5
0004:   LOADI       R64, 259            ; 4:5
0005:   UPCALL      0, R64              ; 4:1, OUT
0006:   RETURN                          ; 5:1
0007:   EOF                             ; 0:0
```

## Output

```plain
0=in gosub$
```

# Test: Parameter names are case insensitive

## Source

```basic
FUNCTION foo(A)
    foo = a + 1
END FUNCTION

OUT foo(5)
```

## Disassembly

```asm
0000:   JUMP        6                   ; 1:10

;; FOO (BEGIN)
0001:   LOADI       R64, 0              ; 1:10
0002:   MOVE        R64, R65            ; 2:11
0003:   LOADI       R66, 1              ; 2:15
0004:   ADDI        R64, R64, R66       ; 2:13
0005:   RETURN                          ; 3:1
;; FOO (END)

0006:   LOADI       R67, 5              ; 5:9
0007:   CALL        R66, 1              ; 5:5, FOO
0008:   MOVE        R65, R66            ; 5:5
0009:   LOADI       R64, 258            ; 5:5
0010:   UPCALL      0, R64              ; 5:1, OUT
0011:   EOF                             ; 0:0
```

## Output

```plain
0=6%
```
