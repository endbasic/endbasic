# Test: Repeated assignment

## Source

```basic
a = 1
a = 2

OUT a
```

## Disassembly

```asm
0000:   LOADI       R64, 1              ; 1:5
0001:   LOADI       R64, 2              ; 2:5
0002:   MOVE        R66, R64            ; 4:5
0003:   LOADI       R65, 258            ; 4:5
0004:   UPCALL      0, R65              ; 4:1, OUT
0005:   EOF                             ; 0:0
```

## Output

```plain
0=2%
```

# Test: First assignment has annotation, second infers it

## Source

```basic
a$ = "foo"
OUT a

a = "bar"
OUT a
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:6
0001:   MOVE        R66, R64            ; 2:5
0002:   LOADI       R65, 259            ; 2:5
0003:   UPCALL      0, R65              ; 2:1, OUT
0004:   LOADI       R64, 1              ; 4:5
0005:   MOVE        R66, R64            ; 5:5
0006:   LOADI       R65, 259            ; 5:5
0007:   UPCALL      0, R65              ; 5:1, OUT
0008:   EOF                             ; 0:0
```

## Output

```plain
0=foo$
0=bar$
```

# Test: First assignment infers type, second has annotation

## Source

```basic
a = "foo"
OUT a

a$ = "bar"
OUT a
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:5
0001:   MOVE        R66, R64            ; 2:5
0002:   LOADI       R65, 259            ; 2:5
0003:   UPCALL      0, R65              ; 2:1, OUT
0004:   LOADI       R64, 1              ; 4:6
0005:   MOVE        R66, R64            ; 5:5
0006:   LOADI       R65, 259            ; 5:5
0007:   UPCALL      0, R65              ; 5:1, OUT
0008:   EOF                             ; 0:0
```

## Output

```plain
0=foo$
0=bar$
```

# Test: Annotation mismatch after assignment

## Source

```basic
a# = 4.5
a$ = "foo"
```

## Compilation errors

```plain
2:1: Incompatible type annotation in a$ reference
```

# Test: Assignment can prepend from itself via binary operator

## Source

```basic
s = "hello"
s = "." + s
OUT s
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:5
0001:   LOADI       R65, 1              ; 2:5
0002:   MOVE        R66, R64            ; 2:11
0003:   CONCAT      R65, R65, R66       ; 2:9
0004:   MOVE        R64, R65            ; 2:1
0005:   MOVE        R66, R64            ; 3:5
0006:   LOADI       R65, 259            ; 3:5
0007:   UPCALL      0, R65              ; 3:1, OUT
0008:   EOF                             ; 0:0
```

## Output

```plain
0=.hello$
```

# Test: Assignment can modify itself via unary operator

## Source

```basic
i = 5
i = -i
OUT i
```

## Disassembly

```asm
0000:   LOADI       R64, 5              ; 1:5
0001:   MOVE        R65, R64            ; 2:6
0002:   NEGI        R65                 ; 2:5
0003:   MOVE        R64, R65            ; 2:1
0004:   MOVE        R66, R64            ; 3:5
0005:   LOADI       R65, 258            ; 3:5
0006:   UPCALL      0, R65              ; 3:1, OUT
0007:   EOF                             ; 0:0
```

## Output

```plain
0=-5%
```

# Test: Array assignment can modify itself

## Source

```basic
DIM s(3) AS STRING
s(1) = "foo"
s(1) = "." + s(1)
OUT s(1)
```

## Disassembly

```asm
0000:   LOADI       R65, 3              ; 1:7
0001:   ALLOCA      R64, [1]$, R65      ; 1:5
0002:   LOADI       R65, 0              ; 2:8
0003:   LOADI       R66, 1              ; 2:3
0004:   STOREA      R64, R65, R66       ; 2:1
0005:   LOADI       R65, 1              ; 3:8
0006:   LOADI       R67, 1              ; 3:16
0007:   LOADA       R66, R64, R67       ; 3:14
0008:   CONCAT      R65, R65, R66       ; 3:12
0009:   LOADI       R66, 1              ; 3:3
0010:   STOREA      R64, R65, R66       ; 3:1
0011:   LOADI       R67, 1              ; 4:7
0012:   LOADA       R66, R64, R67       ; 4:5
0013:   LOADI       R65, 259            ; 4:5
0014:   UPCALL      0, R65              ; 4:1, OUT
0015:   EOF                             ; 0:0
```

## Output

```plain
0=.foo$
```

# Test: Value type does not match annotation on first assignment

## Source

```basic
d$ = 3.4
```

## Compilation errors

```plain
1:6: Cannot assign value of type DOUBLE to variable of type STRING
```

# Test: Value type does not match target type after first definition

## Source

```basic
a = 4.5
a = "foo"
```

## Compilation errors

```plain
2:5: STRING is not a number
```

# Test: Integer to double promotion

## Source

```basic
d# = 6
OUT d
```

## Disassembly

```asm
0000:   LOADI       R64, 6              ; 1:6
0001:   ITOD        R64                 ; 1:6
0002:   MOVE        R66, R64            ; 2:5
0003:   LOADI       R65, 257            ; 2:5
0004:   UPCALL      0, R65              ; 2:1, OUT
0005:   EOF                             ; 0:0
```

## Output

```plain
0=6#
```

# Test: Double to integer demotion

## Source

```basic
i1 = 0
i1 = 3.2

i2 = 0
i2 = 3.7

OUT i1, i2
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:6
0001:   LOADC       R64, 0              ; 2:6
0002:   DTOI        R64                 ; 2:6
0003:   LOADI       R65, 0              ; 4:6
0004:   LOADC       R65, 1              ; 5:6
0005:   DTOI        R65                 ; 5:6
0006:   MOVE        R67, R64            ; 7:5
0007:   LOADI       R66, 290            ; 7:5
0008:   MOVE        R69, R65            ; 7:9
0009:   LOADI       R68, 258            ; 7:9
0010:   UPCALL      0, R66              ; 7:1, OUT
0011:   EOF                             ; 0:0
```

## Output

```plain
0=3% , 1=4%
```

# Test: Assignment to name of a built-in callable

## Source

```basic
out = 5
```

## Compilation errors

```plain
1:1: Cannot redefine out
```

# Test: Assignment to name of a user-defined sub

## Source

```basic
SUB foo
END SUB
foo = 5
```

## Compilation errors

```plain
3:1: Cannot redefine foo
```

# Test: Assignment to name of a user-defined function

## Source

```basic
FUNCTION bar%
END FUNCTION
bar = 5
```

## Compilation errors

```plain
3:1: Cannot redefine bar
```
