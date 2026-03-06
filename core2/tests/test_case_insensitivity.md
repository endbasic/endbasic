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
0000:   ENTER       3                   # 0:0
0001:   LOADI       R64, 1              # 1:5
0002:   MOVE        R66, R64            # 2:5
0003:   LOADI       R65, 258            # 2:5
0004:   UPCALL      0, R65              # 2:1, OUT
0005:   LOADI       R64, 2              # 3:5
0006:   MOVE        R66, R64            # 4:5
0007:   LOADI       R65, 258            # 4:5
0008:   UPCALL      0, R65              # 4:1, OUT
0009:   LOADI       R65, 0              # 0:0
0010:   END         R65                 # 0:0
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
0000:   ENTER       6                   # 0:0
0001:   LOADI       R65, 3              # 1:7
0002:   ALLOCA      R64, [1]%, R65      # 1:5
0003:   LOADI       R65, 10             # 2:8
0004:   LOADI       R66, 0              # 2:3
0005:   STOREA      R64, R65, R66       # 2:1
0006:   LOADI       R65, 20             # 3:8
0007:   LOADI       R66, 1              # 3:3
0008:   STOREA      R64, R65, R66       # 3:1
0009:   LOADI       R67, 0              # 4:7
0010:   LOADA       R66, R64, R67       # 4:5
0011:   LOADI       R65, 290            # 4:5
0012:   LOADI       R69, 1              # 4:13
0013:   LOADA       R68, R64, R69       # 4:11
0014:   LOADI       R67, 258            # 4:11
0015:   UPCALL      0, R65              # 4:1, OUT
0016:   LOADI       R65, 0              # 0:0
0017:   END         R65                 # 0:0
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
0000:   ENTER       4                   # 0:0
0001:   LOADI       R0, 0               # 1:12
0002:   LOADI       R0, 1               # 2:5
0003:   LOADI       R0, 2               # 3:5
0004:   MOVE        R65, R0             # 4:5
0005:   LOADI       R64, 290            # 4:5
0006:   MOVE        R67, R0             # 4:8
0007:   LOADI       R66, 258            # 4:8
0008:   UPCALL      0, R64              # 4:1, OUT
0009:   LOADI       R64, 0              # 0:0
0010:   END         R64                 # 0:0
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
0000:   ENTER       2                   # 0:0
0001:   CALL        R65, 6              # 5:5, FOO
0002:   LOADI       R64, 258            # 5:5
0003:   UPCALL      0, R64              # 5:1, OUT
0004:   LOADI       R64, 0              # 0:0
0005:   END         R64                 # 0:0

-- FOO 
0006:   LOADI       R64, 0              # 1:10
0007:   ENTER       1                   # 0:0
0008:   LOADI       R64, 42             # 2:11
0009:   RETURN                          # 3:1
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
0000:   ENTER       1                   # 0:0
0001:   CALL        R64, 4              # 5:1, FOO
0002:   LOADI       R64, 0              # 0:0
0003:   END         R64                 # 0:0

-- FOO 
0004:   ENTER       2                   # 0:0
0005:   LOADI       R65, 0              # 2:9
0006:   LOADI       R64, 259            # 2:9
0007:   UPCALL      0, R64              # 2:5, OUT
0008:   RETURN                          # 3:1
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
0000:   ENTER       2                   # 0:0
0001:   JUMP        5                   # 1:6
0002:   LOADI       R65, 0              # 2:5
0003:   LOADI       R64, 259            # 2:5
0004:   UPCALL      0, R64              # 2:1, OUT
0005:   LOADI       R65, 1              # 4:5
0006:   LOADI       R64, 259            # 4:5
0007:   UPCALL      0, R64              # 4:1, OUT
0008:   LOADI       R64, 0              # 0:0
0009:   END         R64                 # 0:0
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
0000:   ENTER       2                   # 0:0
0001:   GOSUB       4                   # 1:7
0002:   LOADI       R64, 0              # 2:1
0003:   END         R64                 # 2:1
0004:   LOADI       R65, 0              # 4:5
0005:   LOADI       R64, 259            # 4:5
0006:   UPCALL      0, R64              # 4:1, OUT
0007:   RETURN                          # 5:1
0008:   LOADI       R64, 0              # 0:0
0009:   END         R64                 # 0:0
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
0000:   ENTER       4                   # 0:0
0001:   LOADI       R67, 5              # 5:9
0002:   CALL        R66, 8              # 5:5, FOO
0003:   MOVE        R65, R66            # 5:5
0004:   LOADI       R64, 258            # 5:5
0005:   UPCALL      0, R64              # 5:1, OUT
0006:   LOADI       R64, 0              # 0:0
0007:   END         R64                 # 0:0

-- FOO 
0008:   LOADI       R64, 0              # 1:10
0009:   ENTER       3                   # 0:0
0010:   MOVE        R64, R65            # 2:11
0011:   LOADI       R66, 1              # 2:15
0012:   ADDI        R64, R64, R66       # 2:13
0013:   RETURN                          # 3:1
```

## Output

```plain
0=6%
```
