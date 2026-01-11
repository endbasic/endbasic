# Test: Repeated assignment

## Source

```basic
a = 1
a = 2

OUT a
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R64, 1              # 1:5
0002:   LOADI       R64, 2              # 2:5
0003:   MOVE        R66, R64            # 4:5
0004:   LOADI       R65, 258            # 4:5
0005:   UPCALL      0, R65              # 4:1, OUT
0006:   LOADI       R65, 0              # 0:0
0007:   END         R65                 # 0:0
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
0000:   ENTER       3                   # 0:0
0001:   LOADI       R64, 0              # 1:6
0002:   MOVE        R66, R64            # 2:5
0003:   LOADI       R65, 259            # 2:5
0004:   UPCALL      0, R65              # 2:1, OUT
0005:   LOADI       R64, 1              # 4:5
0006:   MOVE        R66, R64            # 5:5
0007:   LOADI       R65, 259            # 5:5
0008:   UPCALL      0, R65              # 5:1, OUT
0009:   LOADI       R65, 0              # 0:0
0010:   END         R65                 # 0:0
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
0000:   ENTER       3                   # 0:0
0001:   LOADI       R64, 0              # 1:5
0002:   MOVE        R66, R64            # 2:5
0003:   LOADI       R65, 259            # 2:5
0004:   UPCALL      0, R65              # 2:1, OUT
0005:   LOADI       R64, 1              # 4:6
0006:   MOVE        R66, R64            # 5:5
0007:   LOADI       R65, 259            # 5:5
0008:   UPCALL      0, R65              # 5:1, OUT
0009:   LOADI       R65, 0              # 0:0
0010:   END         R65                 # 0:0
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
0000:   ENTER       3                   # 0:0
0001:   LOADI       R64, 6              # 1:6
0002:   ITOD        R64                 # 1:6
0003:   MOVE        R66, R64            # 2:5
0004:   LOADI       R65, 257            # 2:5
0005:   UPCALL      0, R65              # 2:1, OUT
0006:   LOADI       R65, 0              # 0:0
0007:   END         R65                 # 0:0
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
0000:   ENTER       6                   # 0:0
0001:   LOADI       R64, 0              # 1:6
0002:   LOADC       R64, 0              # 2:6
0003:   DTOI        R64                 # 2:6
0004:   LOADI       R65, 0              # 4:6
0005:   LOADC       R65, 1              # 5:6
0006:   DTOI        R65                 # 5:6
0007:   MOVE        R67, R64            # 7:5
0008:   LOADI       R66, 290            # 7:5
0009:   MOVE        R69, R65            # 7:9
0010:   LOADI       R68, 258            # 7:9
0011:   UPCALL      0, R66              # 7:1, OUT
0012:   LOADI       R66, 0              # 0:0
0013:   END         R66                 # 0:0
```

## Output

```plain
0=3% , 1=4%
```
