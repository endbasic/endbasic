# Test: Boolean values

## Source

```basic
bool_1 = FALSE
bool_2 = TRUE
OUT bool_1, bool_2
```

## Disassembly

```asm
0000:   ENTER       6                   # 0:0
0001:   LOADI       R64, 0              # 1:10
0002:   LOADI       R65, 1              # 2:10
0003:   MOVE        R67, R64            # 3:5
0004:   LOADI       R66, 288            # 3:5
0005:   MOVE        R69, R65            # 3:13
0006:   LOADI       R68, 256            # 3:13
0007:   UPCALL      0, R66              # 3:1, OUT
0008:   LOADI       R66, 0              # 0:0
0009:   END         R66                 # 0:0
```

## Output

```plain
0=false? , 1=true?
```

# Test: Double values are always constants

## Source

```basic
zero_double = 0.0
small_double = 1.2
large_double = 10000000000000000.818239895
tiny_double = 0.001729874916
OUT zero_double, small_double, large_double, tiny_double
```

## Disassembly

```asm
0000:   ENTER       12                  # 0:0
0001:   LOADC       R64, 0              # 1:15
0002:   LOADC       R65, 1              # 2:16
0003:   LOADC       R66, 2              # 3:16
0004:   LOADC       R67, 3              # 4:15
0005:   MOVE        R69, R64            # 5:5
0006:   LOADI       R68, 289            # 5:5
0007:   MOVE        R71, R65            # 5:18
0008:   LOADI       R70, 289            # 5:18
0009:   MOVE        R73, R66            # 5:32
0010:   LOADI       R72, 289            # 5:32
0011:   MOVE        R75, R67            # 5:46
0012:   LOADI       R74, 257            # 5:46
0013:   UPCALL      0, R68              # 5:1, OUT
0014:   LOADI       R68, 0              # 0:0
0015:   END         R68                 # 0:0
```

## Output

```plain
0=0# , 1=1.2# , 2=10000000000000000# , 3=0.001729874916#
```

# Test: Integer values that fit in an instruction

## Source

```basic
small_int = 123
OUT small_int
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R64, 123            # 1:13
0002:   MOVE        R66, R64            # 2:5
0003:   LOADI       R65, 258            # 2:5
0004:   UPCALL      0, R65              # 2:1, OUT
0005:   LOADI       R65, 0              # 0:0
0006:   END         R65                 # 0:0
```

## Output

```plain
0=123%
```

# Test: Integer values that spill into a constant

## Source

```basic
large_int = 2147483640
OUT large_int
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADC       R64, 0              # 1:13
0002:   MOVE        R66, R64            # 2:5
0003:   LOADI       R65, 258            # 2:5
0004:   UPCALL      0, R65              # 2:1, OUT
0005:   LOADI       R65, 0              # 0:0
0006:   END         R65                 # 0:0
```

## Output

```plain
0=2147483640%
```

# Test: String values

## Source

```basic
text = "Hello, world!"
OUT text
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R64, 0              # 1:8
0002:   MOVE        R66, R64            # 2:5
0003:   LOADI       R65, 259            # 2:5
0004:   UPCALL      0, R65              # 2:1, OUT
0005:   LOADI       R65, 0              # 0:0
0006:   END         R65                 # 0:0
```

## Output

```plain
0=Hello, world!$
```

# Test: Invalid annotation for variable reference

## Source

```basic
d = 3.4
d2 = d$
```

## Compilation errors

```plain
2:6: Incompatible type annotation in d$ reference
```
