# Test: Singular required argument, not provided

## Source

```basic
OUT_REQUIRED_VALUE
```

## Compilation errors

```plain
1:1: OUT_REQUIRED_VALUE expected arg%
```

# Test: Singular required argument, mismatched type

## Source

```basic
OUT_REQUIRED_VALUE "Foo"
```

## Compilation errors

```plain
1:20: STRING is not a number
```

# Test: Singular required argument, correct type

## Source

```basic
OUT_REQUIRED_VALUE 4
```

## Disassembly

```asm
0000:   ENTER       1                   # 0:0
0001:   LOADI       R64, 4              # 1:20
0002:   UPCALL      0, R64              # 1:1, OUT_REQUIRED_VALUE
0003:   LOADI       R64, 0              # 0:0
0004:   END         R64                 # 0:0
```

## Output

```plain
4
```

# Test: Singular required argument, type casting

## Source

```basic
OUT_REQUIRED_VALUE 7.8
```

## Disassembly

```asm
0000:   ENTER       1                   # 0:0
0001:   LOADC       R64, 0              # 1:20
0002:   DTOI        R64                 # 1:20
0003:   UPCALL      0, R64              # 1:1, OUT_REQUIRED_VALUE
0004:   LOADI       R64, 0              # 0:0
0005:   END         R64                 # 0:0
```

## Output

```plain
8
```

# Test: Singular optional argument, not provided

## Source

```basic
OUT_OPTIONAL
```

## Disassembly

```asm
0000:   ENTER       1                   # 0:0
0001:   LOADI       R64, 0              # 1:1
0002:   UPCALL      0, R64              # 1:1, OUT_OPTIONAL
0003:   LOADI       R64, 0              # 0:0
0004:   END         R64                 # 0:0
```

## Output

```plain
()
```

# Test: Singular optional argument, provided

## Source

```basic
OUT_OPTIONAL "Foo"
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADI       R65, 0              # 1:14
0002:   LOADI       R64, 259            # 1:14
0003:   UPCALL      0, R64              # 1:1, OUT_OPTIONAL
0004:   LOADI       R64, 0              # 0:0
0005:   END         R64                 # 0:0
```

## Output

```plain
Foo$
```

# Test: Singular optional argument, too many provided

## Source

```basic
OUT_OPTIONAL "Foo", "Bar"
```

## Compilation errors

```plain
1:1: OUT_OPTIONAL expected [arg$]
```

# Test: Singular argument of any type, not optional

## Source

```basic
OUT_ANY_VALUE TRUE
OUT_ANY_VALUE "Text"
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADI       R65, 1              # 1:15
0002:   LOADI       R64, 256            # 1:15
0003:   UPCALL      0, R64              # 1:1, OUT_ANY_VALUE
0004:   LOADI       R65, 0              # 2:15
0005:   LOADI       R64, 259            # 2:15
0006:   UPCALL      0, R64              # 2:1, OUT_ANY_VALUE
0007:   LOADI       R64, 0              # 0:0
0008:   END         R64                 # 0:0
```

## Output

```plain
true?
Text$
```

# Test: Singular argument of any type, too many provided

## Source

```basic
OUT_ANY_VALUE TRUE, FALSE
```

## Compilation errors

```plain
1:1: OUT_ANY_VALUE expected arg
```

# Test: Singular argument of any type, optional

## Source

```basic
OUT_ANY_VALUE_OPTIONAL
OUT_ANY_VALUE_OPTIONAL TRUE
OUT_ANY_VALUE_OPTIONAL "Text"
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADI       R64, 0              # 1:1
0002:   UPCALL      0, R64              # 1:1, OUT_ANY_VALUE_OPTIONAL
0003:   LOADI       R65, 1              # 2:24
0004:   LOADI       R64, 256            # 2:24
0005:   UPCALL      0, R64              # 2:1, OUT_ANY_VALUE_OPTIONAL
0006:   LOADI       R65, 0              # 3:24
0007:   LOADI       R64, 259            # 3:24
0008:   UPCALL      0, R64              # 3:1, OUT_ANY_VALUE_OPTIONAL
0009:   LOADI       R64, 0              # 0:0
0010:   END         R64                 # 0:0
```

## Output

```plain
()
true?
Text$
```

# Test: Singular argument of any type, too many provided

## Source

```basic
OUT_ANY_VALUE_OPTIONAL "Text", 3
```

## Compilation errors

```plain
1:1: OUT_ANY_VALUE_OPTIONAL expected [arg]
```

# Test: Singular arguments of various kinds, with type casting

## Source

```basic
OUT_POSITIONAL 3, 5.6 AS "Foo"
OUT_POSITIONAL "A"; 4 AS "Foo"
OUT_POSITIONAL ; 0 AS 8.2
```

## Disassembly

```asm
0000:   ENTER       5                   # 0:0
0001:   LOADI       R65, 3              # 1:16
0002:   LOADI       R64, 290            # 1:16
0003:   LOADC       R66, 0              # 1:19
0004:   DTOI        R66                 # 1:19
0005:   LOADI       R68, 1              # 1:26
0006:   LOADI       R67, 259            # 1:26
0007:   UPCALL      0, R64              # 1:1, OUT_POSITIONAL
0008:   LOADI       R65, 2              # 2:16
0009:   LOADI       R64, 275            # 2:16
0010:   LOADI       R66, 4              # 2:21
0011:   LOADI       R68, 1              # 2:26
0012:   LOADI       R67, 259            # 2:26
0013:   UPCALL      0, R64              # 2:1, OUT_POSITIONAL
0014:   LOADI       R64, 16             # 3:16
0015:   LOADI       R65, 0              # 3:18
0016:   LOADC       R67, 3              # 3:23
0017:   LOADI       R66, 257            # 3:23
0018:   UPCALL      0, R64              # 3:1, OUT_POSITIONAL
0019:   LOADI       R64, 0              # 0:0
0020:   END         R64                 # 0:0
```

## Output

```plain
3%
6
Foo$
A$
4
Foo$
()
0
8.2#
```

# Test: Singular arguments of various kinds, mismatched separators

## Source

```basic
OUT_POSITIONAL 3 AS 5.6 AS "Foo"
```

## Compilation errors

```plain
1:16: OUT_POSITIONAL expected [arg1] <,|;> arg2% AS arg3
```

# Test: Repeated arguments, none provided

## Source

```basic
OUT
```

## Disassembly

```asm
0000:   ENTER       1                   # 0:0
0001:   UPCALL      0, R64              # 1:1, OUT
0002:   LOADI       R64, 0              # 0:0
0003:   END         R64                 # 0:0
```

## Output

```plain
0=()
```

# Test: Repeated arguments, several present

## Source

```basic
OUT 100, 200, 300
```

## Disassembly

```asm
0000:   ENTER       6                   # 0:0
0001:   LOADI       R65, 100            # 1:5
0002:   LOADI       R64, 290            # 1:5
0003:   LOADI       R67, 200            # 1:10
0004:   LOADI       R66, 290            # 1:10
0005:   LOADI       R69, 300            # 1:15
0006:   LOADI       R68, 258            # 1:15
0007:   UPCALL      0, R64              # 1:1, OUT
0008:   LOADI       R64, 0              # 0:0
0009:   END         R64                 # 0:0
```

## Output

```plain
0=100% , 1=200% , 2=300%
```

# Test: Repeated arguments, some missing

## Source

```basic
OUT 100, , 300,
```

## Disassembly

```asm
0000:   ENTER       6                   # 0:0
0001:   LOADI       R65, 100            # 1:5
0002:   LOADI       R64, 290            # 1:5
0003:   LOADI       R66, 32             # 1:10
0004:   LOADI       R68, 300            # 1:12
0005:   LOADI       R67, 290            # 1:12
0006:   LOADI       R69, 0              # 1:16
0007:   UPCALL      0, R64              # 1:1, OUT
0008:   LOADI       R64, 0              # 0:0
0009:   END         R64                 # 0:0
```

## Output

```plain
0=100% , 1=() , 2=300% , 3=()
```

# Test: Repeated arguments, different separators

## Source

```basic
OUT 100; 200 AS 300; 400
```

## Disassembly

```asm
0000:   ENTER       8                   # 0:0
0001:   LOADI       R65, 100            # 1:5
0002:   LOADI       R64, 274            # 1:5
0003:   LOADI       R67, 200            # 1:10
0004:   LOADI       R66, 306            # 1:10
0005:   LOADI       R69, 300            # 1:17
0006:   LOADI       R68, 274            # 1:17
0007:   LOADI       R71, 400            # 1:22
0008:   LOADI       R70, 258            # 1:22
0009:   UPCALL      0, R64              # 1:1, OUT
0010:   LOADI       R64, 0              # 0:0
0011:   END         R64                 # 0:0
```

## Output

```plain
0=100% ; 1=200% AS 2=300% ; 3=400%
```

# Test: Repeated arguments, different types

## Source

```basic
OUT 100, "Foo"
```

## Disassembly

```asm
0000:   ENTER       4                   # 0:0
0001:   LOADI       R65, 100            # 1:5
0002:   LOADI       R64, 290            # 1:5
0003:   LOADI       R67, 0              # 1:10
0004:   LOADI       R66, 259            # 1:10
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   LOADI       R64, 0              # 0:0
0007:   END         R64                 # 0:0
```

## Output

```plain
0=100% , 1=Foo$
```
