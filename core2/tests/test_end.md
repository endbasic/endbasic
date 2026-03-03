# Test: Call to END and nothing else

## Source

```basic
END
```

## Disassembly

```asm
0000:   ENTER       1                   # 0:0
0001:   LOADI       R64, 0              # 1:1
0002:   END         R64                 # 1:1
0003:   LOADI       R64, 0              # 0:0
0004:   END         R64                 # 0:0
```

# Test: Exit code is an integer immediate

## Source

```basic
END 42
```

## Disassembly

```asm
0000:   ENTER       1                   # 0:0
0001:   LOADI       R64, 42             # 1:5
0002:   END         R64                 # 1:1
0003:   LOADI       R64, 0              # 0:0
0004:   END         R64                 # 0:0
```

## Exit code

```plain
42
```

# Test: Exit code is a double immediate and needs demotion

## Source

```basic
END 43.98
```

## Disassembly

```asm
0000:   ENTER       1                   # 0:0
0001:   LOADC       R64, 0              # 1:5
0002:   DTOI        R64                 # 1:5
0003:   END         R64                 # 1:1
0004:   LOADI       R64, 0              # 0:0
0005:   END         R64                 # 0:0
```

## Exit code

```plain
44
```

# Test: Exit code is in a global variable

## Source

```basic
DIM SHARED i
i = 5
END i
```

## Disassembly

```asm
0000:   ENTER       1                   # 0:0
0001:   LOADI       R0, 0               # 1:12
0002:   LOADI       R0, 5               # 2:5
0003:   MOVE        R64, R0             # 3:5
0004:   END         R64                 # 3:1
0005:   LOADI       R64, 0              # 0:0
0006:   END         R64                 # 0:0
```

## Exit code

```plain
5
```

# Test: Exit code is in a local variable

## Source

```basic
i = 3
END i
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADI       R64, 3              # 1:5
0002:   MOVE        R65, R64            # 2:5
0003:   END         R65                 # 2:1
0004:   LOADI       R65, 0              # 0:0
0005:   END         R65                 # 0:0
```

## Exit code

```plain
3
```

# Test: Exit code is of an invalid type

## Source

```basic
END "foo"
```

## Compilation errors

```plain
1:5: STRING is not a number
```

# Test: Exit code cannot be negative

## Source

```basic
END -3
```

## Disassembly

```asm
0000:   ENTER       1                   # 0:0
0001:   LOADI       R64, 3              # 1:6
0002:   NEGI        R64                 # 1:5
0003:   END         R64                 # 1:1
0004:   LOADI       R64, 0              # 0:0
0005:   END         R64                 # 0:0
```

## Exit code

```plain
-3
```

# Test: Exit code cannot be larger than 127

## Source

```basic
END 128
```

## Disassembly

```asm
0000:   ENTER       1                   # 0:0
0001:   LOADI       R64, 128            # 1:5
0002:   END         R64                 # 1:1
0003:   LOADI       R64, 0              # 0:0
0004:   END         R64                 # 0:0
```

## Exit code

```plain
128
```

# Test: END exits from inside FOR loop

## Source

```basic
FOR i = 1 TO 10
    IF i = 3 THEN END 42
NEXT
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R64, 1              # 1:9
0002:   MOVE        R65, R64            # 1:5
0003:   LOADI       R66, 10             # 1:14
0004:   CMPLEI      R65, R65, R66       # 1:11
0005:   JMPF        R65, 16             # 1:5
0006:   MOVE        R65, R64            # 2:8
0007:   LOADI       R66, 3              # 2:12
0008:   CMPEQI      R65, R65, R66       # 2:10
0009:   JMPF        R65, 12             # 2:8
0010:   LOADI       R65, 42             # 2:23
0011:   END         R65                 # 2:19
0012:   MOVE        R64, R64            # 1:5
0013:   LOADI       R65, 1              # 1:16
0014:   ADDI        R64, R64, R65       # 1:11
0015:   JUMP        2                   # 1:5
0016:   LOADI       R65, 0              # 0:0
0017:   END         R65                 # 0:0
```

## Exit code

```plain
42
```
