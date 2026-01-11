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
