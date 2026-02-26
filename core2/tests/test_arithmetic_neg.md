# Test: Immediate double

## Source

```basic
OUT -3.5
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADC       R65, 0              # 1:6
0002:   NEGD        R65                 # 1:5
0003:   LOADI       R64, 257            # 1:5
0004:   UPCALL      0, R64              # 1:1, OUT
0005:   LOADI       R64, 0              # 0:0
0006:   END         R64                 # 0:0
```

## Output

```plain
0=-3.5#
```

# Test: Immediate integer

## Source

```basic
OUT -7
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADI       R65, 7              # 1:6
0002:   NEGI        R65                 # 1:5
0003:   LOADI       R64, 258            # 1:5
0004:   UPCALL      0, R64              # 1:1, OUT
0005:   LOADI       R64, 0              # 0:0
0006:   END         R64                 # 0:0
```

## Output

```plain
0=-7%
```

# Test: Zero

## Source

```basic
OUT -0
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADI       R65, 0              # 1:6
0002:   NEGI        R65                 # 1:5
0003:   LOADI       R64, 258            # 1:5
0004:   UPCALL      0, R64              # 1:1, OUT
0005:   LOADI       R64, 0              # 0:0
0006:   END         R64                 # 0:0
```

## Output

```plain
0=0%
```

# Test: Non-numeric type

## Source

```basic
OUT -"hello"
```

## Compilation errors

```plain
1:5: STRING is not a number
```

# Test: Integer overflow

## Source

```basic
a = -(&x80000000)
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADC       R64, 0              # 1:7
0002:   NEGI        R64                 # 1:5
0003:   LOADI       R65, 0              # 0:0
0004:   END         R65                 # 0:0
```

## Runtime errors

```plain
1:5: Integer overflow
```
