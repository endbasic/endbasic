# Test: Two immediate doubles

## Source

```basic
OUT 5.0 - 3.0
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADC       R65, 0              # 1:5
0002:   LOADC       R66, 1              # 1:11
0003:   SUBD        R65, R65, R66       # 1:9
0004:   LOADI       R64, 257            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   LOADI       R64, 0              # 0:0
0007:   END         R64                 # 0:0
```

## Output

```plain
0=2#
```

# Test: Two immediate integers

## Source

```basic
OUT 10 - 3
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R65, 10             # 1:5
0002:   LOADI       R66, 3              # 1:10
0003:   SUBI        R65, R65, R66       # 1:8
0004:   LOADI       R64, 258            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   LOADI       R64, 0              # 0:0
0007:   END         R64                 # 0:0
```

## Output

```plain
0=7%
```

# Test: Left integer operand needs type promotion to double

## Source

```basic
OUT 2 - 8.3
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R65, 2              # 1:5
0002:   LOADC       R66, 0              # 1:9
0003:   ITOD        R65                 # 1:7
0004:   SUBD        R65, R65, R66       # 1:7
0005:   LOADI       R64, 257            # 1:5
0006:   UPCALL      0, R64              # 1:1, OUT
0007:   LOADI       R64, 0              # 0:0
0008:   END         R64                 # 0:0
```

## Output

```plain
0=-6.300000000000001#
```

# Test: Right integer operand needs type promotion to double

## Source

```basic
OUT 8.3 - 2
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADC       R65, 0              # 1:5
0002:   LOADI       R66, 2              # 1:11
0003:   ITOD        R66                 # 1:11
0004:   SUBD        R65, R65, R66       # 1:9
0005:   LOADI       R64, 257            # 1:5
0006:   UPCALL      0, R64              # 1:1, OUT
0007:   LOADI       R64, 0              # 0:0
0008:   END         R64                 # 0:0
```

## Output

```plain
0=6.300000000000001#
```

# Test: Integer overflow

## Source

```basic
a = -2147483640 - 20
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADC       R64, 0              # 1:6
0002:   NEGI        R64                 # 1:5
0003:   LOADI       R65, 20             # 1:19
0004:   SUBI        R64, R64, R65       # 1:17
0005:   LOADI       R65, 0              # 0:0
0006:   END         R65                 # 0:0
```

## Runtime errors

```plain
1:17: Integer underflow
```
