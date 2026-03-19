# Test: Two immediate doubles

## Source

```basic
OUT 4.0 * 2.5
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADC       R65, 0              # 1:5
0002:   LOADC       R66, 1              # 1:11
0003:   MULD        R65, R65, R66       # 1:9
0004:   LOADI       R64, 257            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   EOF                             # 0:0
```

## Output

```plain
0=10#
```

# Test: Two immediate integers

## Source

```basic
OUT 6 * 7
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R65, 6              # 1:5
0002:   LOADI       R66, 7              # 1:9
0003:   MULI        R65, R65, R66       # 1:7
0004:   LOADI       R64, 258            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   EOF                             # 0:0
```

## Output

```plain
0=42%
```

# Test: Left integer operand needs type promotion to double

## Source

```basic
OUT 3 * 2.5
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R65, 3              # 1:5
0002:   LOADC       R66, 0              # 1:9
0003:   ITOD        R65                 # 1:7
0004:   MULD        R65, R65, R66       # 1:7
0005:   LOADI       R64, 257            # 1:5
0006:   UPCALL      0, R64              # 1:1, OUT
0007:   EOF                             # 0:0
```

## Output

```plain
0=7.5#
```

# Test: Right integer operand needs type promotion to double

## Source

```basic
OUT 2.5 * 3
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADC       R65, 0              # 1:5
0002:   LOADI       R66, 3              # 1:11
0003:   ITOD        R66                 # 1:11
0004:   MULD        R65, R65, R66       # 1:9
0005:   LOADI       R64, 257            # 1:5
0006:   UPCALL      0, R64              # 1:1, OUT
0007:   EOF                             # 0:0
```

## Output

```plain
0=7.5#
```

# Test: Integer overflow

## Source

```basic
a = 2147483640 * 10
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADC       R64, 0              # 1:5
0002:   LOADI       R65, 10             # 1:18
0003:   MULI        R64, R64, R65       # 1:16
0004:   EOF                             # 0:0
```

## Runtime errors

```plain
1:16: Integer overflow
```
