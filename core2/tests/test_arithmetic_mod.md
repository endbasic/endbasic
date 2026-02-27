# Test: Two immediate doubles

## Source

```basic
OUT 10.0 MOD 3.0
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADC       R65, 0              # 1:5
0002:   LOADC       R66, 1              # 1:14
0003:   MODD        R65, R65, R66       # 1:10
0004:   LOADI       R64, 257            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   LOADI       R64, 0              # 0:0
0007:   END         R64                 # 0:0
```

## Output

```plain
0=1#
```

# Test: Two immediate integers

## Source

```basic
OUT 10 MOD 3
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R65, 10             # 1:5
0002:   LOADI       R66, 3              # 1:12
0003:   MODI        R65, R65, R66       # 1:8
0004:   LOADI       R64, 258            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   LOADI       R64, 0              # 0:0
0007:   END         R64                 # 0:0
```

## Output

```plain
0=1%
```

# Test: Left integer operand needs type promotion to double

## Source

```basic
OUT 3 MOD 2.5
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R65, 3              # 1:5
0002:   LOADC       R66, 0              # 1:11
0003:   ITOD        R65                 # 1:7
0004:   MODD        R65, R65, R66       # 1:7
0005:   LOADI       R64, 257            # 1:5
0006:   UPCALL      0, R64              # 1:1, OUT
0007:   LOADI       R64, 0              # 0:0
0008:   END         R64                 # 0:0
```

## Output

```plain
0=0.5#
```

# Test: Right integer operand needs type promotion to double

## Source

```basic
OUT 10.5 MOD 3
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADC       R65, 0              # 1:5
0002:   LOADI       R66, 3              # 1:14
0003:   ITOD        R66                 # 1:14
0004:   MODD        R65, R65, R66       # 1:10
0005:   LOADI       R64, 257            # 1:5
0006:   UPCALL      0, R64              # 1:1, OUT
0007:   LOADI       R64, 0              # 0:0
0008:   END         R64                 # 0:0
```

## Output

```plain
0=1.5#
```

# Test: Integer overflow

## Source

```basic
a = (-2147483647 - 1) MOD -1
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADC       R64, 0              # 1:7
0002:   NEGI        R64                 # 1:6
0003:   LOADI       R65, 1              # 1:20
0004:   SUBI        R64, R64, R65       # 1:18
0005:   LOADI       R65, 1              # 1:28
0006:   NEGI        R65                 # 1:27
0007:   MODI        R64, R64, R65       # 1:23
0008:   LOADI       R65, 0              # 0:0
0009:   END         R65                 # 0:0
```

## Runtime errors

```plain
1:23: Integer underflow
```

# Test: Modulo by zero

## Source

```basic
a = 5 MOD 0
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADI       R64, 5              # 1:5
0002:   LOADI       R65, 0              # 1:11
0003:   MODI        R64, R64, R65       # 1:7
0004:   LOADI       R65, 0              # 0:0
0005:   END         R65                 # 0:0
```

## Runtime errors

```plain
1:7: Modulo by zero
```
