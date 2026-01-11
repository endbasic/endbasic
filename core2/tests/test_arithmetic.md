# Test: Two immediate doubles

## Source

```basic
OUT 4.5 + 2.3
```

## Disassembly

```asm
0000:   ENTER       4                   # 0:0
0001:   LOADC       R66, 0              # 1:5
0002:   LOADC       R67, 1              # 1:11
0003:   ADDD        R65, R66, R67       # 1:9
0004:   LOADI       R64, 257            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   LOADI       R64, 0              # 0:0
0007:   END         R64                 # 0:0
```

## Output

```plain
0=6.8#
```

# Test: Two immediate integers

## Source

```basic
OUT 2 + 3
```

## Disassembly

```asm
0000:   ENTER       4                   # 0:0
0001:   LOADI       R66, 2              # 1:5
0002:   LOADI       R67, 3              # 1:9
0003:   ADDI        R65, R66, R67       # 1:7
0004:   LOADI       R64, 258            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   LOADI       R64, 0              # 0:0
0007:   END         R64                 # 0:0
```

## Output

```plain
0=5%
```

# Test: Concatenation of two immediate strings

## Source

```basic
OUT "a" + "b"
```

## Disassembly

```asm
0000:   ENTER       4                   # 0:0
0001:   LOADI       R66, 0              # 1:5
0002:   LOADI       R67, 1              # 1:11
0003:   CONCAT      R65, R66, R67       # 1:9
0004:   LOADI       R64, 259            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   LOADI       R64, 0              # 0:0
0007:   END         R64                 # 0:0
```

## Output

```plain
0=ab$
```

# Test: Left integer operand needs type promotion to double

## Source

```basic
OUT 2 + 8.3
```

## Disassembly

```asm
0000:   ENTER       4                   # 0:0
0001:   LOADI       R66, 2              # 1:5
0002:   LOADC       R67, 0              # 1:9
0003:   ITOD        R66                 # 1:5
0004:   ADDD        R65, R66, R67       # 1:7
0005:   LOADI       R64, 257            # 1:5
0006:   UPCALL      0, R64              # 1:1, OUT
0007:   LOADI       R64, 0              # 0:0
0008:   END         R64                 # 0:0
```

## Output

```plain
0=10.3#
```

# Test: Right integer operand needs type promotion to double

## Source

```basic
OUT 8.3 + 2
```

## Disassembly

```asm
0000:   ENTER       4                   # 0:0
0001:   LOADC       R66, 0              # 1:5
0002:   LOADI       R67, 2              # 1:11
0003:   ITOD        R67                 # 1:11
0004:   ADDD        R65, R66, R67       # 1:9
0005:   LOADI       R64, 257            # 1:5
0006:   UPCALL      0, R64              # 1:1, OUT
0007:   LOADI       R64, 0              # 0:0
0008:   END         R64                 # 0:0
```

## Output

```plain
0=10.3#
```

# Test: Integer overflow

## Source

```basic
a = 2147483640 + 20
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADC       R65, 0              # 1:5
0002:   LOADI       R66, 20             # 1:18
0003:   ADDI        R64, R65, R66       # 1:16
0004:   LOADI       R65, 0              # 0:0
0005:   END         R65                 # 0:0
```

## Runtime errors

```plain
1:16: Integer overflow
```
