# Test: Two immediate integers

## Source

```basic
OUT 12 XOR 10
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R65, 12             # 1:5
0002:   LOADI       R66, 10             # 1:12
0003:   XOR         R65, R65, R66       # 1:8
0004:   LOADI       R64, 258            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   EOF                             # 0:0
```

## Output

```plain
0=6%
```

# Test: Type error with double

## Source

```basic
OUT 1.0 XOR 2.0
```

## Compilation errors

```plain
1:9: Cannot XOR DOUBLE and DOUBLE
```

# Test: Type error with string

## Source

```basic
OUT "a" XOR "b"
```

## Compilation errors

```plain
1:9: Cannot XOR STRING and STRING
```

# Test: Two immediate booleans

## Source

```basic
OUT TRUE XOR FALSE
OUT TRUE XOR TRUE
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R65, 1              # 1:5
0002:   LOADI       R66, 0              # 1:14
0003:   XOR         R65, R65, R66       # 1:10
0004:   LOADI       R64, 256            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   LOADI       R65, 1              # 2:5
0007:   LOADI       R66, 1              # 2:14
0008:   XOR         R65, R65, R66       # 2:10
0009:   LOADI       R64, 256            # 2:5
0010:   UPCALL      0, R64              # 2:1, OUT
0011:   EOF                             # 0:0
```

## Output

```plain
0=true?
0=false?
```
