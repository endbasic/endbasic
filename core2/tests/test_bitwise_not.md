# Test: Immediate integer

## Source

```basic
OUT NOT 12
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADI       R65, 12             # 1:9
0002:   NOT         R65                 # 1:5
0003:   LOADI       R64, 258            # 1:5
0004:   UPCALL      0, R64              # 1:1, OUT
0005:   EOF                             # 0:0
```

## Output

```plain
0=-13%
```

# Test: Type error with double

## Source

```basic
OUT NOT 1.0
```

## Compilation errors

```plain
1:5: Expected INTEGER but found DOUBLE
```

# Test: Type error with string

## Source

```basic
OUT NOT "a"
```

## Compilation errors

```plain
1:5: Expected INTEGER but found STRING
```

# Test: Immediate boolean

## Source

```basic
OUT NOT TRUE
OUT NOT FALSE
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R65, 1              # 1:9
0002:   LOADI       R66, 1              # 1:5
0003:   XOR         R65, R65, R66       # 1:5
0004:   LOADI       R64, 256            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   LOADI       R65, 0              # 2:9
0007:   LOADI       R66, 1              # 2:5
0008:   XOR         R65, R65, R66       # 2:5
0009:   LOADI       R64, 256            # 2:5
0010:   UPCALL      0, R64              # 2:1, OUT
0011:   EOF                             # 0:0
```

## Output

```plain
0=false?
0=true?
```
