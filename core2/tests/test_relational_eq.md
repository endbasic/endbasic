# Test: Two immediate integers

## Source

```basic
OUT 2 = 2
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R65, 2              # 1:5
0002:   LOADI       R66, 2              # 1:9
0003:   CMPEQI      R65, R65, R66       # 1:7
0004:   LOADI       R64, 256            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   EOF                             # 0:0
```

## Output

```plain
0=true?
```

# Test: Two immediate doubles

## Source

```basic
OUT 2.5 = 2.0
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADC       R65, 0              # 1:5
0002:   LOADC       R66, 1              # 1:11
0003:   CMPEQD      R65, R65, R66       # 1:9
0004:   LOADI       R64, 256            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   EOF                             # 0:0
```

## Output

```plain
0=false?
```

# Test: Left integer operand needs type promotion to double

## Source

```basic
OUT 2 = 2.0
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R65, 2              # 1:5
0002:   LOADC       R66, 0              # 1:9
0003:   ITOD        R65                 # 1:7
0004:   CMPEQD      R65, R65, R66       # 1:7
0005:   LOADI       R64, 256            # 1:5
0006:   UPCALL      0, R64              # 1:1, OUT
0007:   EOF                             # 0:0
```

## Output

```plain
0=true?
```

# Test: Two immediate strings

## Source

```basic
OUT "foo" = "bar"
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R65, 0              # 1:5
0002:   LOADI       R66, 1              # 1:13
0003:   CMPEQS      R65, R65, R66       # 1:11
0004:   LOADI       R64, 256            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   EOF                             # 0:0
```

## Output

```plain
0=false?
```

# Test: Two immediate booleans

## Source

```basic
OUT TRUE = FALSE
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R65, 1              # 1:5
0002:   LOADI       R66, 0              # 1:12
0003:   CMPEQB      R65, R65, R66       # 1:10
0004:   LOADI       R64, 256            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   EOF                             # 0:0
```

## Output

```plain
0=false?
```

# Test: Type error between integer and string

## Source

```basic
OUT 1 = "1"
```

## Compilation errors

```plain
1:7: Cannot = INTEGER and STRING
```
