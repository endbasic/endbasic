# Test: Two immediate integers

## Source

```basic
OUT 3 >= 2
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R65, 3              # 1:5
0002:   LOADI       R66, 2              # 1:10
0003:   CMPGEI      R65, R65, R66       # 1:7
0004:   LOADI       R64, 256            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   LOADI       R64, 0              # 0:0
0007:   END         R64                 # 0:0
```

## Output

```plain
0=true?
```

# Test: Two immediate doubles

## Source

```basic
OUT 2.5 >= 2.0
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADC       R65, 0              # 1:5
0002:   LOADC       R66, 1              # 1:12
0003:   CMPGED      R65, R65, R66       # 1:9
0004:   LOADI       R64, 256            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   LOADI       R64, 0              # 0:0
0007:   END         R64                 # 0:0
```

## Output

```plain
0=true?
```

# Test: Left integer operand needs type promotion to double

## Source

```basic
OUT 2 >= 2.5
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R65, 2              # 1:5
0002:   LOADC       R66, 0              # 1:10
0003:   ITOD        R65                 # 1:7
0004:   CMPGED      R65, R65, R66       # 1:7
0005:   LOADI       R64, 256            # 1:5
0006:   UPCALL      0, R64              # 1:1, OUT
0007:   LOADI       R64, 0              # 0:0
0008:   END         R64                 # 0:0
```

## Output

```plain
0=false?
```

# Test: Two immediate strings

## Source

```basic
OUT "foo" >= "bar"
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R65, 0              # 1:5
0002:   LOADI       R66, 1              # 1:14
0003:   CMPGES      R65, R65, R66       # 1:11
0004:   LOADI       R64, 256            # 1:5
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   LOADI       R64, 0              # 0:0
0007:   END         R64                 # 0:0
```

## Output

```plain
0=true?
```

# Test: Type error with boolean

## Source

```basic
OUT TRUE >= FALSE
```

## Compilation errors

```plain
1:10: Cannot >= BOOLEAN and BOOLEAN
```
