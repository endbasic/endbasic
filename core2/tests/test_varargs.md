# Test: No arguments

## Source

```basic
OUT
```

## Disassembly

```asm
0000:   ENTER       1                   # 0:0
0001:   LOADI       R64, 0              # 1:1
0002:   UPCALL      0, R64              # 1:1, OUT
0003:   LOADI       R64, 0              # 0:0
0004:   END         R64                 # 0:0
```

## Output

```plain
0=()
```

# Test: Multiple arguments, all present

## Source

```basic
OUT 100, 200, 300
```

## Disassembly

```asm
0000:   ENTER       6                   # 0:0
0001:   LOADI       R65, 100            # 1:5
0002:   LOADI       R64, 290            # 1:5
0003:   LOADI       R67, 200            # 1:10
0004:   LOADI       R66, 290            # 1:10
0005:   LOADI       R69, 300            # 1:15
0006:   LOADI       R68, 258            # 1:15
0007:   UPCALL      0, R64              # 1:1, OUT
0008:   LOADI       R64, 0              # 0:0
0009:   END         R64                 # 0:0
```

## Output

```plain
0=100% , 1=200% , 2=300%
```

# Test: Multiple arguments, some missing

## Source

```basic
OUT 100, , 300,
```

## Disassembly

```asm
0000:   ENTER       6                   # 0:0
0001:   LOADI       R65, 100            # 1:5
0002:   LOADI       R64, 290            # 1:5
0003:   LOADI       R66, 32             # 1:10
0004:   LOADI       R68, 300            # 1:12
0005:   LOADI       R67, 290            # 1:12
0006:   LOADI       R69, 0              # 1:16
0007:   UPCALL      0, R64              # 1:1, OUT
0008:   LOADI       R64, 0              # 0:0
0009:   END         R64                 # 0:0
```

## Output

```plain
0=100% , 1=() , 2=300% , 3=()
```

# Test: Multiple arguments, different separators

## Source

```basic
OUT 100; 200 AS 300, 400
```

## Disassembly

```asm
0000:   ENTER       8                   # 0:0
0001:   LOADI       R65, 100            # 1:5
0002:   LOADI       R64, 274            # 1:5
0003:   LOADI       R67, 200            # 1:10
0004:   LOADI       R66, 306            # 1:10
0005:   LOADI       R69, 300            # 1:17
0006:   LOADI       R68, 290            # 1:17
0007:   LOADI       R71, 400            # 1:22
0008:   LOADI       R70, 258            # 1:22
0009:   UPCALL      0, R64              # 1:1, OUT
0010:   LOADI       R64, 0              # 0:0
0011:   END         R64                 # 0:0
```

## Output

```plain
0=100% ; 1=200% AS 2=300% , 3=400%
```

# Test: Multiple arguments, different types

## Source

```basic
OUT 100, "Foo"
```

## Disassembly

```asm
0000:   ENTER       4                   # 0:0
0001:   LOADI       R65, 100            # 1:5
0002:   LOADI       R64, 290            # 1:5
0003:   LOADI       R67, 0              # 1:10
0004:   LOADI       R66, 259            # 1:10
0005:   UPCALL      0, R64              # 1:1, OUT
0006:   LOADI       R64, 0              # 0:0
0007:   END         R64                 # 0:0
```

## Output

```plain
0=100% , 1=Foo$
```
