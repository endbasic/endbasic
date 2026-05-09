# Test: Two immediate integers

## Source

```basic
OUT 12 >> 2
```

## Disassembly

```asm
0000:   LOADI       R65, 12             ; 1:5
0001:   LOADI       R66, 2              ; 1:11
0002:   SHR         R65, R65, R66       ; 1:8
0003:   LOADI       R64, 258            ; 1:5
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   EOF                             ; 0:0
```

## Output

```plain
0=3%
```

# Test: Shift by zero

## Source

```basic
OUT 7 >> 0
```

## Disassembly

```asm
0000:   LOADI       R65, 7              ; 1:5
0001:   LOADI       R66, 0              ; 1:10
0002:   SHR         R65, R65, R66       ; 1:7
0003:   LOADI       R64, 258            ; 1:5
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   EOF                             ; 0:0
```

## Output

```plain
0=7%
```

# Test: Shift amount larger than 31 (positive value)

## Source

```basic
OUT 1 >> 32
```

## Disassembly

```asm
0000:   LOADI       R65, 1              ; 1:5
0001:   LOADI       R66, 32             ; 1:10
0002:   SHR         R65, R65, R66       ; 1:7
0003:   LOADI       R64, 258            ; 1:5
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   EOF                             ; 0:0
```

## Output

```plain
0=0%
```

# Test: Shift amount larger than 31 (negative value)

## Source

```basic
OUT -1 >> 32
```

## Disassembly

```asm
0000:   LOADI       R65, 1              ; 1:6
0001:   NEGI        R65                 ; 1:5
0002:   LOADI       R66, 32             ; 1:11
0003:   SHR         R65, R65, R66       ; 1:8
0004:   LOADI       R64, 258            ; 1:5
0005:   UPCALL      0, R64              ; 1:1, OUT
0006:   EOF                             ; 0:0
```

## Output

```plain
0=-1%
```

# Test: Arithmetic right shift (sign extension)

## Source

```basic
OUT -8 >> 2
```

## Disassembly

```asm
0000:   LOADI       R65, 8              ; 1:6
0001:   NEGI        R65                 ; 1:5
0002:   LOADI       R66, 2              ; 1:11
0003:   SHR         R65, R65, R66       ; 1:8
0004:   LOADI       R64, 258            ; 1:5
0005:   UPCALL      0, R64              ; 1:1, OUT
0006:   EOF                             ; 0:0
```

## Output

```plain
0=-2%
```

# Test: Type error with double

## Source

```basic
OUT 1.0 >> 2
```

## Compilation errors

```plain
1:9: Cannot >> DOUBLE and INTEGER
```

# Test: Negative shift amount

## Source

```basic
OUT 1 >> -1
```

## Disassembly

```asm
0000:   LOADI       R65, 1              ; 1:5
0001:   LOADI       R66, 1              ; 1:11
0002:   NEGI        R66                 ; 1:10
0003:   SHR         R65, R65, R66       ; 1:7
0004:   LOADI       R64, 258            ; 1:5
0005:   UPCALL      0, R64              ; 1:1, OUT
0006:   EOF                             ; 0:0
```

## Runtime errors

```plain
1:7: Number of bits to >> (-1) must be positive
```
