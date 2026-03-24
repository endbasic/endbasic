# Test: Two immediate doubles

## Source

```basic
OUT 2.0 ^ 3.0
```

## Disassembly

```asm
0000:   LOADC       R65, 0              ; 1:5
0001:   LOADC       R66, 1              ; 1:11
0002:   POWD        R65, R65, R66       ; 1:9
0003:   LOADI       R64, 257            ; 1:5
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   EOF                             ; 0:0
```

## Output

```plain
0=8#
```

# Test: Two immediate integers

## Source

```basic
OUT 2 ^ 8
```

## Disassembly

```asm
0000:   LOADI       R65, 2              ; 1:5
0001:   LOADI       R66, 8              ; 1:9
0002:   POWI        R65, R65, R66       ; 1:7
0003:   LOADI       R64, 258            ; 1:5
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   EOF                             ; 0:0
```

## Output

```plain
0=256%
```

# Test: Left integer operand needs type promotion to double

## Source

```basic
OUT 4 ^ 0.5
```

## Disassembly

```asm
0000:   LOADI       R65, 4              ; 1:5
0001:   LOADC       R66, 0              ; 1:9
0002:   ITOD        R65                 ; 1:7
0003:   POWD        R65, R65, R66       ; 1:7
0004:   LOADI       R64, 257            ; 1:5
0005:   UPCALL      0, R64              ; 1:1, OUT
0006:   EOF                             ; 0:0
```

## Output

```plain
0=2#
```

# Test: Right integer operand needs type promotion to double

## Source

```basic
OUT 2.5 ^ 3
```

## Disassembly

```asm
0000:   LOADC       R65, 0              ; 1:5
0001:   LOADI       R66, 3              ; 1:11
0002:   ITOD        R66                 ; 1:11
0003:   POWD        R65, R65, R66       ; 1:9
0004:   LOADI       R64, 257            ; 1:5
0005:   UPCALL      0, R64              ; 1:1, OUT
0006:   EOF                             ; 0:0
```

## Output

```plain
0=15.625#
```

# Test: Integer overflow

## Source

```basic
a = 46341 ^ 2
```

## Disassembly

```asm
0000:   LOADI       R64, 46341          ; 1:5
0001:   LOADI       R65, 2              ; 1:13
0002:   POWI        R64, R64, R65       ; 1:11
0003:   EOF                             ; 0:0
```

## Runtime errors

```plain
1:11: Integer overflow
```

# Test: Negative exponent

## Source

```basic
a = 2 ^ -1
```

## Disassembly

```asm
0000:   LOADI       R64, 2              ; 1:5
0001:   LOADI       R65, 1              ; 1:10
0002:   NEGI        R65                 ; 1:9
0003:   POWI        R64, R64, R65       ; 1:7
0004:   EOF                             ; 0:0
```

## Runtime errors

```plain
1:7: Exponent -1 cannot be negative
```
