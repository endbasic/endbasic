# Test: Two immediate doubles

## Source

```basic
OUT 9.0 / 4.0
```

## Disassembly

```asm
0000:   LOADC       R65, 0              ; 1:5, 9
0001:   LOADC       R66, 1              ; 1:11, 4
0002:   DIVD        R65, R65, R66       ; 1:9
0003:   LOADI       R64, 257            ; 1:5
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   EOF                             ; 0:0
```

## Output

```plain
0=2.25#
```

# Test: Two immediate integers

## Source

```basic
OUT 10 / 3
```

## Disassembly

```asm
0000:   LOADI       R65, 10             ; 1:5
0001:   LOADI       R66, 3              ; 1:10
0002:   DIVI        R65, R65, R66       ; 1:8
0003:   LOADI       R64, 258            ; 1:5
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   EOF                             ; 0:0
```

## Output

```plain
0=3%
```

# Test: Left integer operand needs type promotion to double

## Source

```basic
OUT 3 / 1.5
```

## Disassembly

```asm
0000:   LOADI       R65, 3              ; 1:5
0001:   LOADC       R66, 0              ; 1:9, 1.5
0002:   ITOD        R65                 ; 1:7
0003:   DIVD        R65, R65, R66       ; 1:7
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
OUT 9.0 / 3
```

## Disassembly

```asm
0000:   LOADC       R65, 0              ; 1:5, 9
0001:   LOADI       R66, 3              ; 1:11
0002:   ITOD        R66                 ; 1:11
0003:   DIVD        R65, R65, R66       ; 1:9
0004:   LOADI       R64, 257            ; 1:5
0005:   UPCALL      0, R64              ; 1:1, OUT
0006:   EOF                             ; 0:0
```

## Output

```plain
0=3#
```

# Test: Integer overflow

## Source

```basic
a = (-2147483647 - 1) / -1
```

## Disassembly

```asm
0000:   LOADC       R64, 0              ; 1:7, 2147483647
0001:   NEGI        R64                 ; 1:6
0002:   LOADI       R65, 1              ; 1:20
0003:   SUBI        R64, R64, R65       ; 1:18
0004:   LOADI       R65, 1              ; 1:26
0005:   NEGI        R65                 ; 1:25
0006:   DIVI        R64, R64, R65       ; 1:23
0007:   EOF                             ; 0:0
```

## Runtime errors

```plain
1:23: Integer underflow
```

# Test: Division by zero

## Source

```basic
a = 5 / 0
```

## Disassembly

```asm
0000:   LOADI       R64, 5              ; 1:5
0001:   LOADI       R65, 0              ; 1:9
0002:   DIVI        R64, R64, R65       ; 1:7
0003:   EOF                             ; 0:0
```

## Runtime errors

```plain
1:7: Division by zero
```
