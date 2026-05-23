# Test: Two immediate doubles

## Source

```basic
OUT 5.0 - 3.0
```

## Disassembly

```asm
0000:   LOADC       R65, 0              ; 1:5, 5
0001:   LOADC       R66, 1              ; 1:11, 3
0002:   SUBD        R65, R65, R66       ; 1:9
0003:   LOADI       R64, 257            ; 1:5
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   EOF                             ; 0:0
```

## Output

```plain
0=2#
```

# Test: Two immediate integers

## Source

```basic
OUT 10 - 3
```

## Disassembly

```asm
0000:   LOADI       R65, 10             ; 1:5
0001:   LOADI       R66, 3              ; 1:10
0002:   SUBI        R65, R65, R66       ; 1:8
0003:   LOADI       R64, 258            ; 1:5
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   EOF                             ; 0:0
```

## Output

```plain
0=7%
```

# Test: Left integer operand needs type promotion to double

## Source

```basic
OUT 2 - 8.3
```

## Disassembly

```asm
0000:   LOADI       R65, 2              ; 1:5
0001:   LOADC       R66, 0              ; 1:9, 8.3
0002:   ITOD        R65                 ; 1:7
0003:   SUBD        R65, R65, R66       ; 1:7
0004:   LOADI       R64, 257            ; 1:5
0005:   UPCALL      0, R64              ; 1:1, OUT
0006:   EOF                             ; 0:0
```

## Output

```plain
0=-6.300000000000001#
```

# Test: Right integer operand needs type promotion to double

## Source

```basic
OUT 8.3 - 2
```

## Disassembly

```asm
0000:   LOADC       R65, 0              ; 1:5, 8.3
0001:   LOADI       R66, 2              ; 1:11
0002:   ITOD        R66                 ; 1:11
0003:   SUBD        R65, R65, R66       ; 1:9
0004:   LOADI       R64, 257            ; 1:5
0005:   UPCALL      0, R64              ; 1:1, OUT
0006:   EOF                             ; 0:0
```

## Output

```plain
0=6.300000000000001#
```

# Test: Integer overflow

## Source

```basic
a = -2147483640 - 20
```

## Disassembly

```asm
0000:   LOADC       R64, 0              ; 1:6, 2147483640
0001:   NEGI        R64                 ; 1:5
0002:   LOADI       R65, 20             ; 1:19
0003:   SUBI        R64, R64, R65       ; 1:17
0004:   EOF                             ; 0:0
```

## Runtime errors

```plain
1:17: Integer underflow
```
