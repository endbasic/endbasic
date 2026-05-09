# Test: Two immediate doubles

## Source

```basic
OUT 4.5 + 2.3
```

## Disassembly

```asm
0000:   LOADC       R65, 0              ; 1:5
0001:   LOADC       R66, 1              ; 1:11
0002:   ADDD        R65, R65, R66       ; 1:9
0003:   LOADI       R64, 257            ; 1:5
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   EOF                             ; 0:0
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
0000:   LOADI       R65, 2              ; 1:5
0001:   LOADI       R66, 3              ; 1:9
0002:   ADDI        R65, R65, R66       ; 1:7
0003:   LOADI       R64, 258            ; 1:5
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   EOF                             ; 0:0
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
0000:   LOADI       R65, 0              ; 1:5
0001:   LOADI       R66, 1              ; 1:11
0002:   CONCAT      R65, R65, R66       ; 1:9
0003:   LOADI       R64, 259            ; 1:5
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   EOF                             ; 0:0
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
0000:   LOADI       R65, 2              ; 1:5
0001:   LOADC       R66, 0              ; 1:9
0002:   ITOD        R65                 ; 1:7
0003:   ADDD        R65, R65, R66       ; 1:7
0004:   LOADI       R64, 257            ; 1:5
0005:   UPCALL      0, R64              ; 1:1, OUT
0006:   EOF                             ; 0:0
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
0000:   LOADC       R65, 0              ; 1:5
0001:   LOADI       R66, 2              ; 1:11
0002:   ITOD        R66                 ; 1:11
0003:   ADDD        R65, R65, R66       ; 1:9
0004:   LOADI       R64, 257            ; 1:5
0005:   UPCALL      0, R64              ; 1:1, OUT
0006:   EOF                             ; 0:0
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
0000:   LOADC       R64, 0              ; 1:5
0001:   LOADI       R65, 20             ; 1:18
0002:   ADDI        R64, R64, R65       ; 1:16
0003:   EOF                             ; 0:0
```

## Runtime errors

```plain
1:16: Integer overflow
```

# Test: Array subscripts in addition chain

## Source

```basic
DIM a(3) AS INTEGER
a(0) = 10
a(1) = 20
a(2) = 30
OUT a(0) + a(1) + a(2)
```

## Disassembly

```asm
0000:   LOADI       R65, 3              ; 1:7
0001:   ALLOCA      R64, [1]%, R65      ; 1:5
0002:   LOADI       R65, 10             ; 2:8
0003:   LOADI       R66, 0              ; 2:3
0004:   STOREA      R64, R65, R66       ; 2:1
0005:   LOADI       R65, 20             ; 3:8
0006:   LOADI       R66, 1              ; 3:3
0007:   STOREA      R64, R65, R66       ; 3:1
0008:   LOADI       R65, 30             ; 4:8
0009:   LOADI       R66, 2              ; 4:3
0010:   STOREA      R64, R65, R66       ; 4:1
0011:   LOADI       R67, 0              ; 5:7
0012:   LOADA       R66, R64, R67       ; 5:5
0013:   LOADI       R68, 1              ; 5:14
0014:   LOADA       R67, R64, R68       ; 5:12
0015:   ADDI        R66, R66, R67       ; 5:10
0016:   LOADI       R68, 2              ; 5:21
0017:   LOADA       R67, R64, R68       ; 5:19
0018:   ADDI        R66, R66, R67       ; 5:17
0019:   LOADI       R65, 258            ; 5:5
0020:   UPCALL      0, R65              ; 5:1, OUT
0021:   EOF                             ; 0:0
```

## Output

```plain
0=60%
```
