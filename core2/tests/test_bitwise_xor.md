# Test: Two immediate integers

## Source

```basic
OUT 12 XOR 10
```

## Disassembly

```asm
0000:   LOADI       R65, 12             ; 1:5
0001:   LOADI       R66, 10             ; 1:12
0002:   XOR         R65, R65, R66       ; 1:8
0003:   LOADI       R64, 258            ; 1:5
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   EOF                             ; 0:0
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
0000:   LOADI       R65, 1              ; 1:5
0001:   LOADI       R66, 0              ; 1:14
0002:   XOR         R65, R65, R66       ; 1:10
0003:   LOADI       R64, 256            ; 1:5
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   LOADI       R65, 1              ; 2:5
0006:   LOADI       R66, 1              ; 2:14
0007:   XOR         R65, R65, R66       ; 2:10
0008:   LOADI       R64, 256            ; 2:5
0009:   UPCALL      0, R64              ; 2:1, OUT
0010:   EOF                             ; 0:0
```

## Output

```plain
0=true?
0=false?
```
