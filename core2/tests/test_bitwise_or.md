# Test: Two immediate integers

## Source

```basic
OUT 12 OR 10
```

## Disassembly

```asm
0000:   LOADI       R65, 12             ; 1:5
0001:   LOADI       R66, 10             ; 1:11
0002:   OR          R65, R65, R66       ; 1:8
0003:   LOADI       R64, 258            ; 1:5
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   EOF                             ; 0:0
```

## Output

```plain
0=14%
```

# Test: Type error with double

## Source

```basic
OUT 1.0 OR 2.0
```

## Compilation errors

```plain
1:9: Cannot OR DOUBLE and DOUBLE
```

# Test: Type error with string

## Source

```basic
OUT "a" OR "b"
```

## Compilation errors

```plain
1:9: Cannot OR STRING and STRING
```

# Test: Two immediate booleans

## Source

```basic
OUT TRUE OR FALSE
OUT FALSE OR FALSE
```

## Disassembly

```asm
0000:   LOADI       R65, 1              ; 1:5
0001:   LOADI       R66, 0              ; 1:13
0002:   OR          R65, R65, R66       ; 1:10
0003:   LOADI       R64, 256            ; 1:5
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   LOADI       R65, 0              ; 2:5
0006:   LOADI       R66, 0              ; 2:14
0007:   OR          R65, R65, R66       ; 2:11
0008:   LOADI       R64, 256            ; 2:5
0009:   UPCALL      0, R64              ; 2:1, OUT
0010:   EOF                             ; 0:0
```

## Output

```plain
0=true?
0=false?
```
