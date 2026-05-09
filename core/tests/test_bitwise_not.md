# Test: Immediate integer

## Source

```basic
OUT NOT 12
```

## Disassembly

```asm
0000:   LOADI       R65, 12             ; 1:9
0001:   NOT         R65                 ; 1:5
0002:   LOADI       R64, 258            ; 1:5
0003:   UPCALL      0, R64              ; 1:1, OUT
0004:   EOF                             ; 0:0
```

## Output

```plain
0=-13%
```

# Test: Type error with double

## Source

```basic
OUT NOT 1.0
```

## Compilation errors

```plain
1:5: Expected INTEGER but found DOUBLE
```

# Test: Type error with string

## Source

```basic
OUT NOT "a"
```

## Compilation errors

```plain
1:5: Expected INTEGER but found STRING
```

# Test: Immediate boolean

## Source

```basic
OUT NOT TRUE
OUT NOT FALSE
```

## Disassembly

```asm
0000:   LOADI       R65, 1              ; 1:9
0001:   LOADI       R66, 1              ; 1:5
0002:   XOR         R65, R65, R66       ; 1:5
0003:   LOADI       R64, 256            ; 1:5
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   LOADI       R65, 0              ; 2:9
0006:   LOADI       R66, 1              ; 2:5
0007:   XOR         R65, R65, R66       ; 2:5
0008:   LOADI       R64, 256            ; 2:5
0009:   UPCALL      0, R64              ; 2:1, OUT
0010:   EOF                             ; 0:0
```

## Output

```plain
0=false?
0=true?
```
