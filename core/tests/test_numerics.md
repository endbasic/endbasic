# Test: Double to integer cast preserves negatives

## Source

```basic
DIM x AS INTEGER
x = -31000.3
OUT x
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:5
0001:   LOADC       R64, 0              ; 2:6, 31000.3
0002:   NEGD        R64                 ; 2:5
0003:   DTOI        R64                 ; 2:5
0004:   MOVE        R66, R64            ; 3:5
0005:   LOADI       R65, 258            ; 3:5
0006:   UPCALL      0, R65              ; 3:1, OUT
0007:   EOF                             ; 0:0
```

## Output

```plain
0=-31000%
```

# Test: Double to integer cast reports overflow

## Source

```basic
DIM x AS INTEGER
x = 3000000000.0
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:5
0001:   LOADC       R64, 0              ; 2:5, 3000000000
0002:   DTOI        R64                 ; 2:5
0003:   EOF                             ; 0:0
```

## Runtime errors

```plain
2:5: Cannot cast 3000000000 to integer due to overflow
```
