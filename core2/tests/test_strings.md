# Test: Concatenation

## Source

```basic
c1 = "Constant string 1"
c2 = "Constant string 2"

c3 = c1 + c2
c4 = c3 + "."

OUT c1
OUT c2
OUT c3
OUT c4
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:6
0001:   LOADI       R65, 1              ; 2:6
0002:   MOVE        R66, R64            ; 4:6
0003:   MOVE        R67, R65            ; 4:11
0004:   CONCAT      R66, R66, R67       ; 4:9
0005:   MOVE        R67, R66            ; 5:6
0006:   LOADI       R68, 2              ; 5:11
0007:   CONCAT      R67, R67, R68       ; 5:9
0008:   MOVE        R69, R64            ; 7:5
0009:   LOADI       R68, 259            ; 7:5
0010:   UPCALL      0, R68              ; 7:1, OUT
0011:   MOVE        R69, R65            ; 8:5
0012:   LOADI       R68, 259            ; 8:5
0013:   UPCALL      0, R68              ; 8:1, OUT
0014:   MOVE        R69, R66            ; 9:5
0015:   LOADI       R68, 259            ; 9:5
0016:   UPCALL      0, R68              ; 9:1, OUT
0017:   MOVE        R69, R67            ; 10:5
0018:   LOADI       R68, 259            ; 10:5
0019:   UPCALL      0, R68              ; 10:1, OUT
0020:   EOF                             ; 0:0
```

## Output

```plain
0=Constant string 1$
0=Constant string 2$
0=Constant string 1Constant string 2$
0=Constant string 1Constant string 2.$
```
