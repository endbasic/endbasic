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
0000:   ENTER       6                   # 0:0
0001:   LOADI       R64, 0              # 1:6
0002:   LOADI       R65, 1              # 2:6
0003:   MOVE        R67, R64            # 4:6
0004:   MOVE        R68, R65            # 4:11
0005:   CONCAT      R66, R67, R68       # 4:9
0006:   MOVE        R68, R66            # 5:6
0007:   LOADI       R69, 2              # 5:11
0008:   CONCAT      R67, R68, R69       # 5:9
0009:   MOVE        R69, R64            # 7:5
0010:   LOADI       R68, 259            # 7:5
0011:   UPCALL      0, R68              # 7:1, OUT
0012:   MOVE        R69, R65            # 8:5
0013:   LOADI       R68, 259            # 8:5
0014:   UPCALL      0, R68              # 8:1, OUT
0015:   MOVE        R69, R66            # 9:5
0016:   LOADI       R68, 259            # 9:5
0017:   UPCALL      0, R68              # 9:1, OUT
0018:   MOVE        R69, R67            # 10:5
0019:   LOADI       R68, 259            # 10:5
0020:   UPCALL      0, R68              # 10:1, OUT
0021:   LOADI       R68, 0              # 0:0
0022:   END         R68                 # 0:0
```

## Output

```plain
0=Constant string 1$
0=Constant string 2$
0=Constant string 1Constant string 2$
0=Constant string 1Constant string 2.$
```
