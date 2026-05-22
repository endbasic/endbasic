# Test: Produce and consume empty strings

## Source

```basic
s$ = ""
FOR i% = 1 TO 18000000
    ' Produce a new string by _consuming_ an earlier one.
    s$ = s$ + ""
NEXT
OUT "success"
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:6
0001:   LOADI       R65, 1              ; 2:10
0002:   MOVE        R66, R65            ; 2:5
0003:   LOADC       R67, 1              ; 2:15
0004:   CMPLEI      R66, R66, R67       ; 2:12
0005:   JMPF        R66, 15             ; 2:5
0006:   MOVE        R66, R64            ; 4:10
0007:   LOADI       R67, 0              ; 4:15
0008:   CONCAT      R66, R66, R67       ; 4:13
0009:   MOVE        R64, R66            ; 4:5
0010:   MOVE        R66, R65            ; 2:5
0011:   LOADI       R67, 1              ; 2:23
0012:   ADDI        R66, R66, R67       ; 2:12
0013:   MOVE        R65, R66            ; 2:5
0014:   JUMP        2                   ; 2:5
0015:   LOADI       R67, 2              ; 6:5
0016:   LOADI       R66, 259            ; 6:5
0017:   UPCALL      0, R66              ; 6:1, OUT
0018:   EOF                             ; 0:0
```

## Output

```plain
0=success$
```

# Test: Produce and consume non-empty strings

## Source

```basic
s$ = ""
FOR i% = 1 TO 18000000
    ' Produce a new string by _consuming_ an earlier one.
    s$ = s$ + "x"
    ' But keep overall memory bounded.
    s$ = ""
NEXT
OUT "success"
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:6
0001:   LOADI       R65, 1              ; 2:10
0002:   MOVE        R66, R65            ; 2:5
0003:   LOADC       R67, 1              ; 2:15
0004:   CMPLEI      R66, R66, R67       ; 2:12
0005:   JMPF        R66, 16             ; 2:5
0006:   MOVE        R66, R64            ; 4:10
0007:   LOADI       R67, 2              ; 4:15
0008:   CONCAT      R66, R66, R67       ; 4:13
0009:   MOVE        R64, R66            ; 4:5
0010:   LOADI       R64, 0              ; 6:10
0011:   MOVE        R66, R65            ; 2:5
0012:   LOADI       R67, 1              ; 2:23
0013:   ADDI        R66, R66, R67       ; 2:12
0014:   MOVE        R65, R66            ; 2:5
0015:   JUMP        2                   ; 2:5
0016:   LOADI       R67, 3              ; 8:5
0017:   LOADI       R66, 259            ; 8:5
0018:   UPCALL      0, R66              ; 8:1, OUT
0019:   EOF                             ; 0:0
```

## Runtime errors

```plain
4:13: Out of heap space
```
