# Test: DATA values are collected in source order

## Source

```basic
DATA TRUE, 3
DATA , "hello"
GETDATA
```

## Disassembly

```asm
0000:   ENTER       1                   # 0:0
0001:   UPCALL      0, R64              # 3:1, GETDATA
0002:   LOADI       R64, 0              # 0:0
0003:   END         R64                 # 0:0
```

## Output

```plain
0=true? 1=3% 2=() 3=hello$
```

# Test: DATA values are collected in nested statements

## Source

```basic
IF FALSE THEN
    DATA 5
ELSE
    DATA 6
END IF
WHILE FALSE
    DATA 1
WEND
FOR i = 0 TO 0
    DATA 0
NEXT
GETDATA
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R64, 0              # 1:4
0002:   JMPF        R64, 4              # 1:4
0003:   JUMP        6                   # 1:4
0004:   LOADI       R64, 1              # 3:1
0005:   JMPF        R64, 6              # 3:1
0006:   LOADI       R64, 0              # 6:7
0007:   JMPF        R64, 9              # 6:7
0008:   JUMP        6                   # 6:7
0009:   LOADI       R64, 0              # 9:9
0010:   MOVE        R65, R64            # 9:5
0011:   LOADI       R66, 0              # 9:14
0012:   CMPLEI      R65, R65, R66       # 9:11
0013:   JMPF        R65, 18             # 9:5
0014:   MOVE        R64, R64            # 9:5
0015:   LOADI       R65, 1              # 9:15
0016:   ADDI        R64, R64, R65       # 9:11
0017:   JUMP        10                  # 9:5
0018:   UPCALL      0, R65              # 12:1, GETDATA
0019:   LOADI       R65, 0              # 0:0
0020:   END         R65                 # 0:0
```

## Output

```plain
0=5% 1=6% 2=1% 3=0%
```

# Test: GETDATA sees all DATA values even before execution

## Source

```basic
GETDATA
DATA 1
DATA 2
GETDATA
```

## Disassembly

```asm
0000:   ENTER       1                   # 0:0
0001:   UPCALL      0, R64              # 1:1, GETDATA
0002:   UPCALL      0, R64              # 4:1, GETDATA
0003:   LOADI       R64, 0              # 0:0
0004:   END         R64                 # 0:0
```

## Output

```plain
0=1% 1=2%
0=1% 1=2%
```

# Test: DATA rejects non-literal values at compile time

## Source

```basic
DATA 5 + 1
```

## Compilation errors

```plain
1:8: Expected comma after datum but found +
```
