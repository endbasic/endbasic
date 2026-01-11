# Test: Default zero values

## Source

```basic
DIM SHARED b1 AS BOOLEAN
DIM SHARED d1 AS DOUBLE
DIM SHARED i1 AS INTEGER
DIM SHARED i2
DIM SHARED s1 AS STRING

OUT b1, d1, i1, i2, s1
```

## Disassembly

```asm
0000:   ENTER       10                  # 0:0
0001:   LOADI       R0, 0               # 1:12
0002:   LOADI       R1, 0               # 2:12
0003:   LOADI       R2, 0               # 3:12
0004:   LOADI       R3, 0               # 4:12
0005:   ALLOC       R4, STRING          # 5:12
0006:   MOVE        R65, R0             # 7:5
0007:   LOADI       R64, 288            # 7:5
0008:   MOVE        R67, R1             # 7:9
0009:   LOADI       R66, 289            # 7:9
0010:   MOVE        R69, R2             # 7:13
0011:   LOADI       R68, 290            # 7:13
0012:   MOVE        R71, R3             # 7:17
0013:   LOADI       R70, 290            # 7:17
0014:   MOVE        R73, R4             # 7:21
0015:   LOADI       R72, 259            # 7:21
0016:   UPCALL      0, R64              # 7:1, OUT
0017:   LOADI       R64, 0              # 0:0
0018:   END         R64                 # 0:0
```

## Output

```plain
0=false? , 1=0# , 2=0% , 3=0% , 4=$
```

# Test: Set global variables to explicit values

## Source

```basic
DIM SHARED b1 AS BOOLEAN
DIM SHARED d1 AS DOUBLE
DIM SHARED i1 AS INTEGER
DIM SHARED i2
DIM SHARED s1 AS STRING

b1 = TRUE
d1 = 2.3
i1 = 5
i2 = 7
s1 = "text"
OUT b1, d1, i1, i2, s1
```

## Disassembly

```asm
0000:   ENTER       10                  # 0:0
0001:   LOADI       R0, 0               # 1:12
0002:   LOADI       R1, 0               # 2:12
0003:   LOADI       R2, 0               # 3:12
0004:   LOADI       R3, 0               # 4:12
0005:   ALLOC       R4, STRING          # 5:12
0006:   LOADI       R0, 1               # 7:6
0007:   LOADC       R1, 0               # 8:6
0008:   LOADI       R2, 5               # 9:6
0009:   LOADI       R3, 7               # 10:6
0010:   LOADI       R4, 1               # 11:6
0011:   MOVE        R65, R0             # 12:5
0012:   LOADI       R64, 288            # 12:5
0013:   MOVE        R67, R1             # 12:9
0014:   LOADI       R66, 289            # 12:9
0015:   MOVE        R69, R2             # 12:13
0016:   LOADI       R68, 290            # 12:13
0017:   MOVE        R71, R3             # 12:17
0018:   LOADI       R70, 290            # 12:17
0019:   MOVE        R73, R4             # 12:21
0020:   LOADI       R72, 259            # 12:21
0021:   UPCALL      0, R64              # 12:1, OUT
0022:   LOADI       R64, 0              # 0:0
0023:   END         R64                 # 0:0
```

## Output

```plain
0=true? , 1=2.3# , 2=5% , 3=7% , 4=text$
```

# Test: Global variables are accessible in functions

## Source

```basic
FUNCTION modify_global
    i1 = 3
    OUT "Inside after", i1
END FUNCTION

DIM SHARED i1
i1 = 2
OUT "Before", i1
OUT modify_global(2)
OUT "After", i1
```

## Disassembly

```asm
0000:   ENTER       4                   # 0:0
0001:   LOADI       R0, 0               # 6:12
0002:   LOADI       R0, 2               # 7:6
0003:   LOADI       R65, 0              # 8:5
0004:   LOADI       R64, 291            # 8:5
0005:   MOVE        R67, R0             # 8:15
0006:   LOADI       R66, 258            # 8:15
0007:   UPCALL      0, R64              # 8:1, OUT
0008:   CALL        R65, 18             # 9:5, MODIFY_GLOBAL
0009:   LOADI       R64, 258            # 9:5
0010:   UPCALL      0, R64              # 9:1, OUT
0011:   LOADI       R65, 1              # 10:5
0012:   LOADI       R64, 291            # 10:5
0013:   MOVE        R67, R0             # 10:14
0014:   LOADI       R66, 258            # 10:14
0015:   UPCALL      0, R64              # 10:1, OUT
0016:   LOADI       R64, 0              # 0:0
0017:   END         R64                 # 0:0

-- MODIFY_GLOBAL 
0018:   ENTER       5                   # 0:0
0019:   LOADI       R0, 3               # 2:10
0020:   LOADI       R66, 2              # 3:9
0021:   LOADI       R65, 291            # 3:9
0022:   MOVE        R68, R0             # 3:25
0023:   LOADI       R67, 258            # 3:25
0024:   UPCALL      0, R65              # 3:5, OUT
0025:   RETURN                          # 4:1
```

## Output

```plain
0=Before$ , 1=2%
0=Inside after$ , 1=3%
0=0%
0=After$ , 1=3%
```

# Test: Global variables are accessible in subroutines

## Source

```basic
SUB modify_global
    i1 = 3
    OUT "Inside after", i1
END SUB

DIM SHARED i1
i1 = 2
OUT "Before", i1
modify_global
OUT "After", i1
```

## Disassembly

```asm
0000:   ENTER       4                   # 0:0
0001:   LOADI       R0, 0               # 6:12
0002:   LOADI       R0, 2               # 7:6
0003:   LOADI       R65, 0              # 8:5
0004:   LOADI       R64, 291            # 8:5
0005:   MOVE        R67, R0             # 8:15
0006:   LOADI       R66, 258            # 8:15
0007:   UPCALL      0, R64              # 8:1, OUT
0008:   LOADI       R64, 0              # 9:1
0009:   CALL        R64, 17             # 9:1, MODIFY_GLOBAL
0010:   LOADI       R65, 1              # 10:5
0011:   LOADI       R64, 291            # 10:5
0012:   MOVE        R67, R0             # 10:14
0013:   LOADI       R66, 258            # 10:14
0014:   UPCALL      0, R64              # 10:1, OUT
0015:   LOADI       R64, 0              # 0:0
0016:   END         R64                 # 0:0

-- MODIFY_GLOBAL 
0017:   ENTER       4                   # 0:0
0018:   LOADI       R0, 3               # 2:10
0019:   LOADI       R65, 2              # 3:9
0020:   LOADI       R64, 291            # 3:9
0021:   MOVE        R67, R0             # 3:25
0022:   LOADI       R66, 258            # 3:25
0023:   UPCALL      0, R64              # 3:5, OUT
0024:   RETURN                          # 4:1
```

## Output

```plain
0=Before$ , 1=2%
0=Inside after$ , 1=3%
0=After$ , 1=3%
```

# Test: Integer to double promotion

## Source

```basic
DIM SHARED d AS DOUBLE
d = 6
OUT d
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADI       R0, 0               # 1:12
0002:   LOADI       R0, 6               # 2:5
0003:   ITOD        R0                  # 2:5
0004:   MOVE        R65, R0             # 3:5
0005:   LOADI       R64, 257            # 3:5
0006:   UPCALL      0, R64              # 3:1, OUT
0007:   LOADI       R64, 0              # 0:0
0008:   END         R64                 # 0:0
```

## Output

```plain
0=6#
```

# Test: Double to integer demotion

## Source

```basic
DIM SHARED i1 AS INTEGER
DIM SHARED i2 AS INTEGER
i1 = 3.2
i2 = 3.7
OUT i1, i2
```

## Disassembly

```asm
0000:   ENTER       4                   # 0:0
0001:   LOADI       R0, 0               # 1:12
0002:   LOADI       R1, 0               # 2:12
0003:   LOADC       R0, 0               # 3:6
0004:   DTOI        R0                  # 3:6
0005:   LOADC       R1, 1               # 4:6
0006:   DTOI        R1                  # 4:6
0007:   MOVE        R65, R0             # 5:5
0008:   LOADI       R64, 290            # 5:5
0009:   MOVE        R67, R1             # 5:9
0010:   LOADI       R66, 258            # 5:9
0011:   UPCALL      0, R64              # 5:1, OUT
0012:   LOADI       R64, 0              # 0:0
0013:   END         R64                 # 0:0
```

## Output

```plain
0=3% , 1=4%
```

# Test: Type mismatch in global variable assignment

## Source

```basic
DIM SHARED d
d = "foo"
```

## Compilation errors

```plain
2:5: STRING is not a number
```
