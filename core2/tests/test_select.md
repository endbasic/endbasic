# Test: Basic SELECT CASE matching

## Source

```basic
n = 3
SELECT CASE n
    CASE 1, 3, 5, 7, 9
        OUT "odd"
    CASE 0, 2, 4, 6, 8
        OUT "even"
    CASE 10 TO 20
        OUT "large"
    CASE IS < 0
        OUT "negative"
    CASE ELSE
        OUT "too large"
END SELECT
```

## Disassembly

```asm
0000:   ENTER       9                   # 0:0
0001:   LOADI       R64, 3              # 1:5
0002:   MOVE        R65, R64            # 2:13
0003:   MOVE        R66, R65            # 3:10
0004:   LOADI       R67, 1              # 3:10
0005:   CMPEQI      R68, R66, R67       # 3:10
0006:   JMPF        R68, 8              # 3:10
0007:   JUMP        73                  # 3:10
0008:   MOVE        R66, R65            # 3:13
0009:   LOADI       R67, 3              # 3:13
0010:   CMPEQI      R68, R66, R67       # 3:13
0011:   JMPF        R68, 13             # 3:13
0012:   JUMP        73                  # 3:13
0013:   MOVE        R66, R65            # 3:16
0014:   LOADI       R67, 5              # 3:16
0015:   CMPEQI      R68, R66, R67       # 3:16
0016:   JMPF        R68, 18             # 3:16
0017:   JUMP        73                  # 3:16
0018:   MOVE        R66, R65            # 3:19
0019:   LOADI       R67, 7              # 3:19
0020:   CMPEQI      R68, R66, R67       # 3:19
0021:   JMPF        R68, 23             # 3:19
0022:   JUMP        73                  # 3:19
0023:   MOVE        R66, R65            # 3:22
0024:   LOADI       R67, 9              # 3:22
0025:   CMPEQI      R68, R66, R67       # 3:22
0026:   JMPF        R68, 28             # 3:22
0027:   JUMP        73                  # 3:22
0028:   JUMP        29                  # 13:1
0029:   MOVE        R66, R65            # 5:10
0030:   LOADI       R67, 0              # 5:10
0031:   CMPEQI      R68, R66, R67       # 5:10
0032:   JMPF        R68, 34             # 5:10
0033:   JUMP        77                  # 5:10
0034:   MOVE        R66, R65            # 5:13
0035:   LOADI       R67, 2              # 5:13
0036:   CMPEQI      R68, R66, R67       # 5:13
0037:   JMPF        R68, 39             # 5:13
0038:   JUMP        77                  # 5:13
0039:   MOVE        R66, R65            # 5:16
0040:   LOADI       R67, 4              # 5:16
0041:   CMPEQI      R68, R66, R67       # 5:16
0042:   JMPF        R68, 44             # 5:16
0043:   JUMP        77                  # 5:16
0044:   MOVE        R66, R65            # 5:19
0045:   LOADI       R67, 6              # 5:19
0046:   CMPEQI      R68, R66, R67       # 5:19
0047:   JMPF        R68, 49             # 5:19
0048:   JUMP        77                  # 5:19
0049:   MOVE        R66, R65            # 5:22
0050:   LOADI       R67, 8              # 5:22
0051:   CMPEQI      R68, R66, R67       # 5:22
0052:   JMPF        R68, 54             # 5:22
0053:   JUMP        77                  # 5:22
0054:   JUMP        55                  # 13:1
0055:   MOVE        R66, R65            # 7:10
0056:   LOADI       R67, 10             # 7:10
0057:   CMPGEI      R68, R66, R67       # 7:10
0058:   MOVE        R69, R65            # 7:10
0059:   LOADI       R70, 20             # 7:16
0060:   CMPLEI      R71, R69, R70       # 7:10
0061:   AND         R72, R68, R71       # 7:10
0062:   JMPF        R72, 64             # 7:10
0063:   JUMP        81                  # 7:10
0064:   JUMP        65                  # 13:1
0065:   MOVE        R66, R65            # 9:15
0066:   LOADI       R67, 0              # 9:15
0067:   CMPLTI      R68, R66, R67       # 9:15
0068:   JMPF        R68, 70             # 9:15
0069:   JUMP        85                  # 9:15
0070:   JUMP        71                  # 13:1
0071:   JUMP        89                  # 13:1
0072:   JUMP        92                  # 13:1
0073:   LOADI       R66, 0              # 4:13
0074:   LOADI       R65, 259            # 4:13
0075:   UPCALL      0, R65              # 4:9, OUT
0076:   JUMP        92                  # 13:1
0077:   LOADI       R66, 1              # 6:13
0078:   LOADI       R65, 259            # 6:13
0079:   UPCALL      0, R65              # 6:9, OUT
0080:   JUMP        92                  # 13:1
0081:   LOADI       R66, 2              # 8:13
0082:   LOADI       R65, 259            # 8:13
0083:   UPCALL      0, R65              # 8:9, OUT
0084:   JUMP        92                  # 13:1
0085:   LOADI       R66, 3              # 10:13
0086:   LOADI       R65, 259            # 10:13
0087:   UPCALL      0, R65              # 10:9, OUT
0088:   JUMP        92                  # 13:1
0089:   LOADI       R66, 4              # 12:13
0090:   LOADI       R65, 259            # 12:13
0091:   UPCALL      0, R65              # 12:9, OUT
0092:   LOADI       R65, 0              # 0:0
0093:   END         R65                 # 0:0
```

## Output

```plain
0=odd$
```

# Test: CASE ELSE fallback

## Source

```basic
n = 21
SELECT CASE n
    CASE 1
        OUT "one"
    CASE ELSE
        OUT "fallback"
END SELECT
```

## Disassembly

```asm
0000:   ENTER       5                   # 0:0
0001:   LOADI       R64, 21             # 1:5
0002:   MOVE        R65, R64            # 2:13
0003:   MOVE        R66, R65            # 3:10
0004:   LOADI       R67, 1              # 3:10
0005:   CMPEQI      R68, R66, R67       # 3:10
0006:   JMPF        R68, 8              # 3:10
0007:   JUMP        11                  # 3:10
0008:   JUMP        9                   # 7:1
0009:   JUMP        15                  # 7:1
0010:   JUMP        18                  # 7:1
0011:   LOADI       R66, 0              # 4:13
0012:   LOADI       R65, 259            # 4:13
0013:   UPCALL      0, R65              # 4:9, OUT
0014:   JUMP        18                  # 7:1
0015:   LOADI       R66, 1              # 6:13
0016:   LOADI       R65, 259            # 6:13
0017:   UPCALL      0, R65              # 6:9, OUT
0018:   LOADI       R65, 0              # 0:0
0019:   END         R65                 # 0:0
```

## Output

```plain
0=fallback$
```

# Test: SELECT test expression evaluated once

## Source

```basic
SELECT CASE MEANING_OF_LIFE + 1
    CASE 43
        OUT "ok"
    CASE 100
        OUT "nope"
END SELECT
```

## Disassembly

```asm
0000:   ENTER       4                   # 0:0
0001:   UPCALL      0, R64              # 1:13, MEANING_OF_LIFE
0002:   LOADI       R65, 1              # 1:31
0003:   ADDI        R64, R64, R65       # 1:29
0004:   MOVE        R65, R64            # 2:10
0005:   LOADI       R66, 43             # 2:10
0006:   CMPEQI      R67, R65, R66       # 2:10
0007:   JMPF        R67, 9              # 2:10
0008:   JUMP        17                  # 2:10
0009:   JUMP        10                  # 6:1
0010:   MOVE        R65, R64            # 4:10
0011:   LOADI       R66, 100            # 4:10
0012:   CMPEQI      R67, R65, R66       # 4:10
0013:   JMPF        R67, 15             # 4:10
0014:   JUMP        21                  # 4:10
0015:   JUMP        16                  # 6:1
0016:   JUMP        24                  # 6:1
0017:   LOADI       R65, 0              # 3:13
0018:   LOADI       R64, 259            # 3:13
0019:   UPCALL      1, R64              # 3:9, OUT
0020:   JUMP        24                  # 6:1
0021:   LOADI       R65, 1              # 5:13
0022:   LOADI       R64, 259            # 5:13
0023:   UPCALL      1, R64              # 5:9, OUT
0024:   LOADI       R64, 0              # 0:0
0025:   END         R64                 # 0:0
```

## Output

```plain
0=ok$
```

# Test: SELECT with no cases still evaluates expression once

## Source

```basic
SELECT CASE MEANING_OF_LIFE + 1
END SELECT
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   UPCALL      0, R64              # 1:13, MEANING_OF_LIFE
0002:   LOADI       R65, 1              # 1:31
0003:   ADDI        R64, R64, R65       # 1:29
0004:   JUMP        5                   # 2:1
0005:   LOADI       R64, 0              # 0:0
0006:   END         R64                 # 0:0
```

# Test: CASE IS and TO with strings

## Source

```basic
s = "M"
SELECT CASE s
    CASE "exact"
        OUT "exact"
    CASE IS > "ZZZ"
        OUT "is"
    CASE "B" TO "Y"
        OUT "to"
END SELECT
```

## Disassembly

```asm
0000:   ENTER       9                   # 0:0
0001:   LOADI       R64, 0              # 1:5
0002:   MOVE        R65, R64            # 2:13
0003:   MOVE        R66, R65            # 3:10
0004:   LOADI       R67, 1              # 3:10
0005:   CMPEQS      R68, R66, R67       # 3:10
0006:   JMPF        R68, 8              # 3:10
0007:   JUMP        26                  # 3:10
0008:   JUMP        9                   # 9:1
0009:   MOVE        R66, R65            # 5:15
0010:   LOADI       R67, 2              # 5:15
0011:   CMPGTS      R68, R66, R67       # 5:15
0012:   JMPF        R68, 14             # 5:15
0013:   JUMP        30                  # 5:15
0014:   JUMP        15                  # 9:1
0015:   MOVE        R66, R65            # 7:10
0016:   LOADI       R67, 3              # 7:10
0017:   CMPGES      R68, R66, R67       # 7:10
0018:   MOVE        R69, R65            # 7:10
0019:   LOADI       R70, 4              # 7:17
0020:   CMPLES      R71, R69, R70       # 7:10
0021:   AND         R72, R68, R71       # 7:10
0022:   JMPF        R72, 24             # 7:10
0023:   JUMP        34                  # 7:10
0024:   JUMP        25                  # 9:1
0025:   JUMP        37                  # 9:1
0026:   LOADI       R66, 1              # 4:13
0027:   LOADI       R65, 259            # 4:13
0028:   UPCALL      0, R65              # 4:9, OUT
0029:   JUMP        37                  # 9:1
0030:   LOADI       R66, 5              # 6:13
0031:   LOADI       R65, 259            # 6:13
0032:   UPCALL      0, R65              # 6:9, OUT
0033:   JUMP        37                  # 9:1
0034:   LOADI       R66, 6              # 8:13
0035:   LOADI       R65, 259            # 8:13
0036:   UPCALL      0, R65              # 8:9, OUT
0037:   LOADI       R65, 0              # 0:0
0038:   END         R65                 # 0:0
```

## Output

```plain
0=to$
```

# Test: DOUBLE test expression compared against INTEGER guards

## Source

```basic
n# = 5.1
SELECT CASE n#
    CASE 2
        OUT "bad"
    CASE IS > 5
        OUT "ok"
END SELECT
```

## Disassembly

```asm
0000:   ENTER       5                   # 0:0
0001:   LOADC       R64, 0              # 1:6
0002:   MOVE        R65, R64            # 2:13
0003:   MOVE        R66, R65            # 3:10
0004:   LOADI       R67, 2              # 3:10
0005:   ITOD        R67                 # 3:10
0006:   CMPEQD      R68, R66, R67       # 3:10
0007:   JMPF        R68, 9              # 3:10
0008:   JUMP        18                  # 3:10
0009:   JUMP        10                  # 7:1
0010:   MOVE        R66, R65            # 5:15
0011:   LOADI       R67, 5              # 5:15
0012:   ITOD        R67                 # 5:15
0013:   CMPGTD      R68, R66, R67       # 5:15
0014:   JMPF        R68, 16             # 5:15
0015:   JUMP        22                  # 5:15
0016:   JUMP        17                  # 7:1
0017:   JUMP        25                  # 7:1
0018:   LOADI       R66, 1              # 4:13
0019:   LOADI       R65, 259            # 4:13
0020:   UPCALL      0, R65              # 4:9, OUT
0021:   JUMP        25                  # 7:1
0022:   LOADI       R66, 2              # 6:13
0023:   LOADI       R65, 259            # 6:13
0024:   UPCALL      0, R65              # 6:9, OUT
0025:   LOADI       R65, 0              # 0:0
0026:   END         R65                 # 0:0
```

## Output

```plain
0=ok$
```

# Test: INTEGER test expression compared against DOUBLE guards

## Source

```basic
n = 11
SELECT CASE n
    CASE 2.0
        OUT "bad"
    CASE 5.0, -1.0
        OUT "bad"
    CASE 10.2 TO 11.8
        OUT "ok"
END SELECT
```

## Disassembly

```asm
0000:   ENTER       9                   # 0:0
0001:   LOADI       R64, 11             # 1:5
0002:   MOVE        R65, R64            # 2:13
0003:   MOVE        R66, R65            # 3:10
0004:   LOADC       R67, 0              # 3:10
0005:   ITOD        R66                 # 3:10
0006:   CMPEQD      R68, R66, R67       # 3:10
0007:   JMPF        R68, 9              # 3:10
0008:   JUMP        37                  # 3:10
0009:   JUMP        10                  # 9:1
0010:   MOVE        R66, R65            # 5:10
0011:   LOADC       R67, 1              # 5:10
0012:   ITOD        R66                 # 5:10
0013:   CMPEQD      R68, R66, R67       # 5:10
0014:   JMPF        R68, 16             # 5:10
0015:   JUMP        41                  # 5:10
0016:   MOVE        R66, R65            # 5:15
0017:   LOADC       R67, 2              # 5:16
0018:   NEGD        R67                 # 5:15
0019:   ITOD        R66                 # 5:15
0020:   CMPEQD      R68, R66, R67       # 5:15
0021:   JMPF        R68, 23             # 5:15
0022:   JUMP        41                  # 5:15
0023:   JUMP        24                  # 9:1
0024:   MOVE        R66, R65            # 7:10
0025:   LOADC       R67, 3              # 7:10
0026:   ITOD        R66                 # 7:10
0027:   CMPGED      R68, R66, R67       # 7:10
0028:   MOVE        R69, R65            # 7:10
0029:   LOADC       R70, 4              # 7:18
0030:   ITOD        R69                 # 7:10
0031:   CMPLED      R71, R69, R70       # 7:10
0032:   AND         R72, R68, R71       # 7:10
0033:   JMPF        R72, 35             # 7:10
0034:   JUMP        45                  # 7:10
0035:   JUMP        36                  # 9:1
0036:   JUMP        48                  # 9:1
0037:   LOADI       R66, 5              # 4:13
0038:   LOADI       R65, 259            # 4:13
0039:   UPCALL      0, R65              # 4:9, OUT
0040:   JUMP        48                  # 9:1
0041:   LOADI       R66, 5              # 6:13
0042:   LOADI       R65, 259            # 6:13
0043:   UPCALL      0, R65              # 6:9, OUT
0044:   JUMP        48                  # 9:1
0045:   LOADI       R66, 6              # 8:13
0046:   LOADI       R65, 259            # 8:13
0047:   UPCALL      0, R65              # 8:9, OUT
0048:   LOADI       R65, 0              # 0:0
0049:   END         R65                 # 0:0
```

## Output

```plain
0=ok$
```

# Test: Nested SELECT blocks

## Source

```basic
i = 5
SELECT CASE i
    CASE 5
        OUT "ok 1"
        i = 6
        SELECT CASE i
            CASE 6
                OUT "ok 2"
        END SELECT
    CASE 6
        OUT "not ok"
END SELECT
```

## Disassembly

```asm
0000:   ENTER       5                   # 0:0
0001:   LOADI       R64, 5              # 1:5
0002:   MOVE        R65, R64            # 2:13
0003:   MOVE        R66, R65            # 3:10
0004:   LOADI       R67, 5              # 3:10
0005:   CMPEQI      R68, R66, R67       # 3:10
0006:   JMPF        R68, 8              # 3:10
0007:   JUMP        16                  # 3:10
0008:   JUMP        9                   # 12:1
0009:   MOVE        R66, R65            # 10:10
0010:   LOADI       R67, 6              # 10:10
0011:   CMPEQI      R68, R66, R67       # 10:10
0012:   JMPF        R68, 14             # 10:10
0013:   JUMP        32                  # 10:10
0014:   JUMP        15                  # 12:1
0015:   JUMP        35                  # 12:1
0016:   LOADI       R66, 0              # 4:13
0017:   LOADI       R65, 259            # 4:13
0018:   UPCALL      0, R65              # 4:9, OUT
0019:   LOADI       R64, 6              # 5:13
0020:   MOVE        R65, R64            # 6:21
0021:   MOVE        R66, R65            # 7:18
0022:   LOADI       R67, 6              # 7:18
0023:   CMPEQI      R68, R66, R67       # 7:18
0024:   JMPF        R68, 26             # 7:18
0025:   JUMP        28                  # 7:18
0026:   JUMP        27                  # 9:9
0027:   JUMP        31                  # 9:9
0028:   LOADI       R66, 1              # 8:21
0029:   LOADI       R65, 259            # 8:21
0030:   UPCALL      0, R65              # 8:17, OUT
0031:   JUMP        35                  # 12:1
0032:   LOADI       R66, 2              # 11:13
0033:   LOADI       R65, 259            # 11:13
0034:   UPCALL      0, R65              # 11:9, OUT
0035:   LOADI       R65, 0              # 0:0
0036:   END         R65                 # 0:0
```

## Output

```plain
0=ok 1$
0=ok 2$
```

# Test: SELECT nested indirectly through GOSUB

## Source

```basic
i = 5
SELECT CASE i
    CASE 5
        OUT "ok 1"
        GOSUB @another
    CASE 6
        OUT "not ok"
END SELECT
GOTO @end
@another
i = 6
SELECT CASE i
    CASE 6
        OUT "ok 2"
END SELECT
RETURN
@end
```

## Disassembly

```asm
0000:   ENTER       5                   # 0:0
0001:   LOADI       R64, 5              # 1:5
0002:   MOVE        R65, R64            # 2:13
0003:   MOVE        R66, R65            # 3:10
0004:   LOADI       R67, 5              # 3:10
0005:   CMPEQI      R68, R66, R67       # 3:10
0006:   JMPF        R68, 8              # 3:10
0007:   JUMP        16                  # 3:10
0008:   JUMP        9                   # 8:1
0009:   MOVE        R66, R65            # 6:10
0010:   LOADI       R67, 6              # 6:10
0011:   CMPEQI      R68, R66, R67       # 6:10
0012:   JMPF        R68, 14             # 6:10
0013:   JUMP        21                  # 6:10
0014:   JUMP        15                  # 8:1
0015:   JUMP        24                  # 8:1
0016:   LOADI       R66, 0              # 4:13
0017:   LOADI       R65, 259            # 4:13
0018:   UPCALL      0, R65              # 4:9, OUT
0019:   GOSUB       25                  # 5:15
0020:   JUMP        24                  # 8:1
0021:   LOADI       R66, 1              # 7:13
0022:   LOADI       R65, 259            # 7:13
0023:   UPCALL      0, R65              # 7:9, OUT
0024:   JUMP        38                  # 9:6
0025:   LOADI       R64, 6              # 11:5
0026:   MOVE        R65, R64            # 12:13
0027:   MOVE        R66, R65            # 13:10
0028:   LOADI       R67, 6              # 13:10
0029:   CMPEQI      R68, R66, R67       # 13:10
0030:   JMPF        R68, 32             # 13:10
0031:   JUMP        34                  # 13:10
0032:   JUMP        33                  # 15:1
0033:   JUMP        37                  # 15:1
0034:   LOADI       R66, 2              # 14:13
0035:   LOADI       R65, 259            # 14:13
0036:   UPCALL      0, R65              # 14:9, OUT
0037:   RETURN                          # 16:1
0038:   LOADI       R65, 0              # 0:0
0039:   END         R65                 # 0:0
```

## Output

```plain
0=ok 1$
0=ok 2$
```

# Test: CASE guard type mismatch

## Source

```basic
SELECT CASE 2
    CASE FALSE
END SELECT
```

## Compilation errors

```plain
2:10: Cannot = INTEGER and BOOLEAN
```

# Test: SELECT with no matching CASE

## Source

```basic
SELECT CASE 42
    CASE 1
        OUT "unexpected"
    CASE 2
END SELECT
OUT "done"
```

## Disassembly

```asm
0000:   ENTER       4                   # 0:0
0001:   LOADI       R64, 42             # 1:13
0002:   MOVE        R65, R64            # 2:10
0003:   LOADI       R66, 1              # 2:10
0004:   CMPEQI      R67, R65, R66       # 2:10
0005:   JMPF        R67, 7              # 2:10
0006:   JUMP        15                  # 2:10
0007:   JUMP        8                   # 5:1
0008:   MOVE        R65, R64            # 4:10
0009:   LOADI       R66, 2              # 4:10
0010:   CMPEQI      R67, R65, R66       # 4:10
0011:   JMPF        R67, 13             # 4:10
0012:   JUMP        19                  # 4:10
0013:   JUMP        14                  # 5:1
0014:   JUMP        19                  # 5:1
0015:   LOADI       R65, 0              # 3:13
0016:   LOADI       R64, 259            # 3:13
0017:   UPCALL      0, R64              # 3:9, OUT
0018:   JUMP        19                  # 5:1
0019:   LOADI       R65, 1              # 6:5
0020:   LOADI       R64, 259            # 6:5
0021:   UPCALL      0, R64              # 6:1, OUT
0022:   LOADI       R64, 0              # 0:0
0023:   END         R64                 # 0:0
```

## Output

```plain
0=done$
```
