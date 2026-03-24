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
0000:   LOADI       R64, 3              ; 1:5
0001:   MOVE        R65, R64            ; 2:13
0002:   MOVE        R66, R65            ; 3:10
0003:   LOADI       R67, 1              ; 3:10
0004:   CMPEQI      R68, R66, R67       ; 3:10
0005:   JMPF        R68, 7              ; 3:10
0006:   JUMP        72                  ; 3:10
0007:   MOVE        R66, R65            ; 3:13
0008:   LOADI       R67, 3              ; 3:13
0009:   CMPEQI      R68, R66, R67       ; 3:13
0010:   JMPF        R68, 12             ; 3:13
0011:   JUMP        72                  ; 3:13
0012:   MOVE        R66, R65            ; 3:16
0013:   LOADI       R67, 5              ; 3:16
0014:   CMPEQI      R68, R66, R67       ; 3:16
0015:   JMPF        R68, 17             ; 3:16
0016:   JUMP        72                  ; 3:16
0017:   MOVE        R66, R65            ; 3:19
0018:   LOADI       R67, 7              ; 3:19
0019:   CMPEQI      R68, R66, R67       ; 3:19
0020:   JMPF        R68, 22             ; 3:19
0021:   JUMP        72                  ; 3:19
0022:   MOVE        R66, R65            ; 3:22
0023:   LOADI       R67, 9              ; 3:22
0024:   CMPEQI      R68, R66, R67       ; 3:22
0025:   JMPF        R68, 27             ; 3:22
0026:   JUMP        72                  ; 3:22
0027:   JUMP        28                  ; 13:1
0028:   MOVE        R66, R65            ; 5:10
0029:   LOADI       R67, 0              ; 5:10
0030:   CMPEQI      R68, R66, R67       ; 5:10
0031:   JMPF        R68, 33             ; 5:10
0032:   JUMP        76                  ; 5:10
0033:   MOVE        R66, R65            ; 5:13
0034:   LOADI       R67, 2              ; 5:13
0035:   CMPEQI      R68, R66, R67       ; 5:13
0036:   JMPF        R68, 38             ; 5:13
0037:   JUMP        76                  ; 5:13
0038:   MOVE        R66, R65            ; 5:16
0039:   LOADI       R67, 4              ; 5:16
0040:   CMPEQI      R68, R66, R67       ; 5:16
0041:   JMPF        R68, 43             ; 5:16
0042:   JUMP        76                  ; 5:16
0043:   MOVE        R66, R65            ; 5:19
0044:   LOADI       R67, 6              ; 5:19
0045:   CMPEQI      R68, R66, R67       ; 5:19
0046:   JMPF        R68, 48             ; 5:19
0047:   JUMP        76                  ; 5:19
0048:   MOVE        R66, R65            ; 5:22
0049:   LOADI       R67, 8              ; 5:22
0050:   CMPEQI      R68, R66, R67       ; 5:22
0051:   JMPF        R68, 53             ; 5:22
0052:   JUMP        76                  ; 5:22
0053:   JUMP        54                  ; 13:1
0054:   MOVE        R66, R65            ; 7:10
0055:   LOADI       R67, 10             ; 7:10
0056:   CMPGEI      R68, R66, R67       ; 7:10
0057:   MOVE        R69, R65            ; 7:10
0058:   LOADI       R70, 20             ; 7:16
0059:   CMPLEI      R71, R69, R70       ; 7:10
0060:   AND         R72, R68, R71       ; 7:10
0061:   JMPF        R72, 63             ; 7:10
0062:   JUMP        80                  ; 7:10
0063:   JUMP        64                  ; 13:1
0064:   MOVE        R66, R65            ; 9:15
0065:   LOADI       R67, 0              ; 9:15
0066:   CMPLTI      R68, R66, R67       ; 9:15
0067:   JMPF        R68, 69             ; 9:15
0068:   JUMP        84                  ; 9:15
0069:   JUMP        70                  ; 13:1
0070:   JUMP        88                  ; 13:1
0071:   JUMP        91                  ; 13:1
0072:   LOADI       R66, 0              ; 4:13
0073:   LOADI       R65, 259            ; 4:13
0074:   UPCALL      0, R65              ; 4:9, OUT
0075:   JUMP        91                  ; 13:1
0076:   LOADI       R66, 1              ; 6:13
0077:   LOADI       R65, 259            ; 6:13
0078:   UPCALL      0, R65              ; 6:9, OUT
0079:   JUMP        91                  ; 13:1
0080:   LOADI       R66, 2              ; 8:13
0081:   LOADI       R65, 259            ; 8:13
0082:   UPCALL      0, R65              ; 8:9, OUT
0083:   JUMP        91                  ; 13:1
0084:   LOADI       R66, 3              ; 10:13
0085:   LOADI       R65, 259            ; 10:13
0086:   UPCALL      0, R65              ; 10:9, OUT
0087:   JUMP        91                  ; 13:1
0088:   LOADI       R66, 4              ; 12:13
0089:   LOADI       R65, 259            ; 12:13
0090:   UPCALL      0, R65              ; 12:9, OUT
0091:   EOF                             ; 0:0
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
0000:   LOADI       R64, 21             ; 1:5
0001:   MOVE        R65, R64            ; 2:13
0002:   MOVE        R66, R65            ; 3:10
0003:   LOADI       R67, 1              ; 3:10
0004:   CMPEQI      R68, R66, R67       ; 3:10
0005:   JMPF        R68, 7              ; 3:10
0006:   JUMP        10                  ; 3:10
0007:   JUMP        8                   ; 7:1
0008:   JUMP        14                  ; 7:1
0009:   JUMP        17                  ; 7:1
0010:   LOADI       R66, 0              ; 4:13
0011:   LOADI       R65, 259            ; 4:13
0012:   UPCALL      0, R65              ; 4:9, OUT
0013:   JUMP        17                  ; 7:1
0014:   LOADI       R66, 1              ; 6:13
0015:   LOADI       R65, 259            ; 6:13
0016:   UPCALL      0, R65              ; 6:9, OUT
0017:   EOF                             ; 0:0
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
0000:   UPCALL      0, R64              ; 1:13, MEANING_OF_LIFE
0001:   LOADI       R65, 1              ; 1:31
0002:   ADDI        R64, R64, R65       ; 1:29
0003:   MOVE        R65, R64            ; 2:10
0004:   LOADI       R66, 43             ; 2:10
0005:   CMPEQI      R67, R65, R66       ; 2:10
0006:   JMPF        R67, 8              ; 2:10
0007:   JUMP        16                  ; 2:10
0008:   JUMP        9                   ; 6:1
0009:   MOVE        R65, R64            ; 4:10
0010:   LOADI       R66, 100            ; 4:10
0011:   CMPEQI      R67, R65, R66       ; 4:10
0012:   JMPF        R67, 14             ; 4:10
0013:   JUMP        20                  ; 4:10
0014:   JUMP        15                  ; 6:1
0015:   JUMP        23                  ; 6:1
0016:   LOADI       R65, 0              ; 3:13
0017:   LOADI       R64, 259            ; 3:13
0018:   UPCALL      1, R64              ; 3:9, OUT
0019:   JUMP        23                  ; 6:1
0020:   LOADI       R65, 1              ; 5:13
0021:   LOADI       R64, 259            ; 5:13
0022:   UPCALL      1, R64              ; 5:9, OUT
0023:   EOF                             ; 0:0
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
0000:   UPCALL      0, R64              ; 1:13, MEANING_OF_LIFE
0001:   LOADI       R65, 1              ; 1:31
0002:   ADDI        R64, R64, R65       ; 1:29
0003:   JUMP        4                   ; 2:1
0004:   EOF                             ; 0:0
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
0000:   LOADI       R64, 0              ; 1:5
0001:   MOVE        R65, R64            ; 2:13
0002:   MOVE        R66, R65            ; 3:10
0003:   LOADI       R67, 1              ; 3:10
0004:   CMPEQS      R68, R66, R67       ; 3:10
0005:   JMPF        R68, 7              ; 3:10
0006:   JUMP        25                  ; 3:10
0007:   JUMP        8                   ; 9:1
0008:   MOVE        R66, R65            ; 5:15
0009:   LOADI       R67, 2              ; 5:15
0010:   CMPGTS      R68, R66, R67       ; 5:15
0011:   JMPF        R68, 13             ; 5:15
0012:   JUMP        29                  ; 5:15
0013:   JUMP        14                  ; 9:1
0014:   MOVE        R66, R65            ; 7:10
0015:   LOADI       R67, 3              ; 7:10
0016:   CMPGES      R68, R66, R67       ; 7:10
0017:   MOVE        R69, R65            ; 7:10
0018:   LOADI       R70, 4              ; 7:17
0019:   CMPLES      R71, R69, R70       ; 7:10
0020:   AND         R72, R68, R71       ; 7:10
0021:   JMPF        R72, 23             ; 7:10
0022:   JUMP        33                  ; 7:10
0023:   JUMP        24                  ; 9:1
0024:   JUMP        36                  ; 9:1
0025:   LOADI       R66, 1              ; 4:13
0026:   LOADI       R65, 259            ; 4:13
0027:   UPCALL      0, R65              ; 4:9, OUT
0028:   JUMP        36                  ; 9:1
0029:   LOADI       R66, 5              ; 6:13
0030:   LOADI       R65, 259            ; 6:13
0031:   UPCALL      0, R65              ; 6:9, OUT
0032:   JUMP        36                  ; 9:1
0033:   LOADI       R66, 6              ; 8:13
0034:   LOADI       R65, 259            ; 8:13
0035:   UPCALL      0, R65              ; 8:9, OUT
0036:   EOF                             ; 0:0
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
0000:   LOADC       R64, 0              ; 1:6
0001:   MOVE        R65, R64            ; 2:13
0002:   MOVE        R66, R65            ; 3:10
0003:   LOADI       R67, 2              ; 3:10
0004:   ITOD        R67                 ; 3:10
0005:   CMPEQD      R68, R66, R67       ; 3:10
0006:   JMPF        R68, 8              ; 3:10
0007:   JUMP        17                  ; 3:10
0008:   JUMP        9                   ; 7:1
0009:   MOVE        R66, R65            ; 5:15
0010:   LOADI       R67, 5              ; 5:15
0011:   ITOD        R67                 ; 5:15
0012:   CMPGTD      R68, R66, R67       ; 5:15
0013:   JMPF        R68, 15             ; 5:15
0014:   JUMP        21                  ; 5:15
0015:   JUMP        16                  ; 7:1
0016:   JUMP        24                  ; 7:1
0017:   LOADI       R66, 1              ; 4:13
0018:   LOADI       R65, 259            ; 4:13
0019:   UPCALL      0, R65              ; 4:9, OUT
0020:   JUMP        24                  ; 7:1
0021:   LOADI       R66, 2              ; 6:13
0022:   LOADI       R65, 259            ; 6:13
0023:   UPCALL      0, R65              ; 6:9, OUT
0024:   EOF                             ; 0:0
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
0000:   LOADI       R64, 11             ; 1:5
0001:   MOVE        R65, R64            ; 2:13
0002:   MOVE        R66, R65            ; 3:10
0003:   LOADC       R67, 0              ; 3:10
0004:   ITOD        R66                 ; 3:10
0005:   CMPEQD      R68, R66, R67       ; 3:10
0006:   JMPF        R68, 8              ; 3:10
0007:   JUMP        36                  ; 3:10
0008:   JUMP        9                   ; 9:1
0009:   MOVE        R66, R65            ; 5:10
0010:   LOADC       R67, 1              ; 5:10
0011:   ITOD        R66                 ; 5:10
0012:   CMPEQD      R68, R66, R67       ; 5:10
0013:   JMPF        R68, 15             ; 5:10
0014:   JUMP        40                  ; 5:10
0015:   MOVE        R66, R65            ; 5:15
0016:   LOADC       R67, 2              ; 5:16
0017:   NEGD        R67                 ; 5:15
0018:   ITOD        R66                 ; 5:15
0019:   CMPEQD      R68, R66, R67       ; 5:15
0020:   JMPF        R68, 22             ; 5:15
0021:   JUMP        40                  ; 5:15
0022:   JUMP        23                  ; 9:1
0023:   MOVE        R66, R65            ; 7:10
0024:   LOADC       R67, 3              ; 7:10
0025:   ITOD        R66                 ; 7:10
0026:   CMPGED      R68, R66, R67       ; 7:10
0027:   MOVE        R69, R65            ; 7:10
0028:   LOADC       R70, 4              ; 7:18
0029:   ITOD        R69                 ; 7:10
0030:   CMPLED      R71, R69, R70       ; 7:10
0031:   AND         R72, R68, R71       ; 7:10
0032:   JMPF        R72, 34             ; 7:10
0033:   JUMP        44                  ; 7:10
0034:   JUMP        35                  ; 9:1
0035:   JUMP        47                  ; 9:1
0036:   LOADI       R66, 5              ; 4:13
0037:   LOADI       R65, 259            ; 4:13
0038:   UPCALL      0, R65              ; 4:9, OUT
0039:   JUMP        47                  ; 9:1
0040:   LOADI       R66, 5              ; 6:13
0041:   LOADI       R65, 259            ; 6:13
0042:   UPCALL      0, R65              ; 6:9, OUT
0043:   JUMP        47                  ; 9:1
0044:   LOADI       R66, 6              ; 8:13
0045:   LOADI       R65, 259            ; 8:13
0046:   UPCALL      0, R65              ; 8:9, OUT
0047:   EOF                             ; 0:0
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
0000:   LOADI       R64, 5              ; 1:5
0001:   MOVE        R65, R64            ; 2:13
0002:   MOVE        R66, R65            ; 3:10
0003:   LOADI       R67, 5              ; 3:10
0004:   CMPEQI      R68, R66, R67       ; 3:10
0005:   JMPF        R68, 7              ; 3:10
0006:   JUMP        15                  ; 3:10
0007:   JUMP        8                   ; 12:1
0008:   MOVE        R66, R65            ; 10:10
0009:   LOADI       R67, 6              ; 10:10
0010:   CMPEQI      R68, R66, R67       ; 10:10
0011:   JMPF        R68, 13             ; 10:10
0012:   JUMP        31                  ; 10:10
0013:   JUMP        14                  ; 12:1
0014:   JUMP        34                  ; 12:1
0015:   LOADI       R66, 0              ; 4:13
0016:   LOADI       R65, 259            ; 4:13
0017:   UPCALL      0, R65              ; 4:9, OUT
0018:   LOADI       R64, 6              ; 5:13
0019:   MOVE        R65, R64            ; 6:21
0020:   MOVE        R66, R65            ; 7:18
0021:   LOADI       R67, 6              ; 7:18
0022:   CMPEQI      R68, R66, R67       ; 7:18
0023:   JMPF        R68, 25             ; 7:18
0024:   JUMP        27                  ; 7:18
0025:   JUMP        26                  ; 9:9
0026:   JUMP        30                  ; 9:9
0027:   LOADI       R66, 1              ; 8:21
0028:   LOADI       R65, 259            ; 8:21
0029:   UPCALL      0, R65              ; 8:17, OUT
0030:   JUMP        34                  ; 12:1
0031:   LOADI       R66, 2              ; 11:13
0032:   LOADI       R65, 259            ; 11:13
0033:   UPCALL      0, R65              ; 11:9, OUT
0034:   EOF                             ; 0:0
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
0000:   LOADI       R64, 5              ; 1:5
0001:   MOVE        R65, R64            ; 2:13
0002:   MOVE        R66, R65            ; 3:10
0003:   LOADI       R67, 5              ; 3:10
0004:   CMPEQI      R68, R66, R67       ; 3:10
0005:   JMPF        R68, 7              ; 3:10
0006:   JUMP        15                  ; 3:10
0007:   JUMP        8                   ; 8:1
0008:   MOVE        R66, R65            ; 6:10
0009:   LOADI       R67, 6              ; 6:10
0010:   CMPEQI      R68, R66, R67       ; 6:10
0011:   JMPF        R68, 13             ; 6:10
0012:   JUMP        20                  ; 6:10
0013:   JUMP        14                  ; 8:1
0014:   JUMP        23                  ; 8:1
0015:   LOADI       R66, 0              ; 4:13
0016:   LOADI       R65, 259            ; 4:13
0017:   UPCALL      0, R65              ; 4:9, OUT
0018:   GOSUB       24                  ; 5:15
0019:   JUMP        23                  ; 8:1
0020:   LOADI       R66, 1              ; 7:13
0021:   LOADI       R65, 259            ; 7:13
0022:   UPCALL      0, R65              ; 7:9, OUT
0023:   JUMP        37                  ; 9:6
0024:   LOADI       R64, 6              ; 11:5
0025:   MOVE        R65, R64            ; 12:13
0026:   MOVE        R66, R65            ; 13:10
0027:   LOADI       R67, 6              ; 13:10
0028:   CMPEQI      R68, R66, R67       ; 13:10
0029:   JMPF        R68, 31             ; 13:10
0030:   JUMP        33                  ; 13:10
0031:   JUMP        32                  ; 15:1
0032:   JUMP        36                  ; 15:1
0033:   LOADI       R66, 2              ; 14:13
0034:   LOADI       R65, 259            ; 14:13
0035:   UPCALL      0, R65              ; 14:9, OUT
0036:   RETURN                          ; 16:1
0037:   EOF                             ; 0:0
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
0000:   LOADI       R64, 42             ; 1:13
0001:   MOVE        R65, R64            ; 2:10
0002:   LOADI       R66, 1              ; 2:10
0003:   CMPEQI      R67, R65, R66       ; 2:10
0004:   JMPF        R67, 6              ; 2:10
0005:   JUMP        14                  ; 2:10
0006:   JUMP        7                   ; 5:1
0007:   MOVE        R65, R64            ; 4:10
0008:   LOADI       R66, 2              ; 4:10
0009:   CMPEQI      R67, R65, R66       ; 4:10
0010:   JMPF        R67, 12             ; 4:10
0011:   JUMP        18                  ; 4:10
0012:   JUMP        13                  ; 5:1
0013:   JUMP        18                  ; 5:1
0014:   LOADI       R65, 0              ; 3:13
0015:   LOADI       R64, 259            ; 3:13
0016:   UPCALL      0, R64              ; 3:9, OUT
0017:   JUMP        18                  ; 5:1
0018:   LOADI       R65, 1              ; 6:5
0019:   LOADI       R64, 259            ; 6:5
0020:   UPCALL      0, R64              ; 6:1, OUT
0021:   EOF                             ; 0:0
```

## Output

```plain
0=done$
```
