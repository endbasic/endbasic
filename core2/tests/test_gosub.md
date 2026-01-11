# Test: Basic flow

## Source

```basic
OUT "a"
GOSUB @sub
OUT "c"
END

@sub:
OUT "b"
RETURN
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADI       R65, 0              # 1:5
0002:   LOADI       R64, 259            # 1:5
0003:   UPCALL      0, R64              # 1:1, OUT
0004:   GOSUB       10                  # 2:7
0005:   LOADI       R65, 1              # 3:5
0006:   LOADI       R64, 259            # 3:5
0007:   UPCALL      0, R64              # 3:1, OUT
0008:   LOADI       R64, 0              # 4:1
0009:   END         R64                 # 4:1
0010:   LOADI       R65, 2              # 7:5
0011:   LOADI       R64, 259            # 7:5
0012:   UPCALL      0, R64              # 7:1, OUT
0013:   RETURN                          # 8:1
0014:   LOADI       R64, 0              # 0:0
0015:   END         R64                 # 0:0
```

## Output

```plain
0=a$
0=b$
0=c$
```

# Test: Nested GOSUB calls and returns

## Source

```basic
OUT "a"
GOSUB @sub1
OUT "f"
END

@sub1:
OUT "b"
GOSUB @sub2
OUT "e"
RETURN

@sub2:
OUT "c"
GOSUB @sub3
OUT "d"
RETURN

@sub3:
OUT "hello"
RETURN
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADI       R65, 0              # 1:5
0002:   LOADI       R64, 259            # 1:5
0003:   UPCALL      0, R64              # 1:1, OUT
0004:   GOSUB       10                  # 2:7
0005:   LOADI       R65, 1              # 3:5
0006:   LOADI       R64, 259            # 3:5
0007:   UPCALL      0, R64              # 3:1, OUT
0008:   LOADI       R64, 0              # 4:1
0009:   END         R64                 # 4:1
0010:   LOADI       R65, 2              # 7:5
0011:   LOADI       R64, 259            # 7:5
0012:   UPCALL      0, R64              # 7:1, OUT
0013:   GOSUB       18                  # 8:7
0014:   LOADI       R65, 3              # 9:5
0015:   LOADI       R64, 259            # 9:5
0016:   UPCALL      0, R64              # 9:1, OUT
0017:   RETURN                          # 10:1
0018:   LOADI       R65, 4              # 13:5
0019:   LOADI       R64, 259            # 13:5
0020:   UPCALL      0, R64              # 13:1, OUT
0021:   GOSUB       26                  # 14:7
0022:   LOADI       R65, 5              # 15:5
0023:   LOADI       R64, 259            # 15:5
0024:   UPCALL      0, R64              # 15:1, OUT
0025:   RETURN                          # 16:1
0026:   LOADI       R65, 6              # 19:5
0027:   LOADI       R64, 259            # 19:5
0028:   UPCALL      0, R64              # 19:1, OUT
0029:   RETURN                          # 20:1
0030:   LOADI       R64, 0              # 0:0
0031:   END         R64                 # 0:0
```

## Output

```plain
0=a$
0=b$
0=c$
0=hello$
0=d$
0=e$
0=f$
```

# Test: RETURN without GOSUB

## Source

```basic
RETURN
```

## Disassembly

```asm
0000:   ENTER       1                   # 0:0
0001:   RETURN                          # 1:1
0002:   LOADI       R64, 0              # 0:0
0003:   END         R64                 # 0:0
```

## Runtime errors

```plain
1:1: RETURN without GOSUB or FUNCTION call
```

# Test: GOSUB target requires backwards jump

## Source

```basic
GOTO @skip

@s:
OUT "In target"
RETURN

@skip:
GOSUB @s
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   JUMP        6                   # 1:6
0002:   LOADI       R65, 0              # 4:5
0003:   LOADI       R64, 259            # 4:5
0004:   UPCALL      0, R64              # 4:1, OUT
0005:   RETURN                          # 5:1
0006:   GOSUB       2                   # 8:7
0007:   LOADI       R64, 0              # 0:0
0008:   END         R64                 # 0:0
```

## Output

```plain
0=In target$
```
