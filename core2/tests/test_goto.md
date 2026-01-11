# Test: Basic flow

## Source

```basic
OUT "a"
GOTO @foo
OUT "b"
@foo:
OUT "c"
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADI       R65, 0              # 1:5
0002:   LOADI       R64, 259            # 1:5
0003:   UPCALL      0, R64              # 1:1, OUT
0004:   JUMP        8                   # 2:6
0005:   LOADI       R65, 1              # 3:5
0006:   LOADI       R64, 259            # 3:5
0007:   UPCALL      0, R64              # 3:1, OUT
0008:   LOADI       R65, 2              # 5:5
0009:   LOADI       R64, 259            # 5:5
0010:   UPCALL      0, R64              # 5:1, OUT
0011:   LOADI       R64, 0              # 0:0
0012:   END         R64                 # 0:0
```

## Output

```plain
0=a$
0=c$
```

# Test: GOTO jumps to label at end of file.

## Source

```basic
GOTO @end
OUT "a"
@end:
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   JUMP        5                   # 1:6
0002:   LOADI       R65, 0              # 2:5
0003:   LOADI       R64, 259            # 2:5
0004:   UPCALL      0, R64              # 2:1, OUT
0005:   LOADI       R64, 0              # 0:0
0006:   END         R64                 # 0:0
```

# Test: GOTO target requires backwards jump

## Source

```basic
GOTO @skip
OUT "Skipped"
@print_it:
OUT "Print something"
GOTO @end
@skip:
GOTO @print_it
@end:
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   JUMP        9                   # 1:6
0002:   LOADI       R65, 0              # 2:5
0003:   LOADI       R64, 259            # 2:5
0004:   UPCALL      0, R64              # 2:1, OUT
0005:   LOADI       R65, 1              # 4:5
0006:   LOADI       R64, 259            # 4:5
0007:   UPCALL      0, R64              # 4:1, OUT
0008:   JUMP        10                  # 5:6
0009:   JUMP        5                   # 7:6
0010:   LOADI       R64, 0              # 0:0
0011:   END         R64                 # 0:0
```

## Output

```plain
0=Print something$
```
