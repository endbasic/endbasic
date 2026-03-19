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
0011:   EOF                             # 0:0
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
0005:   EOF                             # 0:0
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
0010:   EOF                             # 0:0
```

## Output

```plain
0=Print something$
```

# Test: GOTO with numeric label

## Source

```basic
GOTO 20
OUT "skipped"
20 OUT "target"
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   JUMP        5                   # 1:6
0002:   LOADI       R65, 0              # 2:5
0003:   LOADI       R64, 259            # 2:5
0004:   UPCALL      0, R64              # 2:1, OUT
0005:   LOADI       R65, 1              # 3:8
0006:   LOADI       R64, 259            # 3:8
0007:   UPCALL      0, R64              # 3:4, OUT
0008:   EOF                             # 0:0
```

## Output

```plain
0=target$
```

# Test: GOTO to numeric label in middle of line

## Source

```basic
GOTO 20
OUT "skipped": 20 OUT "target"
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   JUMP        5                   # 1:6
0002:   LOADI       R65, 0              # 2:5
0003:   LOADI       R64, 259            # 2:5
0004:   UPCALL      0, R64              # 2:1, OUT
0005:   LOADI       R65, 1              # 2:23
0006:   LOADI       R64, 259            # 2:23
0007:   UPCALL      0, R64              # 2:19, OUT
0008:   EOF                             # 0:0
```

## Output

```plain
0=target$
```

# Test: GOTO unknown label

## Source

```basic
GOTO @missing
```

## Compilation errors

```plain
1:6: Unknown label missing
```

# Test: GOTO unknown numeric label

## Source

```basic
GOTO 10
```

## Compilation errors

```plain
1:6: Unknown label 10
```

# Test: Duplicate label

## Source

```basic
@foo:
@foo:
```

## Compilation errors

```plain
2:1: Duplicate label foo
```

# Test: Duplicate label in nested control flow

## Source

```basic
i = 0
@a
    @b
        @c
            i = i + 1
            IF i = 1 THEN: GOTO @b: END IF
            @a
            IF i = 2 THEN: GOTO @c: END IF
            IF i = 3 THEN: GOTO @out: END IF
@out
```

## Compilation errors

```plain
7:13: Duplicate label a
```

# Test: GOTO as the last statement in a loop

## Source

```basic
i = 0
@again:
IF i = 5 THEN END i
i = i + 1
GOTO @again
```

## Disassembly

```asm
0000:   ENTER       3                   # 0:0
0001:   LOADI       R64, 0              # 1:5
0002:   MOVE        R65, R64            # 3:4
0003:   LOADI       R66, 5              # 3:8
0004:   CMPEQI      R65, R65, R66       # 3:6
0005:   JMPF        R65, 8              # 3:4
0006:   MOVE        R65, R64            # 3:19
0007:   END         R65                 # 3:15
0008:   MOVE        R64, R64            # 4:5
0009:   LOADI       R65, 1              # 4:9
0010:   ADDI        R64, R64, R65       # 4:7
0011:   JUMP        2                   # 5:6
0012:   EOF                             # 0:0
```

## Exit code

```plain
5
```
