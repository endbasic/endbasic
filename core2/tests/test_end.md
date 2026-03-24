# Test: Call to END and nothing else

## Source

```basic
END
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:1
0001:   END         R64                 ; 1:1
0002:   EOF                             ; 0:0
```

# Test: Exit code is an integer immediate

## Source

```basic
END 42
```

## Disassembly

```asm
0000:   LOADI       R64, 42             ; 1:5
0001:   END         R64                 ; 1:1
0002:   EOF                             ; 0:0
```

## Exit code

```plain
42
```

# Test: Exit code is a double immediate and needs demotion

## Source

```basic
END 43.98
```

## Disassembly

```asm
0000:   LOADC       R64, 0              ; 1:5
0001:   DTOI        R64                 ; 1:5
0002:   END         R64                 ; 1:1
0003:   EOF                             ; 0:0
```

## Exit code

```plain
44
```

# Test: Exit code is in a global variable

## Source

```basic
DIM SHARED i
i = 5
END i
```

## Disassembly

```asm
0000:   LOADI       R0, 0               ; 1:12
0001:   LOADI       R0, 5               ; 2:5
0002:   MOVE        R64, R0             ; 3:5
0003:   END         R64                 ; 3:1
0004:   EOF                             ; 0:0
```

## Exit code

```plain
5
```

# Test: Exit code is in a local variable

## Source

```basic
i = 3
END i
```

## Disassembly

```asm
0000:   LOADI       R64, 3              ; 1:5
0001:   MOVE        R65, R64            ; 2:5
0002:   END         R65                 ; 2:1
0003:   EOF                             ; 0:0
```

## Exit code

```plain
3
```

# Test: Exit code is of an invalid type

## Source

```basic
END "foo"
```

## Compilation errors

```plain
1:5: STRING is not a number
```

# Test: Exit code cannot be negative

## Source

```basic
END -3
```

## Compilation errors

```plain
1:5: Exit code must be in the 0..127 range
```

# Test: Exit code cannot be larger than 127

## Source

```basic
END 128
```

## Compilation errors

```plain
1:5: Exit code must be in the 0..127 range
```

# Test: Dynamic exit code cannot be negative

## Source

```basic
i = -3
END i
```

## Disassembly

```asm
0000:   LOADI       R64, 3              ; 1:6
0001:   NEGI        R64                 ; 1:5
0002:   MOVE        R65, R64            ; 2:5
0003:   END         R65                 ; 2:1
0004:   EOF                             ; 0:0
```

## Runtime errors

```plain
2:1: Exit code must be in the 0..127 range
```

# Test: Dynamic exit code cannot be larger than 127

## Source

```basic
i = 128
END i
```

## Disassembly

```asm
0000:   LOADI       R64, 128            ; 1:5
0001:   MOVE        R65, R64            ; 2:5
0002:   END         R65                 ; 2:1
0003:   EOF                             ; 0:0
```

## Runtime errors

```plain
2:1: Exit code must be in the 0..127 range
```

# Test: END exits from inside FOR loop

## Source

```basic
FOR i = 1 TO 10
    IF i = 3 THEN END 42
NEXT
```

## Disassembly

```asm
0000:   LOADI       R64, 1              ; 1:9
0001:   MOVE        R65, R64            ; 1:5
0002:   LOADI       R66, 10             ; 1:14
0003:   CMPLEI      R65, R65, R66       ; 1:11
0004:   JMPF        R65, 15             ; 1:5
0005:   MOVE        R65, R64            ; 2:8
0006:   LOADI       R66, 3              ; 2:12
0007:   CMPEQI      R65, R65, R66       ; 2:10
0008:   JMPF        R65, 11             ; 2:8
0009:   LOADI       R65, 42             ; 2:23
0010:   END         R65                 ; 2:19
0011:   MOVE        R64, R64            ; 1:5
0012:   LOADI       R65, 1              ; 1:16
0013:   ADDI        R64, R64, R65       ; 1:11
0014:   JUMP        1                   ; 1:5
0015:   EOF                             ; 0:0
```

## Exit code

```plain
42
```
