# Test: Elaborate execution flow

## Source

```basic
a = 10

SUB foo
    a = 20
    OUT "Inside", a
END SUB

OUT "Before", a
foo
OUT "After", a
```

## Disassembly

```asm
0000:   ENTER       5                   # 0:0
0001:   LOADI       R64, 10             # 1:5
0002:   LOADI       R66, 0              # 8:5
0003:   LOADI       R65, 291            # 8:5
0004:   MOVE        R68, R64            # 8:15
0005:   LOADI       R67, 258            # 8:15
0006:   UPCALL      0, R65              # 8:1, OUT
0007:   LOADI       R65, 0              # 9:1
0008:   CALL        R65, 16             # 9:1, FOO
0009:   LOADI       R66, 1              # 10:5
0010:   LOADI       R65, 291            # 10:5
0011:   MOVE        R68, R64            # 10:14
0012:   LOADI       R67, 258            # 10:14
0013:   UPCALL      0, R65              # 10:1, OUT
0014:   LOADI       R65, 0              # 0:0
0015:   END         R65                 # 0:0

-- FOO 
0016:   ENTER       5                   # 0:0
0017:   LOADI       R64, 20             # 4:9
0018:   LOADI       R66, 2              # 5:9
0019:   LOADI       R65, 291            # 5:9
0020:   MOVE        R68, R64            # 5:19
0021:   LOADI       R67, 258            # 5:19
0022:   UPCALL      0, R65              # 5:5, OUT
0023:   RETURN                          # 6:1
```

## Output

```plain
0=Before$ , 1=10%
0=Inside$ , 1=20%
0=After$ , 1=10%
```

# Test: Subroutine call requires jumping backwards

## Source

```basic
SUB first
    OUT "first"
END SUB

SUB second
    first
END SUB

second
```

## Disassembly

```asm
0000:   ENTER       1                   # 0:0
0001:   LOADI       R64, 0              # 9:1
0002:   CALL        R64, 10             # 9:1, SECOND
0003:   LOADI       R64, 0              # 0:0
0004:   END         R64                 # 0:0

-- FIRST 
0005:   ENTER       2                   # 0:0
0006:   LOADI       R65, 0              # 2:9
0007:   LOADI       R64, 259            # 2:9
0008:   UPCALL      0, R64              # 2:5, OUT
0009:   RETURN                          # 3:1

-- SECOND 
0010:   ENTER       1                   # 0:0
0011:   LOADI       R64, 0              # 6:5
0012:   CALL        R64, 5              # 6:5, FIRST
0013:   RETURN                          # 7:1
```

## Output

```plain
0=first$
```

# Test: Annotation not allowed in subroutine call

## Source

```basic
OUT$ 3
```

## Compilation errors

```plain
1:1: Type annotation not allowed in OUT$
```

# Test: Local variables

## Source

```basic
SUB modify_2
    var = 2
    OUT "Inside modify_2", var
END SUB

SUB modify_1
    var = 1
    OUT "Before modify_2", var
    modify_2
    OUT "After modify_2", var
END SUB

var = 0
OUT "Before modify_1", var
modify_1
OUT "After modify_1", var
```

## Disassembly

```asm
0000:   ENTER       5                   # 0:0
0001:   LOADI       R64, 0              # 13:7
0002:   LOADI       R66, 0              # 14:5
0003:   LOADI       R65, 291            # 14:5
0004:   MOVE        R68, R64            # 14:24
0005:   LOADI       R67, 258            # 14:24
0006:   UPCALL      0, R65              # 14:1, OUT
0007:   LOADI       R65, 0              # 15:1
0008:   CALL        R65, 24             # 15:1, MODIFY_1
0009:   LOADI       R66, 1              # 16:5
0010:   LOADI       R65, 291            # 16:5
0011:   MOVE        R68, R64            # 16:23
0012:   LOADI       R67, 258            # 16:23
0013:   UPCALL      0, R65              # 16:1, OUT
0014:   LOADI       R65, 0              # 0:0
0015:   END         R65                 # 0:0

-- MODIFY_2 
0016:   ENTER       5                   # 0:0
0017:   LOADI       R64, 2              # 2:11
0018:   LOADI       R66, 2              # 3:9
0019:   LOADI       R65, 291            # 3:9
0020:   MOVE        R68, R64            # 3:28
0021:   LOADI       R67, 258            # 3:28
0022:   UPCALL      0, R65              # 3:5, OUT
0023:   RETURN                          # 4:1

-- MODIFY_1 
0024:   ENTER       5                   # 0:0
0025:   LOADI       R64, 1              # 7:11
0026:   LOADI       R66, 3              # 8:9
0027:   LOADI       R65, 291            # 8:9
0028:   MOVE        R68, R64            # 8:28
0029:   LOADI       R67, 258            # 8:28
0030:   UPCALL      0, R65              # 8:5, OUT
0031:   LOADI       R65, 0              # 9:5
0032:   CALL        R65, 16             # 9:5, MODIFY_2
0033:   LOADI       R66, 4              # 10:9
0034:   LOADI       R65, 291            # 10:9
0035:   MOVE        R68, R64            # 10:27
0036:   LOADI       R67, 258            # 10:27
0037:   UPCALL      0, R65              # 10:5, OUT
0038:   RETURN                          # 11:1
```

## Output

```plain
0=Before modify_1$ , 1=0%
0=Before modify_2$ , 1=1%
0=Inside modify_2$ , 1=2%
0=After modify_2$ , 1=1%
0=After modify_1$ , 1=0%
```

# Test: Local is not global

## Source

```basic
SUB set_local
    local_var = 8
END SUB

set_local
OUT local_var
```

## Compilation errors

```plain
6:5: Undefined global symbol local_var
```
