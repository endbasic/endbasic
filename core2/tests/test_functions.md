# Test: Return value matches function type

## Source

```basic
FUNCTION foo$
    foo = "abc"
END FUNCTION

OUT foo$(2)
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   CALL        R65, 6              # 5:5, FOO
0002:   LOADI       R64, 259            # 5:5
0003:   UPCALL      0, R64              # 5:1, OUT
0004:   LOADI       R64, 0              # 0:0
0005:   END         R64                 # 0:0

-- FOO 
0006:   ENTER       1                   # 0:0
0007:   LOADI       R64, 0              # 2:11
0008:   RETURN                          # 3:1
```

## Output

```plain
0=abc$
```

# Test: Type mismatch in return value

## Source

```basic
FUNCTION foo$
    foo = 3
END FUNCTION

OUT foo$(2)
```

## Compilation errors

```plain
2:11: Cannot assign value of type INTEGER to variable of type STRING
```

# Test: Elaborate execution flow

## Source

```basic
a = 10

FUNCTION foo
    a = 20
    OUT "Inside", a
    foo = 30
END FUNCTION

OUT "Before", a
OUT "Return value", foo(2)
OUT "After", a
```

## Disassembly

```asm
0000:   ENTER       5                   # 0:0
0001:   LOADI       R64, 10             # 1:5
0002:   LOADI       R66, 0              # 9:5
0003:   LOADI       R65, 291            # 9:5
0004:   MOVE        R68, R64            # 9:15
0005:   LOADI       R67, 258            # 9:15
0006:   UPCALL      0, R65              # 9:1, OUT
0007:   LOADI       R66, 1              # 10:5
0008:   LOADI       R65, 291            # 10:5
0009:   CALL        R68, 19             # 10:21, FOO
0010:   LOADI       R67, 258            # 10:21
0011:   UPCALL      0, R65              # 10:1, OUT
0012:   LOADI       R66, 2              # 11:5
0013:   LOADI       R65, 291            # 11:5
0014:   MOVE        R68, R64            # 11:14
0015:   LOADI       R67, 258            # 11:14
0016:   UPCALL      0, R65              # 11:1, OUT
0017:   LOADI       R65, 0              # 0:0
0018:   END         R65                 # 0:0

-- FOO 
0019:   ENTER       6                   # 0:0
0020:   LOADI       R65, 20             # 4:9
0021:   LOADI       R67, 3              # 5:9
0022:   LOADI       R66, 291            # 5:9
0023:   MOVE        R69, R65            # 5:19
0024:   LOADI       R68, 258            # 5:19
0025:   UPCALL      0, R66              # 5:5, OUT
0026:   LOADI       R64, 30             # 6:11
0027:   RETURN                          # 7:1
```

## Output

```plain
0=Before$ , 1=10%
0=Inside$ , 1=20%
0=Return value$ , 1=30%
0=After$ , 1=10%
```

# Test: Function call requires jumping backwards

## Source

```basic
FUNCTION first
    OUT "first"
    first = 123
END FUNCTION

FUNCTION second
    second = first(0)
END FUNCTION

OUT second(0)
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   CALL        R65, 12             # 10:5, SECOND
0002:   LOADI       R64, 258            # 10:5
0003:   UPCALL      0, R64              # 10:1, OUT
0004:   LOADI       R64, 0              # 0:0
0005:   END         R64                 # 0:0

-- FIRST 
0006:   ENTER       3                   # 0:0
0007:   LOADI       R66, 0              # 2:9
0008:   LOADI       R65, 259            # 2:9
0009:   UPCALL      0, R65              # 2:5, OUT
0010:   LOADI       R64, 123            # 3:13
0011:   RETURN                          # 4:1

-- SECOND 
0012:   ENTER       1                   # 0:0
0013:   CALL        R64, 6              # 7:14, FIRST
0014:   RETURN                          # 8:1
```

## Output

```plain
0=first$
0=123%
```

# Test: Local variables

## Source

```basic
FUNCTION modify_2
    var = 2
    OUT "Inside modify_2", var
END FUNCTION

FUNCTION modify_1
    var = 1
    OUT "Before modify_2", var
    OUT modify_2(2)
    OUT "After modify_2", var
END FUNCTION

var = 0
OUT "Before modify_1", var
OUT modify_1(2)
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
0007:   CALL        R66, 25             # 15:5, MODIFY_1
0008:   LOADI       R65, 258            # 15:5
0009:   UPCALL      0, R65              # 15:1, OUT
0010:   LOADI       R66, 1              # 16:5
0011:   LOADI       R65, 291            # 16:5
0012:   MOVE        R68, R64            # 16:23
0013:   LOADI       R67, 258            # 16:23
0014:   UPCALL      0, R65              # 16:1, OUT
0015:   LOADI       R65, 0              # 0:0
0016:   END         R65                 # 0:0

-- MODIFY_2 
0017:   ENTER       6                   # 0:0
0018:   LOADI       R65, 2              # 2:11
0019:   LOADI       R67, 2              # 3:9
0020:   LOADI       R66, 291            # 3:9
0021:   MOVE        R69, R65            # 3:28
0022:   LOADI       R68, 258            # 3:28
0023:   UPCALL      0, R66              # 3:5, OUT
0024:   RETURN                          # 4:1

-- MODIFY_1 
0025:   ENTER       6                   # 0:0
0026:   LOADI       R65, 1              # 7:11
0027:   LOADI       R67, 3              # 8:9
0028:   LOADI       R66, 291            # 8:9
0029:   MOVE        R69, R65            # 8:28
0030:   LOADI       R68, 258            # 8:28
0031:   UPCALL      0, R66              # 8:5, OUT
0032:   CALL        R67, 17             # 9:9, MODIFY_2
0033:   LOADI       R66, 258            # 9:9
0034:   UPCALL      0, R66              # 9:5, OUT
0035:   LOADI       R67, 4              # 10:9
0036:   LOADI       R66, 291            # 10:9
0037:   MOVE        R69, R65            # 10:27
0038:   LOADI       R68, 258            # 10:27
0039:   UPCALL      0, R66              # 10:5, OUT
0040:   RETURN                          # 11:1
```

## Output

```plain
0=Before modify_1$ , 1=0%
0=Before modify_2$ , 1=1%
0=Inside modify_2$ , 1=2%
0=0%
0=After modify_2$ , 1=1%
0=0%
0=After modify_1$ , 1=0%
```

# Test: Local is not global

## Source

```basic
FUNCTION set_local
    local_var = 8
END FUNCTION

OUT set_local(2)
OUT local_var
```

## Compilation errors

```plain
6:5: Undefined global symbol local_var
```
