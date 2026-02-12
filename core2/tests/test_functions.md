# Test: Return value matches function type

## Source

```basic
FUNCTION foo$
    foo = "abc"
END FUNCTION

OUT foo$
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
0006:   LOADI       R64, 0              # 1:10
0007:   ENTER       1                   # 0:0
0008:   LOADI       R64, 1              # 2:11
0009:   RETURN                          # 3:1
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

OUT foo$
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
OUT "Return value", foo
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
0019:   LOADI       R64, 0              # 3:10
0020:   ENTER       6                   # 0:0
0021:   LOADI       R65, 20             # 4:9
0022:   LOADI       R67, 3              # 5:9
0023:   LOADI       R66, 291            # 5:9
0024:   MOVE        R69, R65            # 5:19
0025:   LOADI       R68, 258            # 5:19
0026:   UPCALL      0, R66              # 5:5, OUT
0027:   LOADI       R64, 30             # 6:11
0028:   RETURN                          # 7:1
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
    second = first
END FUNCTION

OUT second
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   CALL        R65, 13             # 10:5, SECOND
0002:   LOADI       R64, 258            # 10:5
0003:   UPCALL      0, R64              # 10:1, OUT
0004:   LOADI       R64, 0              # 0:0
0005:   END         R64                 # 0:0

-- FIRST 
0006:   LOADI       R64, 0              # 1:10
0007:   ENTER       3                   # 0:0
0008:   LOADI       R66, 0              # 2:9
0009:   LOADI       R65, 259            # 2:9
0010:   UPCALL      0, R65              # 2:5, OUT
0011:   LOADI       R64, 123            # 3:13
0012:   RETURN                          # 4:1

-- SECOND 
0013:   LOADI       R64, 0              # 6:10
0014:   ENTER       1                   # 0:0
0015:   CALL        R64, 6              # 7:14, FIRST
0016:   RETURN                          # 8:1
```

## Output

```plain
0=first$
0=123%
```

# Test: Default return value is reset

## Source

```basic
FUNCTION default_double#
END FUNCTION

FUNCTION default_integer
END FUNCTION

FUNCTION default_string$
END FUNCTION

FUNCTION do_call
    OUT 300
    OUT default_double  ' Needs to print 0.
    OUT default_integer  ' Needs to print 0.
    OUT default_string  ' Needs to print "".
END FUNCTION

OUT do_call
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   CALL        R65, 15             # 17:5, DO_CALL
0002:   LOADI       R64, 258            # 17:5
0003:   UPCALL      0, R64              # 17:1, OUT
0004:   LOADI       R64, 0              # 0:0
0005:   END         R64                 # 0:0

-- DEFAULT_DOUBLE 
0006:   LOADI       R64, 0              # 1:10
0007:   ENTER       1                   # 0:0
0008:   RETURN                          # 2:1

-- DEFAULT_INTEGER 
0009:   LOADI       R64, 0              # 4:10
0010:   ENTER       1                   # 0:0
0011:   RETURN                          # 5:1

-- DEFAULT_STRING 
0012:   LOADI       R64, 1              # 7:10
0013:   ENTER       1                   # 0:0
0014:   RETURN                          # 8:1

-- DO_CALL 
0015:   LOADI       R64, 0              # 10:10
0016:   ENTER       3                   # 0:0
0017:   LOADI       R66, 300            # 11:9
0018:   LOADI       R65, 258            # 11:9
0019:   UPCALL      0, R65              # 11:5, OUT
0020:   CALL        R66, 6              # 12:9, DEFAULT_DOUBLE
0021:   LOADI       R65, 257            # 12:9
0022:   UPCALL      0, R65              # 12:5, OUT
0023:   CALL        R66, 9              # 13:9, DEFAULT_INTEGER
0024:   LOADI       R65, 258            # 13:9
0025:   UPCALL      0, R65              # 13:5, OUT
0026:   CALL        R66, 12             # 14:9, DEFAULT_STRING
0027:   LOADI       R65, 259            # 14:9
0028:   UPCALL      0, R65              # 14:5, OUT
0029:   RETURN                          # 15:1
```

## Output

```plain
0=300%
0=0#
0=0%
0=$
0=0%
```

# Test: Local variables

## Source

```basic
FUNCTION modify_2
    var = 300
    modify_2 = 2000
    OUT "Inside modify_2", var
END FUNCTION

FUNCTION modify_1
    var = 200
    OUT "Before modify_2", var
    OUT modify_2
    OUT "After modify_2", var
    modify_1 = 1000
END FUNCTION

var = 100
OUT "Before modify_1", var
OUT modify_1
OUT "After modify_1", var
```

## Disassembly

```asm
0000:   ENTER       5                   # 0:0
0001:   LOADI       R64, 100            # 15:7
0002:   LOADI       R66, 0              # 16:5
0003:   LOADI       R65, 291            # 16:5
0004:   MOVE        R68, R64            # 16:24
0005:   LOADI       R67, 258            # 16:24
0006:   UPCALL      0, R65              # 16:1, OUT
0007:   CALL        R66, 27             # 17:5, MODIFY_1
0008:   LOADI       R65, 258            # 17:5
0009:   UPCALL      0, R65              # 17:1, OUT
0010:   LOADI       R66, 1              # 18:5
0011:   LOADI       R65, 291            # 18:5
0012:   MOVE        R68, R64            # 18:23
0013:   LOADI       R67, 258            # 18:23
0014:   UPCALL      0, R65              # 18:1, OUT
0015:   LOADI       R65, 0              # 0:0
0016:   END         R65                 # 0:0

-- MODIFY_2 
0017:   LOADI       R64, 0              # 1:10
0018:   ENTER       6                   # 0:0
0019:   LOADI       R65, 300            # 2:11
0020:   LOADI       R64, 2000           # 3:16
0021:   LOADI       R67, 2              # 4:9
0022:   LOADI       R66, 291            # 4:9
0023:   MOVE        R69, R65            # 4:28
0024:   LOADI       R68, 258            # 4:28
0025:   UPCALL      0, R66              # 4:5, OUT
0026:   RETURN                          # 5:1

-- MODIFY_1 
0027:   LOADI       R64, 0              # 7:10
0028:   ENTER       6                   # 0:0
0029:   LOADI       R65, 200            # 8:11
0030:   LOADI       R67, 3              # 9:9
0031:   LOADI       R66, 291            # 9:9
0032:   MOVE        R69, R65            # 9:28
0033:   LOADI       R68, 258            # 9:28
0034:   UPCALL      0, R66              # 9:5, OUT
0035:   CALL        R67, 17             # 10:9, MODIFY_2
0036:   LOADI       R66, 258            # 10:9
0037:   UPCALL      0, R66              # 10:5, OUT
0038:   LOADI       R67, 4              # 11:9
0039:   LOADI       R66, 291            # 11:9
0040:   MOVE        R69, R65            # 11:27
0041:   LOADI       R68, 258            # 11:27
0042:   UPCALL      0, R66              # 11:5, OUT
0043:   LOADI       R64, 1000           # 12:16
0044:   RETURN                          # 13:1
```

## Output

```plain
0=Before modify_1$ , 1=100%
0=Before modify_2$ , 1=200%
0=Inside modify_2$ , 1=300%
0=2000%
0=After modify_2$ , 1=200%
0=1000%
0=After modify_1$ , 1=100%
```

# Test: Local is not global

## Source

```basic
FUNCTION set_local
    local_var = 8
END FUNCTION

OUT set_local
OUT local_var
```

## Compilation errors

```plain
6:5: Undefined global symbol local_var
```

# Test: Argument passing

## Source

```basic
FUNCTION add(a, b)
    add = a + b
END FUNCTION

OUT add(3, 5) + add(10, 20)
```

## Disassembly

```asm
0000:   ENTER       6                   # 0:0
0001:   LOADI       R67, 3              # 5:9
0002:   LOADI       R68, 5              # 5:12
0003:   CALL        R66, 12             # 5:5, ADD
0004:   LOADI       R68, 10             # 5:21
0005:   LOADI       R69, 20             # 5:25
0006:   CALL        R67, 12             # 5:17, ADD
0007:   ADDI        R65, R66, R67       # 5:15
0008:   LOADI       R64, 258            # 5:5
0009:   UPCALL      0, R64              # 5:1, OUT
0010:   LOADI       R64, 0              # 0:0
0011:   END         R64                 # 0:0

-- ADD 
0012:   LOADI       R64, 0              # 1:10
0013:   ENTER       5                   # 0:0
0014:   MOVE        R67, R65            # 2:11
0015:   MOVE        R68, R66            # 2:15
0016:   ADDI        R64, R67, R68       # 2:13
0017:   RETURN                          # 3:1
```

## Output

```plain
0=38%
```

# Test: Argument passing with result saved to global

## Source

```basic
FUNCTION foo(i)
    foo = 42 + i
END FUNCTION

DIM SHARED ret
ret = foo(3)
OUT ret
```

## Disassembly

```asm
0000:   ENTER       2                   # 0:0
0001:   LOADI       R0, 0               # 5:12
0002:   LOADI       R65, 3              # 6:11
0003:   CALL        R64, 10             # 6:7, FOO
0004:   MOVE        R0, R64             # 6:7
0005:   MOVE        R65, R0             # 7:5
0006:   LOADI       R64, 258            # 7:5
0007:   UPCALL      0, R64              # 7:1, OUT
0008:   LOADI       R64, 0              # 0:0
0009:   END         R64                 # 0:0

-- FOO 
0010:   LOADI       R64, 0              # 1:10
0011:   ENTER       4                   # 0:0
0012:   LOADI       R66, 42             # 2:11
0013:   MOVE        R67, R65            # 2:16
0014:   ADDI        R64, R66, R67       # 2:14
0015:   RETURN                          # 3:1
```

## Output

```plain
0=45%
```

# Test: Arguments are passed by value

## Source

```basic
FUNCTION change_integer(i%)
    i = 3
END FUNCTION

FUNCTION change_string(s$)
    s = "foo"
END FUNCTION

i = 5
OUT change_integer(i)
OUT i

s = "bar"
OUT change_string(s)
OUT s
```

## Disassembly

```asm
0000:   ENTER       5                   # 0:0
0001:   LOADI       R64, 5              # 9:5
0002:   MOVE        R67, R64            # 10:20
0003:   CALL        R66, 19             # 10:5, CHANGE_INTEGER
0004:   LOADI       R65, 258            # 10:5
0005:   UPCALL      0, R65              # 10:1, OUT
0006:   MOVE        R66, R64            # 11:5
0007:   LOADI       R65, 258            # 11:5
0008:   UPCALL      0, R65              # 11:1, OUT
0009:   LOADI       R65, 0              # 13:5
0010:   MOVE        R68, R65            # 14:19
0011:   CALL        R67, 23             # 14:5, CHANGE_STRING
0012:   LOADI       R66, 258            # 14:5
0013:   UPCALL      0, R66              # 14:1, OUT
0014:   MOVE        R67, R65            # 15:5
0015:   LOADI       R66, 259            # 15:5
0016:   UPCALL      0, R66              # 15:1, OUT
0017:   LOADI       R66, 0              # 0:0
0018:   END         R66                 # 0:0

-- CHANGE_INTEGER 
0019:   LOADI       R64, 0              # 1:10
0020:   ENTER       2                   # 0:0
0021:   LOADI       R65, 3              # 2:9
0022:   RETURN                          # 3:1

-- CHANGE_STRING 
0023:   LOADI       R64, 0              # 5:10
0024:   ENTER       2                   # 0:0
0025:   LOADI       R65, 1              # 6:9
0026:   RETURN                          # 7:1
```

## Output

```plain
0=0%
0=5%
0=0%
0=bar$
```
