# Test: Singular required argument, not provided

## Source

```basic
OUT_REQUIRED_VALUE
```

## Compilation errors

```plain
1:1: OUT_REQUIRED_VALUE expected arg%
```

# Test: Singular required argument, mismatched type

## Source

```basic
OUT_REQUIRED_VALUE "Foo"
```

## Compilation errors

```plain
1:20: STRING is not a number
```

# Test: Singular required argument, correct type

## Source

```basic
OUT_REQUIRED_VALUE 4
```

## Disassembly

```asm
0000:   LOADI       R64, 4              ; 1:20
0001:   UPCALL      0, R64              ; 1:1, OUT_REQUIRED_VALUE
0002:   EOF                             ; 0:0
```

## Output

```plain
4
```

# Test: Singular required argument, type casting

## Source

```basic
OUT_REQUIRED_VALUE 7.8
```

## Disassembly

```asm
0000:   LOADC       R64, 0              ; 1:20
0001:   DTOI        R64                 ; 1:20
0002:   UPCALL      0, R64              ; 1:1, OUT_REQUIRED_VALUE
0003:   EOF                             ; 0:0
```

## Output

```plain
8
```

# Test: Singular optional argument, not provided

## Source

```basic
OUT_OPTIONAL
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:1
0001:   UPCALL      0, R64              ; 1:1, OUT_OPTIONAL
0002:   EOF                             ; 0:0
```

## Output

```plain
()
```

# Test: Singular optional argument, provided

## Source

```basic
OUT_OPTIONAL "Foo"
```

## Disassembly

```asm
0000:   LOADI       R65, 0              ; 1:14
0001:   LOADI       R64, 259            ; 1:14
0002:   UPCALL      0, R64              ; 1:1, OUT_OPTIONAL
0003:   EOF                             ; 0:0
```

## Output

```plain
Foo$
```

# Test: Singular optional argument, too many provided

## Source

```basic
OUT_OPTIONAL "Foo", "Bar"
```

## Compilation errors

```plain
1:1: OUT_OPTIONAL expected [arg$]
```

# Test: Singular argument of any type, not optional

## Source

```basic
OUT_ANY_VALUE TRUE
OUT_ANY_VALUE "Text"
```

## Disassembly

```asm
0000:   LOADI       R65, 1              ; 1:15
0001:   LOADI       R64, 256            ; 1:15
0002:   UPCALL      0, R64              ; 1:1, OUT_ANY_VALUE
0003:   LOADI       R65, 0              ; 2:15
0004:   LOADI       R64, 259            ; 2:15
0005:   UPCALL      0, R64              ; 2:1, OUT_ANY_VALUE
0006:   EOF                             ; 0:0
```

## Output

```plain
true?
Text$
```

# Test: Singular argument of any type, too many provided

## Source

```basic
OUT_ANY_VALUE TRUE, FALSE
```

## Compilation errors

```plain
1:1: OUT_ANY_VALUE expected arg
```

# Test: Singular argument of any type, optional

## Source

```basic
OUT_ANY_VALUE_OPTIONAL
OUT_ANY_VALUE_OPTIONAL TRUE
OUT_ANY_VALUE_OPTIONAL "Text"
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:1
0001:   UPCALL      0, R64              ; 1:1, OUT_ANY_VALUE_OPTIONAL
0002:   LOADI       R65, 1              ; 2:24
0003:   LOADI       R64, 256            ; 2:24
0004:   UPCALL      0, R64              ; 2:1, OUT_ANY_VALUE_OPTIONAL
0005:   LOADI       R65, 0              ; 3:24
0006:   LOADI       R64, 259            ; 3:24
0007:   UPCALL      0, R64              ; 3:1, OUT_ANY_VALUE_OPTIONAL
0008:   EOF                             ; 0:0
```

## Output

```plain
()
true?
Text$
```

# Test: Singular argument of any type, too many provided

## Source

```basic
OUT_ANY_VALUE_OPTIONAL "Text", 3
```

## Compilation errors

```plain
1:1: OUT_ANY_VALUE_OPTIONAL expected [arg]
```

# Test: Singular arguments of various kinds, with type casting

## Source

```basic
OUT_POSITIONAL 3, 5.6 AS "Foo"
OUT_POSITIONAL "A"; 4 AS "Foo"
OUT_POSITIONAL ; 0 AS 8.2
```

## Disassembly

```asm
0000:   LOADI       R65, 3              ; 1:16
0001:   LOADI       R64, 290            ; 1:16
0002:   LOADC       R66, 0              ; 1:19
0003:   DTOI        R66                 ; 1:19
0004:   LOADI       R68, 1              ; 1:26
0005:   LOADI       R67, 259            ; 1:26
0006:   UPCALL      0, R64              ; 1:1, OUT_POSITIONAL
0007:   LOADI       R65, 2              ; 2:16
0008:   LOADI       R64, 275            ; 2:16
0009:   LOADI       R66, 4              ; 2:21
0010:   LOADI       R68, 1              ; 2:26
0011:   LOADI       R67, 259            ; 2:26
0012:   UPCALL      0, R64              ; 2:1, OUT_POSITIONAL
0013:   LOADI       R64, 16             ; 3:16
0014:   LOADI       R65, 0              ; 3:18
0015:   LOADC       R67, 3              ; 3:23
0016:   LOADI       R66, 257            ; 3:23
0017:   UPCALL      0, R64              ; 3:1, OUT_POSITIONAL
0018:   EOF                             ; 0:0
```

## Output

```plain
3%
6
Foo$
A$
4
Foo$
()
0
8.2#
```

# Test: Singular arguments of various kinds, mismatched separators

## Source

```basic
OUT_POSITIONAL 3 AS 5.6 AS "Foo"
```

## Compilation errors

```plain
1:18: OUT_POSITIONAL expected [arg1] <,|;> arg2% AS arg3
```

# Test: Singular arguments of various kinds, second separator mismatched

## Source

```basic
OUT_POSITIONAL 3, 5; "Foo"
```

## Compilation errors

```plain
1:20: OUT_POSITIONAL expected [arg1] <,|;> arg2% AS arg3
```

# Test: Repeated arguments, none provided

## Source

```basic
OUT
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:1
0001:   UPCALL      0, R64              ; 1:1, OUT
0002:   EOF                             ; 0:0
```

## Output

```plain
0=()
```

# Test: Repeated arguments, several present

## Source

```basic
OUT 100, 200, 300
```

## Disassembly

```asm
0000:   LOADI       R65, 100            ; 1:5
0001:   LOADI       R64, 290            ; 1:5
0002:   LOADI       R67, 200            ; 1:10
0003:   LOADI       R66, 290            ; 1:10
0004:   LOADI       R69, 300            ; 1:15
0005:   LOADI       R68, 258            ; 1:15
0006:   UPCALL      0, R64              ; 1:1, OUT
0007:   EOF                             ; 0:0
```

## Output

```plain
0=100% , 1=200% , 2=300%
```

# Test: Repeated arguments, some missing

## Source

```basic
OUT 100, , 300,
```

## Disassembly

```asm
0000:   LOADI       R65, 100            ; 1:5
0001:   LOADI       R64, 290            ; 1:5
0002:   LOADI       R66, 32             ; 1:10
0003:   LOADI       R68, 300            ; 1:12
0004:   LOADI       R67, 290            ; 1:12
0005:   LOADI       R69, 0              ; 1:16
0006:   UPCALL      0, R64              ; 1:1, OUT
0007:   EOF                             ; 0:0
```

## Output

```plain
0=100% , 1=() , 2=300% , 3=()
```

# Test: Repeated arguments, different separators

## Source

```basic
OUT 100; 200 AS 300; 400
```

## Disassembly

```asm
0000:   LOADI       R65, 100            ; 1:5
0001:   LOADI       R64, 274            ; 1:5
0002:   LOADI       R67, 200            ; 1:10
0003:   LOADI       R66, 306            ; 1:10
0004:   LOADI       R69, 300            ; 1:17
0005:   LOADI       R68, 274            ; 1:17
0006:   LOADI       R71, 400            ; 1:22
0007:   LOADI       R70, 258            ; 1:22
0008:   UPCALL      0, R64              ; 1:1, OUT
0009:   EOF                             ; 0:0
```

## Output

```plain
0=100% ; 1=200% AS 2=300% ; 3=400%
```

# Test: Repeated arguments, different types

## Source

```basic
OUT 100, "Foo"
```

## Disassembly

```asm
0000:   LOADI       R65, 100            ; 1:5
0001:   LOADI       R64, 290            ; 1:5
0002:   LOADI       R67, 0              ; 1:10
0003:   LOADI       R66, 259            ; 1:10
0004:   UPCALL      0, R64              ; 1:1, OUT
0005:   EOF                             ; 0:0
```

## Output

```plain
0=100% , 1=Foo$
```

# Test: Singular required reference, not provided

## Source

```basic
INCREMENT_REQUIRED_INT
```

## Compilation errors

```plain
1:1: INCREMENT_REQUIRED_INT expected arg
```

# Test: Singular required reference, not a variable

## Source

```basic
INCREMENT_REQUIRED_INT 8
```

## Compilation errors

```plain
1:24: INCREMENT_REQUIRED_INT expected arg
```

# Test: Singular required reference, global variable

## Source

```basic
DIM SHARED i
i = 8
INCREMENT_REQUIRED_INT i
OUT i
```

## Disassembly

```asm
0000:   LOADI       R0, 0               ; 1:12
0001:   LOADI       R0, 8               ; 2:5
0002:   LOADRP      R64, INTEGER, R0    ; 3:24
0003:   UPCALL      0, R64              ; 3:1, INCREMENT_REQUIRED_INT
0004:   MOVE        R65, R0             ; 4:5
0005:   LOADI       R64, 258            ; 4:5
0006:   UPCALL      1, R64              ; 4:1, OUT
0007:   EOF                             ; 0:0
```

## Output

```plain
0=9%
```

# Test: Singular required reference, local variable

## Source

```basic
i = 8
INCREMENT_REQUIRED_INT i
OUT i
```

## Disassembly

```asm
0000:   LOADI       R64, 8              ; 1:5
0001:   LOADRP      R65, INTEGER, R64   ; 2:24
0002:   UPCALL      0, R65              ; 2:1, INCREMENT_REQUIRED_INT
0003:   MOVE        R66, R64            ; 3:5
0004:   LOADI       R65, 258            ; 3:5
0005:   UPCALL      1, R65              ; 3:1, OUT
0006:   EOF                             ; 0:0
```

## Output

```plain
0=9%
```

# Test: Singular required reference, variable not defined

## Source

```basic
INCREMENT_REQUIRED_INT i
OUT i
```

## Compilation errors

```plain
1:24: Undefined symbol i
```

# Test: Singular required reference, define output variable with default type

## Source

```basic
DEFINE_ARG i
OUT i
i = 1
DEFINE_ARG i
OUT i
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:12
0001:   LOADRP      R65, INTEGER, R64   ; 1:12
0002:   UPCALL      0, R65              ; 1:1, DEFINE_ARG
0003:   MOVE        R66, R64            ; 2:5
0004:   LOADI       R65, 258            ; 2:5
0005:   UPCALL      1, R65              ; 2:1, OUT
0006:   LOADI       R64, 1              ; 3:5
0007:   LOADRP      R65, INTEGER, R64   ; 4:12
0008:   UPCALL      0, R65              ; 4:1, DEFINE_ARG
0009:   MOVE        R66, R64            ; 5:5
0010:   LOADI       R65, 258            ; 5:5
0011:   UPCALL      1, R65              ; 5:1, OUT
0012:   EOF                             ; 0:0
```

## Output

```plain
0=0%
0=1%
```

# Test: Singular required reference, define output variable with explicit type

## Source

```basic
DEFINE_ARG t$
OUT t
t = "Foo"
DEFINE_ARG t
OUT t
```

## Disassembly

```asm
0000:   ALLOC       R64, STRING         ; 1:12
0001:   LOADRP      R65, STRING, R64    ; 1:12
0002:   UPCALL      0, R65              ; 1:1, DEFINE_ARG
0003:   MOVE        R66, R64            ; 2:5
0004:   LOADI       R65, 259            ; 2:5
0005:   UPCALL      1, R65              ; 2:1, OUT
0006:   LOADI       R64, 0              ; 3:5
0007:   LOADRP      R65, STRING, R64    ; 4:12
0008:   UPCALL      0, R65              ; 4:1, DEFINE_ARG
0009:   MOVE        R66, R64            ; 5:5
0010:   LOADI       R65, 259            ; 5:5
0011:   UPCALL      1, R65              ; 5:1, OUT
0012:   EOF                             ; 0:0
```

## Output

```plain
0=$
0=Foo$
```

# Test: Repeated references, define output variables

## Source

```basic
DEFINE_AND_CHANGE_ARGS b?, d#, i%, s$
OUT b, d, i, s

DEFINE_AND_CHANGE_ARGS b, d, i, s
OUT b, d, i, s
```

## Disassembly

```asm
0000:   LOADI       R64, 0              ; 1:24
0001:   LOADI       R65, 0              ; 1:28
0002:   LOADI       R66, 0              ; 1:32
0003:   ALLOC       R67, STRING         ; 1:36
0004:   LOADRP      R69, BOOLEAN, R64   ; 1:24
0005:   LOADI       R68, 544            ; 1:24
0006:   LOADRP      R71, DOUBLE, R65    ; 1:28
0007:   LOADI       R70, 544            ; 1:28
0008:   LOADRP      R73, INTEGER, R66   ; 1:32
0009:   LOADI       R72, 544            ; 1:32
0010:   LOADRP      R75, STRING, R67    ; 1:36
0011:   LOADI       R74, 512            ; 1:36
0012:   UPCALL      0, R68              ; 1:1, DEFINE_AND_CHANGE_ARGS
0013:   MOVE        R69, R64            ; 2:5
0014:   LOADI       R68, 288            ; 2:5
0015:   MOVE        R71, R65            ; 2:8
0016:   LOADI       R70, 289            ; 2:8
0017:   MOVE        R73, R66            ; 2:11
0018:   LOADI       R72, 290            ; 2:11
0019:   MOVE        R75, R67            ; 2:14
0020:   LOADI       R74, 259            ; 2:14
0021:   UPCALL      1, R68              ; 2:1, OUT
0022:   LOADRP      R69, BOOLEAN, R64   ; 4:24
0023:   LOADI       R68, 544            ; 4:24
0024:   LOADRP      R71, DOUBLE, R65    ; 4:27
0025:   LOADI       R70, 544            ; 4:27
0026:   LOADRP      R73, INTEGER, R66   ; 4:30
0027:   LOADI       R72, 544            ; 4:30
0028:   LOADRP      R75, STRING, R67    ; 4:33
0029:   LOADI       R74, 512            ; 4:33
0030:   UPCALL      0, R68              ; 4:1, DEFINE_AND_CHANGE_ARGS
0031:   MOVE        R69, R64            ; 5:5
0032:   LOADI       R68, 288            ; 5:5
0033:   MOVE        R71, R65            ; 5:8
0034:   LOADI       R70, 289            ; 5:8
0035:   MOVE        R73, R66            ; 5:11
0036:   LOADI       R72, 290            ; 5:11
0037:   MOVE        R75, R67            ; 5:14
0038:   LOADI       R74, 259            ; 5:14
0039:   UPCALL      1, R68              ; 5:1, OUT
0040:   EOF                             ; 0:0
```

## Output

```plain
0=true? , 1=0.6# , 2=1% , 3=.$
0=false? , 1=1.2# , 2=2% , 3=..$
```

# Test: Singular required reference, wrong type annotation

## Source

```basic
i$ = "hello"
INCREMENT_REQUIRED_INT i%
```

## Compilation errors

```plain
2:24: Incompatible type annotation in i% reference
```

# Test: Singular argument of any type, wrong type annotation

## Source

```basic
d# = 1.0
OUT_ANY_VALUE d?
```

## Compilation errors

```plain
2:15: Incompatible type annotation in d? reference
```

# Test: Singular argument of any type, not provided

## Source

```basic
OUT_ANY_VALUE
```

## Compilation errors

```plain
1:1: OUT_ANY_VALUE expected arg
```

# Test: Repeated arguments with require_one, none provided

## Source

```basic
DEFINE_AND_CHANGE_ARGS
```

## Compilation errors

```plain
1:1: DEFINE_AND_CHANGE_ARGS expected arg1[ <,|;> .. <,|;> argN]
```

# Test: Repeated references with require_one, value instead of ref

## Source

```basic
DEFINE_AND_CHANGE_ARGS 5
```

## Compilation errors

```plain
1:24: DEFINE_AND_CHANGE_ARGS expected arg1[ <,|;> .. <,|;> argN]
```

# Test: Repeated references with require_one, invalid first separator

## Source

```basic
DEFINE_AND_CHANGE_ARGS b AS d
```

## Compilation errors

```plain
1:26: DEFINE_AND_CHANGE_ARGS expected arg1[ <,|;> .. <,|;> argN]
```

# Test: Repeated references with require_one, invalid later separator

## Source

```basic
DEFINE_AND_CHANGE_ARGS b, d AS i
```

## Compilation errors

```plain
1:29: DEFINE_AND_CHANGE_ARGS expected arg1[ <,|;> .. <,|;> argN]
```

# Test: Repeated references with require_one, single argument

## Source

```basic
b? = TRUE
DEFINE_AND_CHANGE_ARGS b
OUT b
```

## Disassembly

```asm
0000:   LOADI       R64, 1              ; 1:6
0001:   LOADRP      R66, BOOLEAN, R64   ; 2:24
0002:   LOADI       R65, 512            ; 2:24
0003:   UPCALL      0, R65              ; 2:1, DEFINE_AND_CHANGE_ARGS
0004:   MOVE        R66, R64            ; 3:5
0005:   LOADI       R65, 256            ; 3:5
0006:   UPCALL      1, R65              ; 3:1, OUT
0007:   EOF                             ; 0:0
```

## Output

```plain
0=false?
```
