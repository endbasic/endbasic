# Test: 1D integer array

## Source

```basic
DIM a(3) AS INTEGER
a(0) = 10
a(1) = 20
a(2) = 30
OUT a(0), a(1), a(2)
```

## Disassembly

```asm
0000:   LOADI       R65, 3              ; 1:7
0001:   ALLOCA      R64, [1]%, R65      ; 1:5
0002:   LOADI       R65, 10             ; 2:8
0003:   LOADI       R66, 0              ; 2:3
0004:   STOREA      R64, R65, R66       ; 2:1
0005:   LOADI       R65, 20             ; 3:8
0006:   LOADI       R66, 1              ; 3:3
0007:   STOREA      R64, R65, R66       ; 3:1
0008:   LOADI       R65, 30             ; 4:8
0009:   LOADI       R66, 2              ; 4:3
0010:   STOREA      R64, R65, R66       ; 4:1
0011:   LOADI       R67, 0              ; 5:7
0012:   LOADA       R66, R64, R67       ; 5:5
0013:   LOADI       R65, 290            ; 5:5
0014:   LOADI       R69, 1              ; 5:13
0015:   LOADA       R68, R64, R69       ; 5:11
0016:   LOADI       R67, 290            ; 5:11
0017:   LOADI       R71, 2              ; 5:19
0018:   LOADA       R70, R64, R71       ; 5:17
0019:   LOADI       R69, 258            ; 5:17
0020:   UPCALL      0, R65              ; 5:1, OUT
0021:   EOF                             ; 0:0
```

## Output

```plain
0=10% , 1=20% , 2=30%
```

# Test: 2D integer array

## Source

```basic
DIM m(2, 3) AS INTEGER
m(0, 0) = 1
m(0, 1) = 2
m(0, 2) = 3
m(1, 0) = 4
m(1, 1) = 5
m(1, 2) = 6
OUT m(0, 0), m(0, 2), m(1, 1), m(1, 2)
```

## Disassembly

```asm
0000:   LOADI       R65, 2              ; 1:7
0001:   LOADI       R66, 3              ; 1:10
0002:   ALLOCA      R64, [2]%, R65      ; 1:5
0003:   LOADI       R65, 1              ; 2:11
0004:   LOADI       R66, 0              ; 2:3
0005:   LOADI       R67, 0              ; 2:6
0006:   STOREA      R64, R65, R66       ; 2:1
0007:   LOADI       R65, 2              ; 3:11
0008:   LOADI       R66, 0              ; 3:3
0009:   LOADI       R67, 1              ; 3:6
0010:   STOREA      R64, R65, R66       ; 3:1
0011:   LOADI       R65, 3              ; 4:11
0012:   LOADI       R66, 0              ; 4:3
0013:   LOADI       R67, 2              ; 4:6
0014:   STOREA      R64, R65, R66       ; 4:1
0015:   LOADI       R65, 4              ; 5:11
0016:   LOADI       R66, 1              ; 5:3
0017:   LOADI       R67, 0              ; 5:6
0018:   STOREA      R64, R65, R66       ; 5:1
0019:   LOADI       R65, 5              ; 6:11
0020:   LOADI       R66, 1              ; 6:3
0021:   LOADI       R67, 1              ; 6:6
0022:   STOREA      R64, R65, R66       ; 6:1
0023:   LOADI       R65, 6              ; 7:11
0024:   LOADI       R66, 1              ; 7:3
0025:   LOADI       R67, 2              ; 7:6
0026:   STOREA      R64, R65, R66       ; 7:1
0027:   LOADI       R67, 0              ; 8:7
0028:   LOADI       R68, 0              ; 8:10
0029:   LOADA       R66, R64, R67       ; 8:5
0030:   LOADI       R65, 290            ; 8:5
0031:   LOADI       R69, 0              ; 8:16
0032:   LOADI       R70, 2              ; 8:19
0033:   LOADA       R68, R64, R69       ; 8:14
0034:   LOADI       R67, 290            ; 8:14
0035:   LOADI       R71, 1              ; 8:25
0036:   LOADI       R72, 1              ; 8:28
0037:   LOADA       R70, R64, R71       ; 8:23
0038:   LOADI       R69, 290            ; 8:23
0039:   LOADI       R73, 1              ; 8:34
0040:   LOADI       R74, 2              ; 8:37
0041:   LOADA       R72, R64, R73       ; 8:32
0042:   LOADI       R71, 258            ; 8:32
0043:   UPCALL      0, R65              ; 8:1, OUT
0044:   EOF                             ; 0:0
```

## Output

```plain
0=1% , 1=3% , 2=5% , 3=6%
```

# Test: Boolean array

## Source

```basic
DIM flags(2) AS BOOLEAN
flags(0) = TRUE
OUT flags(0), flags(1)
```

## Disassembly

```asm
0000:   LOADI       R65, 2              ; 1:11
0001:   ALLOCA      R64, [1]?, R65      ; 1:5
0002:   LOADI       R65, 1              ; 2:12
0003:   LOADI       R66, 0              ; 2:7
0004:   STOREA      R64, R65, R66       ; 2:1
0005:   LOADI       R67, 0              ; 3:11
0006:   LOADA       R66, R64, R67       ; 3:5
0007:   LOADI       R65, 288            ; 3:5
0008:   LOADI       R69, 1              ; 3:21
0009:   LOADA       R68, R64, R69       ; 3:15
0010:   LOADI       R67, 256            ; 3:15
0011:   UPCALL      0, R65              ; 3:1, OUT
0012:   EOF                             ; 0:0
```

## Output

```plain
0=true? , 1=false?
```

# Test: Double array

## Source

```basic
DIM d(2) AS DOUBLE
d(0) = 3.14
OUT d(0), d(1)
```

## Disassembly

```asm
0000:   LOADI       R65, 2              ; 1:7
0001:   ALLOCA      R64, [1]#, R65      ; 1:5
0002:   LOADC       R65, 0              ; 2:8, 3.14
0003:   LOADI       R66, 0              ; 2:3
0004:   STOREA      R64, R65, R66       ; 2:1
0005:   LOADI       R67, 0              ; 3:7
0006:   LOADA       R66, R64, R67       ; 3:5
0007:   LOADI       R65, 289            ; 3:5
0008:   LOADI       R69, 1              ; 3:13
0009:   LOADA       R68, R64, R69       ; 3:11
0010:   LOADI       R67, 257            ; 3:11
0011:   UPCALL      0, R65              ; 3:1, OUT
0012:   EOF                             ; 0:0
```

## Output

```plain
0=3.14# , 1=0#
```

# Test: String array

## Source

```basic
DIM s(3) AS STRING
s(0) = "hello"
s(1) = "world"
OUT s(0), s(1), s(2)
```

## Disassembly

```asm
0000:   LOADI       R65, 3              ; 1:7
0001:   ALLOCA      R64, [1]$, R65      ; 1:5
0002:   LOADI       R65, 0              ; 2:8
0003:   LOADI       R66, 0              ; 2:3
0004:   STOREA      R64, R65, R66       ; 2:1
0005:   LOADI       R65, 1              ; 3:8
0006:   LOADI       R66, 1              ; 3:3
0007:   STOREA      R64, R65, R66       ; 3:1
0008:   LOADI       R67, 0              ; 4:7
0009:   LOADA       R66, R64, R67       ; 4:5
0010:   LOADI       R65, 291            ; 4:5
0011:   LOADI       R69, 1              ; 4:13
0012:   LOADA       R68, R64, R69       ; 4:11
0013:   LOADI       R67, 291            ; 4:11
0014:   LOADI       R71, 2              ; 4:19
0015:   LOADA       R70, R64, R71       ; 4:17
0016:   LOADI       R69, 259            ; 4:17
0017:   UPCALL      0, R65              ; 4:1, OUT
0018:   EOF                             ; 0:0
```

## Output

```plain
0=hello$ , 1=world$ , 2=$
```

# Test: DIM SHARED array

## Source

```basic
DIM SHARED a(2) AS INTEGER

SUB fill_array
    a(0) = 100
    a(1) = 200
END SUB

fill_array
OUT a(0), a(1)
```

## Disassembly

```asm
0000:   LOADI       R64, 2              ; 1:14
0001:   ALLOCA      R0, [1]%, R64       ; 1:12
0002:   JUMP        10                  ; 3:5

;; FILL_ARRAY (BEGIN)
0003:   LOADI       R64, 100            ; 4:12
0004:   LOADI       R65, 0              ; 4:7
0005:   STOREA      R0, R64, R65        ; 4:5
0006:   LOADI       R64, 200            ; 5:12
0007:   LOADI       R65, 1              ; 5:7
0008:   STOREA      R0, R64, R65        ; 5:5
0009:   RETURN                          ; 6:1
;; FILL_ARRAY (END)

0010:   CALL        R64, 3              ; 8:1, FILL_ARRAY
0011:   LOADI       R66, 0              ; 9:7
0012:   LOADA       R65, R0, R66        ; 9:5
0013:   LOADI       R64, 290            ; 9:5
0014:   LOADI       R68, 1              ; 9:13
0015:   LOADA       R67, R0, R68        ; 9:11
0016:   LOADI       R66, 258            ; 9:11
0017:   UPCALL      0, R64              ; 9:1, OUT
0018:   EOF                             ; 0:0
```

## Output

```plain
0=100% , 1=200%
```

# Test: Array reference with matching annotation

## Source

```basic
DIM a(3) AS INTEGER
OUT a%(1)
```

## Disassembly

```asm
0000:   LOADI       R65, 3              ; 1:7
0001:   ALLOCA      R64, [1]%, R65      ; 1:5
0002:   LOADI       R67, 1              ; 2:8
0003:   LOADA       R66, R64, R67       ; 2:5
0004:   LOADI       R65, 258            ; 2:5
0005:   UPCALL      0, R65              ; 2:1, OUT
0006:   EOF                             ; 0:0
```

## Output

```plain
0=0%
```

# Test: Array reference with bad annotation

## Source

```basic
DIM a(3) AS INTEGER
OUT a#(1)
```

## Compilation errors

```plain
2:5: Incompatible type annotation in a# reference
```

# Test: Array reference index is double and needs demotion

## Source

```basic
DIM a(4) AS INTEGER
a(2) = 99
OUT a(1.9)
```

## Disassembly

```asm
0000:   LOADI       R65, 4              ; 1:7
0001:   ALLOCA      R64, [1]%, R65      ; 1:5
0002:   LOADI       R65, 99             ; 2:8
0003:   LOADI       R66, 2              ; 2:3
0004:   STOREA      R64, R65, R66       ; 2:1
0005:   LOADC       R67, 0              ; 3:7, 1.9
0006:   DTOI        R67                 ; 3:7
0007:   LOADA       R66, R64, R67       ; 3:5
0008:   LOADI       R65, 258            ; 3:5
0009:   UPCALL      0, R65              ; 3:1, OUT
0010:   EOF                             ; 0:0
```

## Output

```plain
0=99%
```

# Test: Array reference index has bad type

## Source

```basic
DIM a(3) AS INTEGER
OUT a(FALSE)
```

## Compilation errors

```plain
2:7: BOOLEAN is not a number
```

# Test: Array reference has wrong number of dimensions

## Source

```basic
DIM a(2, 3) AS INTEGER
OUT a(1)
```

## Compilation errors

```plain
2:5: Array requires 2 subscripts but got 1
```

# Test: Undefined symbol in array-style expression

## Source

```basic
OUT foo(1)
```

## Compilation errors

```plain
1:5: Undefined symbol foo
```

# Test: Scalar used as array-style expression

## Source

```basic
a = 3
OUT a(1)
```

## Compilation errors

```plain
2:5: a is not an array nor a function
```

# Test: Array dimension too large

## Source

```basic
DIM a(1000000000000000)
```

## Compilation errors

```plain
1:7: Bad integer 1000000000000000: number too large to fit in target type
```

# Test: Array dimension is zero

## Source

```basic
DIM a(1, 0, 1)
```

## Disassembly

```asm
0000:   LOADI       R65, 1              ; 1:7
0001:   LOADI       R66, 0              ; 1:10
0002:   LOADI       R67, 1              ; 1:13
0003:   ALLOCA      R64, [3]%, R65      ; 1:5
0004:   EOF                             ; 0:0
```

## Runtime errors

```plain
1:5: Dimension 1 must be positive
```

# Test: Array dimension is negative

## Source

```basic
DIM a(1, -5, 1)
```

## Disassembly

```asm
0000:   LOADI       R65, 1              ; 1:7
0001:   LOADI       R66, 5              ; 1:11
0002:   NEGI        R66                 ; 1:10
0003:   LOADI       R67, 1              ; 1:14
0004:   ALLOCA      R64, [3]%, R65      ; 1:5
0005:   EOF                             ; 0:0
```

## Runtime errors

```plain
1:5: Dimension 1 must be positive
```

# Test: Array bounds error subscript too large

## Source

```basic
DIM a(3) AS INTEGER
a(5) = 10
```

## Disassembly

```asm
0000:   LOADI       R65, 3              ; 1:7
0001:   ALLOCA      R64, [1]%, R65      ; 1:5
0002:   LOADI       R65, 10             ; 2:8
0003:   LOADI       R66, 5              ; 2:3
0004:   STOREA      R64, R65, R66       ; 2:1
0005:   EOF                             ; 0:0
```

## Runtime errors

```plain
2:1: Subscript 5 exceeds limit of 3
```

# Test: Array index is negative

## Source

```basic
DIM a(3) AS INTEGER
a(-5) = 10
```

## Disassembly

```asm
0000:   LOADI       R65, 3              ; 1:7
0001:   ALLOCA      R64, [1]%, R65      ; 1:5
0002:   LOADI       R65, 10             ; 2:9
0003:   LOADI       R66, 5              ; 2:4
0004:   NEGI        R66                 ; 2:3
0005:   STOREA      R64, R65, R66       ; 2:1
0006:   EOF                             ; 0:0
```

## Runtime errors

```plain
2:1: Subscript -5 cannot be negative
```

# Test: Array bounds error subscript at limit

## Source

```basic
DIM a(3) AS INTEGER
OUT a(3)
```

## Disassembly

```asm
0000:   LOADI       R65, 3              ; 1:7
0001:   ALLOCA      R64, [1]%, R65      ; 1:5
0002:   LOADI       R67, 3              ; 2:7
0003:   LOADA       R66, R64, R67       ; 2:5
0004:   LOADI       R65, 258            ; 2:5
0005:   UPCALL      0, R65              ; 2:1, OUT
0006:   EOF                             ; 0:0
```

## Runtime errors

```plain
2:5: Subscript 3 exceeds limit of 3
```

# Test: Multidimensional array bounds error

## Source

```basic
DIM a(5, 100) AS INTEGER
a(10, 50) = 123
```

## Disassembly

```asm
0000:   LOADI       R65, 5              ; 1:7
0001:   LOADI       R66, 100            ; 1:10
0002:   ALLOCA      R64, [2]%, R65      ; 1:5
0003:   LOADI       R65, 123            ; 2:13
0004:   LOADI       R66, 10             ; 2:3
0005:   LOADI       R67, 50             ; 2:7
0006:   STOREA      R64, R65, R66       ; 2:1
0007:   EOF                             ; 0:0
```

## Runtime errors

```plain
2:1: Subscript 10 exceeds limit of 5
```

# Test: Default values

## Source

```basic
DIM a(3) AS INTEGER
DIM b(2) AS BOOLEAN
DIM d(2) AS DOUBLE
DIM s(2) AS STRING
OUT a(0), a(1), a(2)
OUT b(0), b(1)
OUT d(0), d(1)
OUT s(0), s(1)
```

## Disassembly

```asm
0000:   LOADI       R65, 3              ; 1:7
0001:   ALLOCA      R64, [1]%, R65      ; 1:5
0002:   LOADI       R66, 2              ; 2:7
0003:   ALLOCA      R65, [1]?, R66      ; 2:5
0004:   LOADI       R67, 2              ; 3:7
0005:   ALLOCA      R66, [1]#, R67      ; 3:5
0006:   LOADI       R68, 2              ; 4:7
0007:   ALLOCA      R67, [1]$, R68      ; 4:5
0008:   LOADI       R70, 0              ; 5:7
0009:   LOADA       R69, R64, R70       ; 5:5
0010:   LOADI       R68, 290            ; 5:5
0011:   LOADI       R72, 1              ; 5:13
0012:   LOADA       R71, R64, R72       ; 5:11
0013:   LOADI       R70, 290            ; 5:11
0014:   LOADI       R74, 2              ; 5:19
0015:   LOADA       R73, R64, R74       ; 5:17
0016:   LOADI       R72, 258            ; 5:17
0017:   UPCALL      0, R68              ; 5:1, OUT
0018:   LOADI       R70, 0              ; 6:7
0019:   LOADA       R69, R65, R70       ; 6:5
0020:   LOADI       R68, 288            ; 6:5
0021:   LOADI       R72, 1              ; 6:13
0022:   LOADA       R71, R65, R72       ; 6:11
0023:   LOADI       R70, 256            ; 6:11
0024:   UPCALL      0, R68              ; 6:1, OUT
0025:   LOADI       R70, 0              ; 7:7
0026:   LOADA       R69, R66, R70       ; 7:5
0027:   LOADI       R68, 289            ; 7:5
0028:   LOADI       R72, 1              ; 7:13
0029:   LOADA       R71, R66, R72       ; 7:11
0030:   LOADI       R70, 257            ; 7:11
0031:   UPCALL      0, R68              ; 7:1, OUT
0032:   LOADI       R70, 0              ; 8:7
0033:   LOADA       R69, R67, R70       ; 8:5
0034:   LOADI       R68, 291            ; 8:5
0035:   LOADI       R72, 1              ; 8:13
0036:   LOADA       R71, R67, R72       ; 8:11
0037:   LOADI       R70, 259            ; 8:11
0038:   UPCALL      0, R68              ; 8:1, OUT
0039:   EOF                             ; 0:0
```

## Output

```plain
0=0% , 1=0% , 2=0%
0=false? , 1=false?
0=0# , 1=0#
0=$ , 1=$
```

# Test: Multiple arrays in same scope

## Source

```basic
DIM x(2) AS INTEGER
DIM y(2) AS INTEGER
x(0) = 1
y(0) = 2
OUT x(0), y(0)
```

## Disassembly

```asm
0000:   LOADI       R65, 2              ; 1:7
0001:   ALLOCA      R64, [1]%, R65      ; 1:5
0002:   LOADI       R66, 2              ; 2:7
0003:   ALLOCA      R65, [1]%, R66      ; 2:5
0004:   LOADI       R66, 1              ; 3:8
0005:   LOADI       R67, 0              ; 3:3
0006:   STOREA      R64, R66, R67       ; 3:1
0007:   LOADI       R66, 2              ; 4:8
0008:   LOADI       R67, 0              ; 4:3
0009:   STOREA      R65, R66, R67       ; 4:1
0010:   LOADI       R68, 0              ; 5:7
0011:   LOADA       R67, R64, R68       ; 5:5
0012:   LOADI       R66, 290            ; 5:5
0013:   LOADI       R70, 0              ; 5:13
0014:   LOADA       R69, R65, R70       ; 5:11
0015:   LOADI       R68, 258            ; 5:11
0016:   UPCALL      0, R66              ; 5:1, OUT
0017:   EOF                             ; 0:0
```

## Output

```plain
0=1% , 1=2%
```

# Test: Array inside a function

## Source

```basic
FUNCTION sum%(n%)
    DIM a(3) AS INTEGER
    a(0) = 10
    a(1) = 20
    a(2) = 30
    sum = a(0) + a(1) + a(2)
END FUNCTION

OUT sum(0)
```

## Disassembly

```asm
0000:   JUMP        22                  ; 1:10

;; SUM (BEGIN)
0001:   LOADI       R64, 0              ; 1:10
0002:   LOADI       R67, 3              ; 2:11
0003:   ALLOCA      R66, [1]%, R67      ; 2:9
0004:   LOADI       R67, 10             ; 3:12
0005:   LOADI       R68, 0              ; 3:7
0006:   STOREA      R66, R67, R68       ; 3:5
0007:   LOADI       R67, 20             ; 4:12
0008:   LOADI       R68, 1              ; 4:7
0009:   STOREA      R66, R67, R68       ; 4:5
0010:   LOADI       R67, 30             ; 5:12
0011:   LOADI       R68, 2              ; 5:7
0012:   STOREA      R66, R67, R68       ; 5:5
0013:   LOADI       R67, 0              ; 6:13
0014:   LOADA       R64, R66, R67       ; 6:11
0015:   LOADI       R68, 1              ; 6:20
0016:   LOADA       R67, R66, R68       ; 6:18
0017:   ADDI        R64, R64, R67       ; 6:16
0018:   LOADI       R68, 2              ; 6:27
0019:   LOADA       R67, R66, R68       ; 6:25
0020:   ADDI        R64, R64, R67       ; 6:23
0021:   RETURN                          ; 7:1
;; SUM (END)

0022:   LOADI       R67, 0              ; 9:9
0023:   CALL        R66, 1              ; 9:5, SUM
0024:   MOVE        R65, R66            ; 9:5
0025:   LOADI       R64, 258            ; 9:5
0026:   UPCALL      0, R64              ; 9:1, OUT
0027:   EOF                             ; 0:0
```

## Output

```plain
0=60%
```

# Test: Array used as scalar in expression

## Source

```basic
DIM a(3) AS INTEGER
OUT a
```

## Compilation errors

```plain
2:5: a is an array and requires subscripts
```

# Test: Array used as scalar in assignment

## Source

```basic
DIM a(3) AS INTEGER
a = 5
```

## Compilation errors

```plain
2:1: a is an array and requires subscripts
```

# Test: Too many dimensions exceeding bytecode packing

## Source

```basic
DIM good(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15)
DIM bad(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16)
```

## Compilation errors

```plain
2:5: Array cannot have 16 dimensions
```

# Test: Too many dimensions exceeding potential u8 integer

## Source

```basic
DIM bad(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260)
```

## Compilation errors

```plain
1:5: Out of temp registers
```

# Test: DIM of name of a built-in callable

## Source

```basic
DIM out(3) AS INTEGER
```

## Compilation errors

```plain
1:5: Cannot redefine out
```

# Test: DIM of name of a user-defined sub

## Source

```basic
SUB foo
END SUB
DIM foo(3) AS INTEGER
```

## Compilation errors

```plain
3:5: Cannot redefine foo
```

# Test: Redefine existing array with DIM

## Source

```basic
DIM a(3) AS INTEGER
DIM a(3) AS INTEGER
```

## Compilation errors

```plain
2:5: Cannot redefine a
```

# Test: Redefine existing variable as array with DIM

## Source

```basic
a = 5
DIM a(3) AS INTEGER
```

## Compilation errors

```plain
2:5: Cannot redefine a
```

# Test: Redefine existing shared array with DIM SHARED

## Source

```basic
DIM SHARED a(3) AS INTEGER
DIM SHARED a(3) AS INTEGER
```

## Compilation errors

```plain
2:12: Cannot redefine a
```

# Test: Redefine existing array as scalar with DIM

## Source

```basic
DIM a(3) AS INTEGER
DIM a AS INTEGER
```

## Compilation errors

```plain
2:5: Cannot redefine a
```
