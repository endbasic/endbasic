# Test: Default zero values

## Source

```basic
DIM SHARED b1 AS BOOLEAN
DIM SHARED d1 AS DOUBLE
DIM SHARED i1 AS INTEGER
DIM SHARED i2
DIM SHARED s1 AS STRING

OUT b1, d1, i1, i2, s1
```

## Disassembly

```asm
0000:   LOADI       R0, 0               ; 1:12
0001:   LOADI       R1, 0               ; 2:12
0002:   LOADI       R2, 0               ; 3:12
0003:   LOADI       R3, 0               ; 4:12
0004:   ALLOC       R4, STRING          ; 5:12
0005:   MOVE        R65, R0             ; 7:5
0006:   LOADI       R64, 288            ; 7:5
0007:   MOVE        R67, R1             ; 7:9
0008:   LOADI       R66, 289            ; 7:9
0009:   MOVE        R69, R2             ; 7:13
0010:   LOADI       R68, 290            ; 7:13
0011:   MOVE        R71, R3             ; 7:17
0012:   LOADI       R70, 290            ; 7:17
0013:   MOVE        R73, R4             ; 7:21
0014:   LOADI       R72, 259            ; 7:21
0015:   UPCALL      0, R64              ; 7:1, OUT
0016:   EOF                             ; 0:0
```

## Output

```plain
0=false? , 1=0# , 2=0% , 3=0% , 4=$
```

# Test: Set global variables to explicit values

## Source

```basic
DIM SHARED b1 AS BOOLEAN
DIM SHARED d1 AS DOUBLE
DIM SHARED i1 AS INTEGER
DIM SHARED i2
DIM SHARED s1 AS STRING

b1 = TRUE
d1 = 2.3
i1 = 5
i2 = 7
s1 = "text"
OUT b1, d1, i1, i2, s1
```

## Disassembly

```asm
0000:   LOADI       R0, 0               ; 1:12
0001:   LOADI       R1, 0               ; 2:12
0002:   LOADI       R2, 0               ; 3:12
0003:   LOADI       R3, 0               ; 4:12
0004:   ALLOC       R4, STRING          ; 5:12
0005:   LOADI       R0, 1               ; 7:6
0006:   LOADC       R1, 0               ; 8:6, 2.3
0007:   LOADI       R2, 5               ; 9:6
0008:   LOADI       R3, 7               ; 10:6
0009:   LOADI       R4, 1               ; 11:6
0010:   MOVE        R65, R0             ; 12:5
0011:   LOADI       R64, 288            ; 12:5
0012:   MOVE        R67, R1             ; 12:9
0013:   LOADI       R66, 289            ; 12:9
0014:   MOVE        R69, R2             ; 12:13
0015:   LOADI       R68, 290            ; 12:13
0016:   MOVE        R71, R3             ; 12:17
0017:   LOADI       R70, 290            ; 12:17
0018:   MOVE        R73, R4             ; 12:21
0019:   LOADI       R72, 259            ; 12:21
0020:   UPCALL      0, R64              ; 12:1, OUT
0021:   EOF                             ; 0:0
```

## Output

```plain
0=true? , 1=2.3# , 2=5% , 3=7% , 4=text$
```

# Test: Global variables are accessible in functions

## Source

```basic
DIM SHARED i1

FUNCTION modify_global
    i1 = 3
    OUT "Inside after", i1
END FUNCTION

i1 = 2
OUT "Before", i1
OUT modify_global
OUT "After", i1
```

## Disassembly

```asm
0000:   LOADI       R0, 0               ; 1:12
0001:   JUMP        10                  ; 3:10

;; MODIFY_GLOBAL (BEGIN)
0002:   LOADI       R64, 0              ; 3:10
0003:   LOADI       R0, 3               ; 4:10
0004:   LOADI       R66, 0              ; 5:9
0005:   LOADI       R65, 291            ; 5:9
0006:   MOVE        R68, R0             ; 5:25
0007:   LOADI       R67, 258            ; 5:25
0008:   UPCALL      0, R65              ; 5:5, OUT
0009:   RETURN                          ; 6:1
;; MODIFY_GLOBAL (END)

0010:   LOADI       R0, 2               ; 8:6
0011:   LOADI       R65, 1              ; 9:5
0012:   LOADI       R64, 291            ; 9:5
0013:   MOVE        R67, R0             ; 9:15
0014:   LOADI       R66, 258            ; 9:15
0015:   UPCALL      0, R64              ; 9:1, OUT
0016:   CALL        R65, 2              ; 10:5, MODIFY_GLOBAL
0017:   LOADI       R64, 258            ; 10:5
0018:   UPCALL      0, R64              ; 10:1, OUT
0019:   LOADI       R65, 2              ; 11:5
0020:   LOADI       R64, 291            ; 11:5
0021:   MOVE        R67, R0             ; 11:14
0022:   LOADI       R66, 258            ; 11:14
0023:   UPCALL      0, R64              ; 11:1, OUT
0024:   EOF                             ; 0:0
```

## Output

```plain
0=Before$ , 1=2%
0=Inside after$ , 1=3%
0=0%
0=After$ , 1=3%
```

# Test: Global variables are accessible in subroutines

## Source

```basic
DIM SHARED i1

SUB modify_global
    i1 = 3
    OUT "Inside after", i1
END SUB

i1 = 2
OUT "Before", i1
modify_global
OUT "After", i1
```

## Disassembly

```asm
0000:   LOADI       R0, 0               ; 1:12
0001:   JUMP        9                   ; 3:5

;; MODIFY_GLOBAL (BEGIN)
0002:   LOADI       R0, 3               ; 4:10
0003:   LOADI       R65, 0              ; 5:9
0004:   LOADI       R64, 291            ; 5:9
0005:   MOVE        R67, R0             ; 5:25
0006:   LOADI       R66, 258            ; 5:25
0007:   UPCALL      0, R64              ; 5:5, OUT
0008:   RETURN                          ; 6:1
;; MODIFY_GLOBAL (END)

0009:   LOADI       R0, 2               ; 8:6
0010:   LOADI       R65, 1              ; 9:5
0011:   LOADI       R64, 291            ; 9:5
0012:   MOVE        R67, R0             ; 9:15
0013:   LOADI       R66, 258            ; 9:15
0014:   UPCALL      0, R64              ; 9:1, OUT
0015:   CALL        R64, 2              ; 10:1, MODIFY_GLOBAL
0016:   LOADI       R65, 2              ; 11:5
0017:   LOADI       R64, 291            ; 11:5
0018:   MOVE        R67, R0             ; 11:14
0019:   LOADI       R66, 258            ; 11:14
0020:   UPCALL      0, R64              ; 11:1, OUT
0021:   EOF                             ; 0:0
```

## Output

```plain
0=Before$ , 1=2%
0=Inside after$ , 1=3%
0=After$ , 1=3%
```

# Test: Integer to double promotion

## Source

```basic
DIM SHARED d AS DOUBLE
d = 6
OUT d
```

## Disassembly

```asm
0000:   LOADI       R0, 0               ; 1:12
0001:   LOADI       R0, 6               ; 2:5
0002:   ITOD        R0                  ; 2:5
0003:   MOVE        R65, R0             ; 3:5
0004:   LOADI       R64, 257            ; 3:5
0005:   UPCALL      0, R64              ; 3:1, OUT
0006:   EOF                             ; 0:0
```

## Output

```plain
0=6#
```

# Test: Double to integer demotion

## Source

```basic
DIM SHARED i1 AS INTEGER
DIM SHARED i2 AS INTEGER
i1 = 3.2
i2 = 3.7
OUT i1, i2
```

## Disassembly

```asm
0000:   LOADI       R0, 0               ; 1:12
0001:   LOADI       R1, 0               ; 2:12
0002:   LOADC       R0, 0               ; 3:6, 3.2
0003:   DTOI        R0                  ; 3:6
0004:   LOADC       R1, 1               ; 4:6, 3.7
0005:   DTOI        R1                  ; 4:6
0006:   MOVE        R65, R0             ; 5:5
0007:   LOADI       R64, 290            ; 5:5
0008:   MOVE        R67, R1             ; 5:9
0009:   LOADI       R66, 258            ; 5:9
0010:   UPCALL      0, R64              ; 5:1, OUT
0011:   EOF                             ; 0:0
```

## Output

```plain
0=3% , 1=4%
```

# Test: Type mismatch in global variable assignment

## Source

```basic
DIM SHARED d
d = "foo"
```

## Compilation errors

```plain
2:5: STRING is not a number
```

# Test: Redefine existing shared variable with DIM SHARED

## Source

```basic
DIM SHARED x AS INTEGER
DIM SHARED x AS INTEGER
```

## Compilation errors

```plain
2:12: Cannot redefine x
```

# Test: DIM SHARED when local variable of same name exists

## Source

```basic
FUNCTION foo
    x = 5
    DIM SHARED x
    OUT x
END FUNCTION

OUT foo
```

## Disassembly

```asm
0000:   JUMP        8                   ; 1:10

;; FOO (BEGIN)
0001:   LOADI       R64, 0              ; 1:10
0002:   LOADI       R65, 5              ; 2:9
0003:   LOADI       R0, 0               ; 3:16
0004:   MOVE        R67, R65            ; 4:9
0005:   LOADI       R66, 258            ; 4:9
0006:   UPCALL      0, R66              ; 4:5, OUT
0007:   RETURN                          ; 5:1
;; FOO (END)

0008:   CALL        R65, 1              ; 7:5, FOO
0009:   LOADI       R64, 258            ; 7:5
0010:   UPCALL      0, R64              ; 7:1, OUT
0011:   EOF                             ; 0:0
```

## Output

```plain
0=5%
0=0%
```
