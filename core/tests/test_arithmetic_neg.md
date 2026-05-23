# Test: Immediate double

## Source

```basic
OUT -3.5
```

## Disassembly

```asm
0000:   LOADC       R65, 0              ; 1:6, 3.5
0001:   NEGD        R65                 ; 1:5
0002:   LOADI       R64, 257            ; 1:5
0003:   UPCALL      0, R64              ; 1:1, OUT
0004:   EOF                             ; 0:0
```

## Output

```plain
0=-3.5#
```

# Test: Immediate integer

## Source

```basic
OUT -7
```

## Disassembly

```asm
0000:   LOADI       R65, 7              ; 1:6
0001:   NEGI        R65                 ; 1:5
0002:   LOADI       R64, 258            ; 1:5
0003:   UPCALL      0, R64              ; 1:1, OUT
0004:   EOF                             ; 0:0
```

## Output

```plain
0=-7%
```

# Test: Zero

## Source

```basic
OUT -0
```

## Disassembly

```asm
0000:   LOADI       R65, 0              ; 1:6
0001:   NEGI        R65                 ; 1:5
0002:   LOADI       R64, 258            ; 1:5
0003:   UPCALL      0, R64              ; 1:1, OUT
0004:   EOF                             ; 0:0
```

## Output

```plain
0=0%
```

# Test: Non-numeric type

## Source

```basic
OUT -"hello"
```

## Compilation errors

```plain
1:5: STRING is not a number
```

# Test: Integer overflow

## Source

```basic
a = -(&x80000000)
```

## Disassembly

```asm
0000:   LOADC       R64, 0              ; 1:7, -2147483648
0001:   NEGI        R64                 ; 1:5
0002:   EOF                             ; 0:0
```

## Runtime errors

```plain
1:5: Integer overflow
```
