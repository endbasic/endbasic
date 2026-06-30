# Test: Shebang is ignored

## Source

```basic
#!/usr/bin/env endbasic
OUT 1
```

## Disassembly

```asm
0000:   LOADI       R65, 1              ; 2:5
0001:   LOADI       R64, 258            ; 2:5
0002:   UPCALL      0, R64              ; 2:1, OUT
0003:   EOF                             ; 0:0
```

## Output

```plain
0=1%
```

# Test: Shebang preserves error line numbers

## Source

```basic
#!/usr/bin/env endbasic

IF THEN
```

## Compilation errors

```plain
3:4: No expression in IF statement
```
