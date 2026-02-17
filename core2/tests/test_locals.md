# Test: DIM variable with name of a built-in callable

## Source

```basic
DIM out AS INTEGER
```

## Compilation errors

```plain
1:5: Cannot redefine out
```

# Test: DIM variable with name of a user-defined sub

## Source

```basic
SUB foo
END SUB
DIM foo AS INTEGER
```

## Compilation errors

```plain
3:5: Cannot redefine foo
```

# Test: Redefine existing scalar with DIM

## Source

```basic
DIM a AS INTEGER
DIM a AS INTEGER
```

## Compilation errors

```plain
2:5: Cannot redefine a
```

# Test: Redefine existing variable as scalar with DIM

## Source

```basic
a = 5
DIM a AS INTEGER
```

## Compilation errors

```plain
2:5: Cannot redefine a
```
