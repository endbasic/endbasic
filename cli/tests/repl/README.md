# Generating golden files

This directory contains a bunch of `.out` files that track the golden output
of their corresponding `.bas` and `.in` test cases.  Some of these can be
inspected and written out by hand, but others are too cumbersome to manually
edit (for example, because they include terminal control sequences).

To easily update a given `.out` file, make sure that the behavior is correct by
visually inspecting and manually replicating what the test does and then do:
`./regen.sh the-file.out`.

The test should now pass.
