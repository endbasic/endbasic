# Generating golden files

This directory contains a bunch of `.out` files that track the golden output
of their corresponding `.bas` and `.in` test cases.  Some of these can be
inspected and written out by hand, but others are too cumbersome to manually
edit (for example, because they include terminal control sequences).

To easily update a given `.out` file, make sure that the behavior is correct by
visually inspecting and manually replicating what the test does and then do:

1.  ```text
    LINES=24 COLUMNS=80 cargo run -- --programs-dir="$(mktemp -d)" <some-test.in >some-test.out
    ```

1.  Open the generated `some-test.out` file and:

    1.  Manually replace the `1.2.3` version numbers with the `X.Y.Z` literal.

    1.  Manually replace any timestamps (such as those in the output of `DIR`
        with the `YYYY-MM-DD HH:MM` literal).

The test should now pass.
