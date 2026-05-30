# Instructions to prepare a new release

1.  Create a local branch called `release`.

    *   **The name must be `release` to trigger required pre-release checks.**
        These checks ensure that:

        1.  `cargo publish` (detailed below) will succeed, as it is an
            irreversible operation.
        1.  `cargo install` will work for various feature combinations.
        1.   Eagerly deploy the release to staging.

    *   **Make sure the branch is synced to `origin/master`!**

        *   `git fetch`
        *   `git checkout -b release origin/master`.

1.  Create a PR to update the version number everywhere necessary.  You can
    use the `.github/workflows/update-version.sh` script to do this, but then
    make sure that following files were modified as described:

    *   `NEWS.md`: Set next version number, add date, and clean up notes.
    *   `README.md`: Update latest version number and release date.
    *   `*/Cargo.toml`: Update version number and `endbasic-*` dependencies.
    *   `Cargo.lock`: Reflects the new version number.
    *   `web/package*.json`: Update version number.
    *   `.github/workflows/deploy-release.yml`: Update tag number.

1.  Once all tests pass, merge the PR.

1.  Tag the resulting merged commit as `endbasic-X.Y.Z` and push the tag. This
    will trigger the release creation workflow.

1.  Wait for the release creation workflow to finish and then go to the
    *Releases* page to review the newly-created release draft.

1.  Push the new crates out. This is the last step because it's not reversible:

    ```
    for c in core std repl client terminal sdl st7735s rpi cli; do
        ( cd $c && cargo publish ) || break
    done
    ```
