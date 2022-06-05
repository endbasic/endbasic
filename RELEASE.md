# Instructions to prepare a new release

1.  Create a local branch called `release`.

    *   **The name must be `release` to trigger required pre-release checks.**
        These checks ensure that: `cargo publish` (detailed below) will succeed,
        as it is an irreversible operation; that `cargo install` will work
        for various feature combinations; and eagerly deploy the release to
        staging.
    *   **Make sure the branch is synced to `origin/master`!**
    *   `git fetch`
    *   `git checkout -b release origin/master`.

1.  Create a PR to update:

    *   `NEWS.md`: Set next version number, add date, and clean up notes.
    *   `README.md`: Update latest version number and release date.
    *   `*/Cargo.toml`: Update version number and `endbasic-*` dependencies.
    *   `web/package*.json`: Update version number.
    *   `.github/workflows/deploy-release.yml`: Update tag number.

    The `.github/workflows/update-version.sh` script should prepare a PR with
    all of the required changes. Don't forget to clean up the release notes
    though.

1.  Once all tests pass, merge the PR.

1.  Tag the resulting merged commit as `endbasic-X.Y.Z` and push the tag. This
    will trigger the release creation workflow.

1.  Wait for the release creation workflow to finish and then go to the
    *Releases* page to review the newly-created release draft.

1.  Push the new crates out. This is the last step because it's not reversible:

    *   `( cd core && cargo publish )`
    *   `( cd std && cargo publish )`
    *   `( cd repl && cargo publish )`
    *   `( cd client && cargo publish )`
    *   `( cd terminal && cargo publish )`
    *   `( cd sdl && cargo publish )`
    *   `( cd rpi && cargo publish )`
    *   `( cd cli && cargo publish )`
