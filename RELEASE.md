# Instructions to prepare a new release

1.  Create a local branch called `release` or similar.

    *   **Make sure the branch is synced to `origin/master`!**
    *   `git fetch`
    *   `git checkout -b release origin/master`.

1.  Create PR to update:

    *   `NEWS.md`: Set next version number, add date, and clean up notes.
    *   `README.md`: Update latest version number and release date.
    *   `cli/Cargo.toml`: Update version number and `endbasic-*` dependencies.
    *   `core/Cargo.toml`: Update version number.
    *   `std/Cargo.toml`: Update version number and `endbasic-*` dependencies.
    *   `web/Cargo.toml`: Update version number and `endbasic-*` dependencies.
    *   `web/package.json`: Update version number.
    *   `.github/workflows/publish-release.yml`: Update tag number.

1.  Once all tests pass, push the new crates out:

    *   `( cd core && cargo publish )`
    *   `( cd std && cargo publish )`
    *   `( cd cli && cargo publish )`

1.  Merge the PR.

1.  Tag the new release in the repository as `release-X.Y.Z` and push the tag.

1.  Visit the *Releases* page in GitHub, create a new release for the new tag
    and paste the release notes, including the `Released on` header.

1.  Verify that the publish workflow runs for the new tag.
