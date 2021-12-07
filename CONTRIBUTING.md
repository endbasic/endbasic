# Contributing guidelines

So you want to contribute to EndBASIC?  That's great!  But first, please take a
few minutes to read this document in full.  Doing so upfront will minimize the
turnaround time required to get your changes incorporated.

## Disclaimers

*   EndBASIC is my ([jmmv](https://github.com/jmmv/)'s) personal project and is
    developed and maintained in my very limited free time.  My energy to work on
    this project comes in bursts.  Please understand that dealing with
    contributions is time-consuming and, because of the above, responses can be
    delayed.  Also please understand that, right now, some contributions may not
    be accepted if they don't align with my vision for the project (which, I
    know, should be better documented but I'll be happy to explain when
    necessary).

*   Even though EndBASIC is a side project, I want to practice and enforce sound
    engineering principles.  The project is not bound by schedules so there is
    no good reason to rush things.  That said, the project must ship often!  My
    personal choice is to always do the right thing at the individual PR level
    but evaluate and possibly tolerate known issues at release time.

*   As the primary author of the project, I will violate some of the rules
    below.  In particular, I will usually upload multiple commits in a single PR
    and rebase-merge them into the main branch once they pass testing.  This is
    an "optimization" over the "1 PR = 1 commit" guideline described below
    because I have no other code owners to do reviews for me.

## General guidelines

*   Before you start working on a large contribution---especially if there is no
    matching GitHub issue describing the feature gap---you should get in touch
    first.  Prefer to file a new issue and keep the discussion there so that
    anyone can follow.  However, if you are looking for a more informal method
    to get started, pick you favorite communication channel from [the Community
    section](https://www.endbasic.dev/community.html) of the website.
    Coordinating upfront makes it much easier to avoid frustrations later on.

*   All changes are subject to thorough code reviews and CI validation before
    they are merged.

*   I expect quality and attention to detail in every PR.  Please watch out for
    indentation inconsistencies, typos, grammar mistakes, and the like.  While
    these do not affect the functionality of your change, problems in that area
    make it difficult for me to trust that the rest of your contribution is
    correct. See the [Broken windows
    theory](https://en.wikipedia.org/wiki/Broken_windows_theory).  Because of
    this, I will welcome even the most trivial PR to address simple problems!

*   I am happy to mentor you through the review process via extensive comments,
    but I understand that this can get frustrating at some point.  If so, please
    let me know.  But see next item.

*   In general, if your PR is reasonable but only contains a few nits (e.g.
    minor style problems or typos), I reserve the right to take your PR and
    amend it with those fixes to avoid pointless round trips.  *You will
    maintain authorship, of course.*

*   Good PRs do one thing, and only one thing.  Refrain from touching
    surrounding lines "just because".  If there are nearby details that need
    fixing, please send separate PRs.

*   Any major changes should be accompanied by an entry to the `NEWS.md` file.
    The entry should be added to the section for the `X.Y.Z` pseudo-release at
    the top of the file, which is added after every major release to start
    accumulating changes.  Sentences in this file are written in the past tense.

*   Any new functions or commands must be recorded in the `NEWS.md` file, but
    also in the `README.md` file of the crate where they belong.

## Git and Pull Request workflows

*   The `master` branch is protected and cannot be pushed to directly (not even
    by me).  All contributions must go through a PR first and pass all testing.

*   Assume that "1 PR = 1 commit" in the main branch.  This is the preferred
    contribution mechanism as it helps ensure commits are focused and small.

*   To facilitate code reviews via the GitHub interface, follow these steps:

    1.  Create a new branch named after the change you intend to do under your
        personal branch of the project.  If there is a matching issue, prefer
        naming your branch `issue-N`.

    1.  Prepare a PR with a single commit in it under that branch.  It is
        perfectly fine to squash and force-push changes to *your branch* until
        you are ready to start the review process.  (In fact, it's perfectly
        fine to rewrite history in auxiliary branches until they are merged into
        `master`.  Don't believe any comments out there that say force-pushing
        is never appropriate!)

    1.  Once the PR is created, prefer to address review comments via
        incremental commits with messages like `Address review comments`, as
        this makes it possible to review incremental changes to the PR.  These
        commit messages don't matter because they will be lost once squashed.
        (Exception: if the review comments mean that you must change the PR
        significantly, squash them all and force-push the branch to get a clean
        diff from `HEAD` in GitHub.)

    1.  Once the PR is approved, it will be squash-merged into the main branch.
        The commit message that will appear on the main branch will be based on
        the summary and description of the PR---which by default are derived
        from *the first commit* of the branch *at PR creation time*.  Make sure
        to keep these clean following the guidelines below.

*   If you feel that you want to submit multiple separate commits at once and
    that those should be added to the main branch without squashing them, that's
    an option too---but this should be very, very rare.  This workflow doesn't
    play well with GitHub, makes reviewing subsequent iterations of the changes
    very difficult, and makes it very hard for me to fix small details for you.

## Commit messages

*   Follow standard Git commit message guidelines.  In particular:

    *   The first line is the summary or subject of the commit and has a maximum
        length of 50 characters, does not terminate in a period, and has to
        summarize the whole commit.  Write this line in the imperative tense,
        like `Add foo-bar` or `Fix baz`, instead of `Adding blah`, `Adds bleh`
        or `Added bloh`.

    *   The first line is followed by an empty line and then multiple free-form
        paragraphs providing details on the commit.  These should be wrapped at
        72-75 columns.

*   Make sure the verbose explanation of the commit explains the *what* and the
    *why* of the change.  The *how* is explained by the code change itself so,
    in general, you should not have to cover that.

*   If you find yourself writing sentences of the form "Also do..." or "This
    also fixes...", it probably means that your PR is too broad in scope.
    Remember to focus each PR on one semantical change.

*   Commits that address an existing issue should end with a single paragraph of
    the form `Fixes #N`.  More on this below.

*   As an example:

    ```plain
    Brief summary (max 50 columns)

    This PR does this and that.  The reason for this change is this and that
    other thing. (Keep paragraph wrapped at 72-75 columns).

    Some other paragraph with more details.

    Fixes #N.
    ```

*   GitHub is a terrible editor for commit messages and PR descriptions.  I
    strongly suggest you to compose the message of the first commit in your
    branch with Vim *before you create the PR*.  Then, when you create the PR,
    keep this message unedited in the PR summary and description.  (This will
    only work if you kept the branch to one commit as described earlier.)

*   If you don't want to believe me but believe Linus Torvalds, please see [his
    advice on this
    topic](https://github.com/torvalds/subsurface-for-dirk/blob/a48494d2fbed58c751e9b7e8fbff88582f9b2d02/README#L88).

## Handling bug tracker issues

*   Changes should cross-reference one or more issues in the bug tracker, if
    they exist.  This is particularly important for known bugs, but also applies
    to major feature improvements.

*   Unless you have a good reason to do otherwise, name your branch `issue-N`
    where `N` is the number of the issue being fixed.

*   When fixing an existing issue, add an entry of the form `Issue #X: Fixed
    blah.` to the `NEWS.md` file.  Do not worry too much about the relative
    ordering of the entries: I'll reorder them and possibly reword them too at
    the time of release to tell a cohesive story.  Similarly, don't forget to
    add `Fixes #X.` at the end of the PR description so that, when it's merged,
    GitHub links the commit to the issue and closes the issue.

*   If your PR partially addresses an issue but does not completely fix it, you
    cannot say `Fixes #X.` because that would close the issue.  Instead, say
    something like `Partially addresses #X.` to establish a link between the
    two.

## Coding style

*   This project uses `rustfmt` to enforce the style of Rust files so you should
    not have to worry about that.  Don't fight the auto-formatter even if it
    seems to be doing an ugly job.

*   The auto-formatter is not perfect though.  The only thing you should
    manually deal with are comment line lengths, which should be limited to 100
    characters.

*   Unfortunately, there is no auto-formatter (yet) for all other file types in
    the project, including Javascript, HTML, and Markdown.  For those, follow
    existing style within the file you are touching.  I strongly suggest you use
    VSCode to work on the project, as the `settings.json` file included in the
    source tree will aid you in doing the right thing.  Don't forget to install
    the recommended extensions.

*   Use proper punctuation for all sentences.  Always start comments with a
    capital letter and terminate them with a period.

*   Respect lexicographical sorting wherever possible, unless ordering matters.

*   Lines must not be over 100 characters except for in-tree Markdown documents
    (like this one) where the limit is 80.

*   No trailing whitespace.

*   Two spaces after end-of-sentence periods in documents, comments and even
    commit messages.

## Testing

*   Unit tests (those that live within the same `.rs` file where the changed
    code lives) are expected for every code change.

*   Integration tests (those under the `tests` subdirectory of a crate) are
    expected for a minority of changes.  It is hard to describe what the
    criteria are in this document.  Try to get a sense from what exists today.

*   The only exception to writing tests are changes to the web interface because
    tests in that space are already lacking.  (In other words: I won't ask you
    to fix existing deficiencies if you are already modifying a deficient part
    of the tree.)  However, if you *do* want to increase test coverage for this
    part of the codebase so that we can remove this entry, please do so!

*   Not writing a test because it's too difficult to do can be reasonable at
    times.  Note that this should be the exception, not the norm, and should be
    justified in the PR description.

*   If you add any new built-in command or function, you have to register it in
    the `help.in` file.  This helps ensure that the built-in multi-line strings
    are correctly formatted because the corresponding `help.out` allows visual
    inspection of the results.
