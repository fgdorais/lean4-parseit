# Contributing to ParseIt

Contributions are welcome. This file describes how the project is built and tested, the coding
style, and the commit convention.

## Building and testing

ParseIt uses Lake. Build the library and run the tests with warnings treated as errors, as CI does:

```
lake build --wfail
```

Tests are `#guard` checks in the `ParseItTest` library, which is a default target, so a failing
check fails the build. Add tests for every change in behavior.

## Style

* Lines are at most 100 characters.
* Every module uses the Lean module system. Mark each declaration that belongs to the user API
  `public` individually; do not use `public section`. Everything else stays private.
* Put `variable` declarations only at the start of a namespace or a named section.
* The library has no `partial` definitions. Repetition terminates by well-founded recursion on
  `Iter.finitelyManySteps`, using the `Progress` reported by each parse.
* Prefer precise types in the API over raw strings, and existing core functionality over hand-rolled
  code.
* Every public definition has a docstring. Combinator docstrings start with the combinator
  applied to its arguments, for example "`take n p` parses exactly `n` occurrences of `p`".

## Commit convention

ParseIt follows the [Lean 4 commit convention][lean4], which is based on the AngularJS one. Pull
request titles follow the same format, since they become the commit subject when merged.

[lean4]: https://github.com/leanprover/lean4/blob/master/doc/dev/commit_convention.md

### Format

    <type>: <subject>
    <NEWLINE>
    <body>
    <NEWLINE>
    <footer>

`<type>` is one of:

- `feat`: new feature
- `fix`: bug fix
- `doc`: documentation
- `style`: formatting and naming, with no change in behavior
- `refactor`: code change that neither fixes a bug nor adds a feature
- `perf`: performance improvement
- `test`: new or changed tests
- `chore`: maintenance, such as CI, toolchain updates and licensing

`<subject>`:

- uses the imperative, present tense: "add" not "added" nor "adds"
- does not capitalize the first letter
- has no period at the end

`<body>` is optional. It uses the imperative, present tense, and explains the motivation for the
change and how it differs from the previous behavior. Wrap it at 72 columns.

`<footer>` is optional. It lists breaking changes, with migration notes, and closed issues on a
separate line prefixed with `Closes`, for example `Closes #12, #34`.

### Examples

    feat: add BitIterator for parsing BitVec

    BitIterator yields the bits of a BitVec least significant bit first,
    with a Finite proof and bit indices as HasPos positions.

    refactor: rename charCI and stringCI to charCaseInsensitive and stringCaseInsensitive

    chore: update toolchain to v4.35.0-rc4
