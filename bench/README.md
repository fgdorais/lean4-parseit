# ParseIt benchmarks

A separate Lake package, so that lean4-parser is never a dependency of ParseIt itself. It lives
only on the `benchmarks` branch, and requires ParseIt from the parent directory.

```
lake build
```

## Suites

`.lake/build/bin/bench [runs] [simple|trivial] [--parseit-only]` compares ParseIt's JSON validator
with lean4-parser's on generated JSON documents of 100 to 50,000 records, using `Error.Simple`-style
errors (default) or trivial errors. It prints CSV: the median time per run in microseconds and the
small allocations per run (heartbeats), for each library. With `--parseit-only`, lean4-parser is
skipped and its columns are 0.

`.lake/build/bin/micro [runs] [errors]` times single combinators, such as `dropMany`, `sepBy` with
the numeric parsers, `first` and `dropUntil`, with each error class in `errors`, a comma-separated
list (default `trivial,basic,simple`). It prints CSV: case, error class, median time per run in
microseconds and small allocations per run.

## Comparing two revisions

```
./compare.py main my-branch
```

checks out both revisions of ParseIt in temporary git worktrees, with this package copied into each,
so the current checkout is left alone. Both are built with this package's toolchain and manifest and
share its `.lake/packages`. The suites then run in alternating rounds, and the script prints a
Markdown table with each case's time and allocations for both revisions and the change in percent.
Each time is the lower median of the rounds, each the median of `--runs` runs.

Options:

- `--runs N` runs per round (default 11) and `--rounds N` rounds (default 2)
- `--suites json,micro` and `--errors trivial,basic,simple` to run fewer cases
- `--output FILE` also writes the report to a file, and `--csv FILE` writes every measurement
- `--keep` keeps the worktrees, which `git worktree remove` cleans up later

Changes under about 5% are usually noise. Run on an otherwise idle machine. If a build fails because
the manifest is stale, run `lake update` here first.
