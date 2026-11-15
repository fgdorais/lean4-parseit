#!/usr/bin/env python3
"""Benchmark two ParseIt revisions side by side.

Each revision is checked out in a temporary git worktree, with this benchmark package copied into
it, so the current checkout is left alone. Both revisions are built with this package's toolchain
and manifest, and they share its `.lake/packages`, so dependencies are only fetched and built once.
The benchmarks run in alternating rounds, and the report gives each case's time and allocations for
both revisions, with the change in percent.
"""

import argparse
import csv
import datetime
import platform
import shutil
import statistics
import subprocess
import sys
import tempfile
from pathlib import Path

BENCH_DIR = Path(__file__).resolve().parent
JSON_ERRORS = ("trivial", "simple")
ALL_ERRORS = ("trivial", "basic", "simple")
SUITES = ("json", "micro")


def log(msg):
    print(msg, file=sys.stderr, flush=True)


def git(*args, cwd):
    return subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True,
                          text=True).stdout.strip()


def prepare(repo, sha, wt):
    """Check out `sha` at `wt` with this benchmark package in `wt/bench`."""
    git("worktree", "add", "--detach", str(wt), sha, cwd=repo)
    bench = wt / "bench"
    shutil.rmtree(bench, ignore_errors=True)
    shutil.copytree(BENCH_DIR, bench, ignore=shutil.ignore_patterns(".lake", "__pycache__"))
    packages = BENCH_DIR / ".lake" / "packages"
    packages.mkdir(parents=True, exist_ok=True)
    (bench / ".lake").mkdir()
    (bench / ".lake" / "packages").symlink_to(packages, target_is_directory=True)
    toolchain = (BENCH_DIR / "lean-toolchain").read_text().strip()
    ref_toolchain = (wt / "lean-toolchain").read_text().strip()
    if ref_toolchain != toolchain:
        log(f"warning: {sha[:7]} uses {ref_toolchain}, building it with {toolchain}")
    return bench


def build(bench):
    r = subprocess.run(["lake", "build"], cwd=bench, capture_output=True, text=True)
    if r.returncode != 0:
        log(r.stdout + r.stderr)
        sys.exit(f"build failed in {bench}; if the manifest is stale, run `lake update` in "
                 f"{BENCH_DIR} first")


def run_json(bench, runs, errors):
    """Yield `(case, errors, us, allocs)` for the JSON suite."""
    for e in errors:
        out = subprocess.run([str(bench / ".lake/build/bin/bench"), str(runs), e,
                              "--parseit-only"], cwd=bench, check=True, capture_output=True,
                             text=True).stdout.splitlines()
        for line in out[2:]:
            records, _, us, _, allocs, _ = line.split(",")
            yield f"JSON, {int(records):,} records", e, int(us), int(allocs)


def run_micro(bench, runs, errors):
    """Yield `(case, errors, us, allocs)` for the micro suite."""
    out = subprocess.run([str(bench / ".lake/build/bin/micro"), str(runs), ",".join(errors)],
                         cwd=bench, check=True, capture_output=True, text=True).stdout
    for line in out.splitlines()[1:]:
        case, e, us, allocs = line.rsplit(",", 3)
        yield case, e, int(us), int(allocs)


def delta(a, b):
    return f"{(b - a) / a * 100:+.1f}%" if a else "n/a"


def report(args, shas, results, toolchain):
    lines = [
        f"# ParseIt benchmark: `{args.base}` against `{args.head}`",
        "",
        f"Base {args.base} {shas[0][:7]}, head {args.head} {shas[1][:7]}, toolchain "
        f"{toolchain.removeprefix('leanprover/lean4:')}, on {platform.node()}, "
        f"{datetime.date.today()}. Each time is the lower median of {args.rounds} alternating "
        f"rounds, each the median of {args.runs} runs. Allocations are small allocations per run. "
        "Changes under about 5% are usually noise.",
    ]
    for suite in args.suites:
        rows = [(k, v) for k, v in results.items() if k[0] == suite]
        if not rows:
            continue
        lines += ["", f"## {suite}", "",
                  "| case | errors | base ms | head ms | Δ time | Δ allocs |",
                  "|---|---|---:|---:|---:|---:|"]
        for (_, case, e), v in rows:
            tb, th = (statistics.median_low(t for t, _ in v[i]) for i in (0, 1))
            ab, ah = (statistics.median_low(a for _, a in v[i]) for i in (0, 1))
            lines.append(f"| {case} | {e} | {tb / 1000:.2f} | {th / 1000:.2f} | "
                         f"{delta(tb, th)} | {delta(ab, ah)} |")
    return "\n".join(lines) + "\n"


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("base", help="git revision to compare against, e.g. main")
    p.add_argument("head", help="git revision to measure, e.g. a branch")
    p.add_argument("--runs", type=int, default=11, help="runs per round (default 11)")
    p.add_argument("--rounds", type=int, default=2, help="alternating rounds (default 2)")
    p.add_argument("--suites", default=",".join(SUITES),
                   help="comma-separated suites (default json,micro)")
    p.add_argument("--errors", default=",".join(ALL_ERRORS),
                   help="comma-separated error classes (default trivial,basic,simple; "
                        "json has no basic)")
    p.add_argument("--output", type=Path, help="also write the Markdown report here")
    p.add_argument("--csv", type=Path, help="write every measurement here")
    p.add_argument("--keep", action="store_true", help="keep the worktrees")
    args = p.parse_args()
    args.suites = [s for s in args.suites.split(",") if s]
    errors = [e for e in args.errors.split(",") if e]
    for s in args.suites:
        if s not in SUITES:
            p.error(f"unknown suite {s}")
    for e in errors:
        if e not in ALL_ERRORS:
            p.error(f"unknown error class {e}")

    repo = Path(git("rev-parse", "--show-toplevel", cwd=BENCH_DIR))
    shas = [git("rev-parse", "--verify", f"{r}^{{commit}}", cwd=repo) for r in (args.base, args.head)]
    toolchain = (BENCH_DIR / "lean-toolchain").read_text().strip()
    tmp = Path(tempfile.mkdtemp(prefix="parseit-bench-"))
    worktrees = [tmp / "base", tmp / "head"]
    try:
        benches = []
        for sha, wt in zip(shas, worktrees):
            log(f"building {sha[:7]} in {wt}")
            bench = prepare(repo, sha, wt)
            build(bench)
            benches.append(bench)

        results = {}
        for r in range(args.rounds):
            order = (0, 1) if r % 2 == 0 else (1, 0)
            for i in order:
                log(f"round {r + 1}/{args.rounds}: {('base', 'head')[i]}")
                for suite in args.suites:
                    if suite == "json":
                        rows = run_json(benches[i], args.runs,
                                        [e for e in errors if e in JSON_ERRORS])
                    else:
                        rows = run_micro(benches[i], args.runs, errors)
                    for case, e, us, allocs in rows:
                        results.setdefault((suite, case, e), ([], []))[i].append((us, allocs))
    finally:
        if args.keep:
            log(f"worktrees kept in {tmp}")
        else:
            for wt in worktrees:
                if wt.exists():
                    git("worktree", "remove", "--force", str(wt), cwd=repo)
            shutil.rmtree(tmp, ignore_errors=True)

    if args.csv:
        with args.csv.open("w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["suite", "case", "errors", "revision", "round", "median_us", "allocs"])
            for (suite, case, e), v in results.items():
                for i, label in enumerate(("base", "head")):
                    for n, (us, allocs) in enumerate(v[i]):
                        w.writerow([suite, case, e, label, n + 1, us, allocs])
    text = report(args, shas, results, toolchain)
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
