# ParseIt benchmarks

Compares ParseIt's JSON validator with lean4-parser's on generated JSON documents. This is a
separate Lake package so that lean4-parser is never a dependency of ParseIt itself.

```
lake build
.lake/build/bin/bench [runs] [simple|trivial]
```

Prints CSV: median time per run in microseconds and small allocations per run (heartbeats), for
each library, using `Error.Simple`-style errors (default) or trivial errors.
