# Abel replacement

The benchmark compares the original Abel at Mathlib `a3bcf0a3c2` with the replacement,
on Lean PR #15471 at `d1a101d`, using standard Mathlib loading without explicit native plugins.
Each workload uses four adjacent AB/BA/AB/BA pairs and three warmups per arm. All completed
samples are retained. Each run uses one automatically leased CPU on the shared host.

The initial replacement normalized both sides of an equality into displayed normal forms.
It improved larger sums and recursive normalization, but regressed several small equalities.
The revised equality tactic uses `proveAddEq?`; `abel_nf` continues to use `normalizeAdd?`.
The atom callback, coefficient evaluator, transparency settings and simplifier setup are shared.
No second polynomial engine or compatibility fallback is introduced.

| Workload | Revised/original time | Revised/original heartbeats |
| --- | ---: | ---: |
| monoid-small | 0.626 | 0.234 |
| group-subtraction | 0.483 | 0.156 |
| telescoping-8 | 0.556 | 0.344 |
| telescoping-32 | 0.623 | 0.446 |
| telescoping-64 | 0.706 | 0.650 |
| integer-coefficients-16 | 0.691 | 0.173 |
| closed-coefficient | 0.747 | 0.348 |
| integer-constants | 0.869 | 0.426 |
| symbolic-scalar-atoms | 0.398 | 0.181 |
| recursive-atoms | 0.542 | 0.371 |
| open-predicate | 0.140 | 0.140 |
| multiple-locations | 0.242 | 0.278 |

All four pairs improve for every revised workload. These are synthetic tactic measurements,
not a whole-Mathlib speedup estimate. The two runs occurred under different shared-host
conditions, so compare each implementation against its adjacent baseline rather than comparing
absolute times between runs.

The harness times saved-goal restoration and tactic evaluation, including proof construction.
For equality-tactic workloads this includes the auxiliary theorem kernel check performed by
both implementations; both return an already-checked auxiliary theorem. The `abel_nf` workloads
time target and hypothesis transformations. Input elaboration and final declaration kernel
checking are excluded from the timers. All benchmark declarations pass final kernel checking.

Each run directory contains exact measured sources (renamed to coexist in the benchmark only),
raw samples, build logs and metadata with source hashes, CPU, host load and toolchain. `run.py`
records runs under `.abel-evidence/<tag>`; it takes a tag and optional Lake configuration.
The captured configuration and CPU-lease helper use paths from the original workspace; update
those paths for reproduction elsewhere. The complete benchmark suite contains twelve workloads
and 96 timed arms per run.
