# Jacobi cancellation

A is Mathlib's original `noncomm_ring` and original Abel from `a3bcf0a3c2`.
B is the replacement `noncomm_ring` using Lean PR #15471 at `d1a101d`.
The copies differ from their production sources only in module, namespace and tactic names.
Both arms use the same Lean binary and goal, three warmups per arm, and four adjacent pairs
in AB/BA/AB/BA order. Every completed sample is retained.

| Execution mode | Original median ms/call | Replacement median ms/call | Median paired B/A |
| --- | ---: | ---: | ---: |
| Explicit native loading of both frontends | 20.64 | 18.25 | 0.884 |
| Standard Mathlib loading | 40.31 | 32.84 | 0.816 |

Each directory contains the measured source, Lake configuration, raw samples, build log,
and metadata with the CPU lease, host load, source hashes and binary hashes.
The standard-loading series has substantial shared-host variation; all four pairs improve,
and no samples were discarded. Absolute timings from different modes should not be compared.

Timing covers restoration of the goal, tactic evaluation and proof construction. It includes
kernel checking performed inside a tactic and excludes the final declaration's kernel check.
The benchmark declaration itself is kernel checked by the successful Lake build.

`run.py` records a run under `.jacobi-evidence/<tag>` and pins its process to an automatically
leased CPU using Hex's shared-host CPU lease helper. Its arguments are the output tag,
benchmark module and Lake configuration. The captured configurations contain the original
workspace's native library paths; update those paths when reproducing elsewhere.
