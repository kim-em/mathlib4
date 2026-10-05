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
| Standard loading, including the resulting proof kernel check | 26.08 | 24.30 | 0.930 |

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

The kernel-inclusive harness checks each resulting proof with `mkAuxTheorem`. This adds
about 0.47 ms for the original tactic's auxiliary-theorem constant and 3.34 ms for the
replacement's full certificate. Its original internal auxiliary-theorem check is also timed,
as it is in normal execution. All four kernel-inclusive pairs improve. Treat this roughly
7% saving as the stronger result; the tactic-only series does not include the same final check.

The profile reconstructs the older `d81678a` module code under the current Lean binary.
On that controlled comparison, module-context setup falls from 5.125 to 0.296 ms,
operation matching from 3.690 to 2.284 ms, and the whole additive backend from 13.966 to
7.518 ms. Context canonicalization now happens only when a displayed normal form needs it;
equality proving no longer pays that cost. Repeated operation comparisons are cached per
reification. Atom lookup remains about 4.5 ms. The callback traversal, polynomial computation
and certificate construction are small by comparison. Timers are nested and inclusive;
these profile costs must not be summed or substituted for the uninstrumented measurements.

This explains the avoidable work behind the older regression without claiming to reproduce
the original shared-host sample exactly. No new production change was needed: both fixes are
already present in Lean PR #15471.
