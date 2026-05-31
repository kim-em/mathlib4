# FastDischarger notes — what's been done, what's left

Companion notes to `Mathlib/Tactic/Linarith/FastDischarger.lean`. Read this if you want to extract a smaller subset that still gives a measurable win, or to understand which past changes are load-bearing vs nice-to-have.

## What's currently delivered

`FastDischarger.lean` (~970 LoC, branch `fast-linarith-discharger`):

- Vendored `Q` type — `{ num : Int, den : Nat, den_nz : den ≠ 0 }` with `Q.toRat := Rat.normalize ...`. Kernel-friendly because `Q.add`/`Q.mul`/`Q.neg` operate on raw fields with no in-place gcd normalisation.
- Four bridging theorems: `Q.toRat_add`, `_mul`, `_neg`, `_eq_of_cross`.
- 14 walk-step lemmas (`atom_norm`, `mul_atom_norm`, `neg_atom_norm`, `take_left`, `take_right`, `combine`, `combine_zero`, `smul_cons`, `neg_cons`, four `*_congr_eq`, `sub_to_add_neg`). All proved by `subst; ring1` at module load; applied at runtime via raw `mkAppN`, never re-derived.
- `LinForm` — sorted descending by atom index.
- Cached operator Exprs (`addRatFn`, `mulRatFn`, `negRatFn`) for `mkApp2`-style construction without typeclass synthesis.
- `mkEqTransFast` — direct `Eq.trans` application, bypasses `mkEqTrans`'s `isDefEq` unification.
- `mkRatLit` / `mkQLit` — Q literal builders with cached `Nat.one_ne_zero` for the den=1 path.
- `proveRatlit{Add,Mul,Neg}` — closed-`Int` cross-multiplication leaves discharged by `Eq.refl`.
- `proveMerge` (7 sub-cases), `proveSmul`, `proveNeg`, `normalizeR` — the structured walkers.
- `precomputeSpine` — hoists suffix renderings out of the recursion (eliminates an O(n²) re-render).
- Entry point: left-fold matching `addExprs`'s left-association, with a per-row bridge for the `(c : Rat)` vs `Q.toRat ⟨c,1,_⟩` syntactic difference.

Tests: all eight `Benchmark/*Fast.lean` files pass; `MathlibTest/Linarith/Basic.lean` and `…/NNReal.lean` pass both flag-off and flag-on.

## Apples-to-apples speedup achieved (median of 5, after tree-fold)

| n | baseline | fast | total | kernel |
|---|---------:|-----:|------:|-------:|
| Size5 | 14.9 | 12.9 | 1.15× | — |
| Size10 | 18.6 | 15.4 | 1.20× | — |
| Size20 | 22.0 | 21.5 | 1.02× | — |
| Size40 | 35.1 | 32.8 | 1.07× | — |
| Size80 | 71.6 | 68.7 | 1.04× | **1.94×** |
| Coeffs | 37.2 | 31.8 | 1.16× | — |
| NonTrivial | 32.0 | 30.2 | 1.05× | — |
| RatCoeffs | 36.6 | 34.1 | 1.07× | — |

Geometric mean ~1.09× total, ~1.4× kernel (where measured). ring1 is fully bypassed on success.

### What the trace tells us about Size80 (`set_option trace.profiler true`)

With trace overhead included:
- `proveEqZeroUsing` time: **baseline 103ms → fast 35ms (2.9×)**
- Kernel `type checking`: 48ms → 25ms (1.9×)
- Total tactic execution: ~75ms in both (construction overhead absorbs the discharger savings)

The construction-side meta work (proveBalancedSum, bridgeLeftFoldToBalancedRange, normalizeR, mkApp* etc.) is competitive in total time with ring1's tactic-side polynomial normalisation. The kernel-checking advantage is real (proof term is ~2× smaller post-tree-fold), but it shows up most clearly with trace enabled, where the per-tactic stage breakdown is visible.

### Asymptotic check at n=160, n=320 (median of 3)

| n | baseline | fast | speedup |
|---|---------:|-----:|--------:|
| 80 | 72 | 68 | 1.05× |
| 160 | 188 | 185 | 1.01× |
| 320 | 601 | 600 | 1.00× |

The hoped-for asymptotic crossover did not materialise at these sizes. Both grow superlinearly at similar rates. Two interpretations:
1. **ring1 is per-op faster.** Its polynomial normalisation is highly tuned compiled code; the structured walker spends more time per Expr-construction unit even with our optimisations.
2. **The bridge cost is real.** `bridgeLeftFoldToBalancedRange` + `buildSplitProof` are O(n log n) but with non-trivial constants. At n=320 they dominate.

**Practical implication:** the structured discharger is a *correctness* win (kernel checks a smaller, more uniform proof term) but not a clear performance win at these sizes. Further work would need to either (a) reduce per-Expr-construction overhead substantially, or (b) eliminate the bridge altogether (which requires changing how linarith builds `sm`).

## Load-bearing components — do not remove these

These are necessary for **correctness**, not optimisation:

- `Q` type + bridging theorems (`Q.toRat_add` / `_mul` / `_neg` / `_eq_of_cross`).
- All 14 walk-step lemmas.
- `proveRatlit{Add,Mul,Neg}` with closed-Int cross-multiplication side conditions.
- `proveMerge` with all 7 sub-cases (in particular `combine_zero` for atom cancellation).
- The per-row "bridge" in the entry point (`buildScaledRowProof`) — handles the `(c : Rat)` ≠ `Q.toRat ⟨c,1⟩` syntactic gap.

These are necessary for **acceptable speed** (without them the structured walker is no faster than ring1):

- Cached operator Exprs (`addRatFn` etc.) — avoids per-node typeclass inference.
- `mkEqTransFast` — used everywhere in the chain.
- `precomputeSpine` — without this, proveMerge re-renders suffixes O(n²) and is *slower than ring1*.
- `den1NeZeroProof` cache — small, but every integer coefficient hits it.

## Candidate optimisations and estimates

If you want to push the speedup further, here are the candidates ranked by expected payoff. Combine with `git blame` / branch history to find the touchpoints; nothing else in the file is delicate, but the points below need careful work.

### A. Balanced tree fold instead of left-fold for the combine (DONE — modest impact)

**Implemented in commit `ee20ff7`. Updated estimate: 1.02–1.20× on benchmarks below n=80; no measurable gain above.**

The kernel-checking time drops ~2× (proof term is genuinely smaller), but the construction-side meta work (`proveBalancedSum` + `bridgeLeftFoldToBalancedRange` + `buildSplitProof`) adds back roughly the same time the discharger saved. Net wall-clock improvement is small.

If revisited, the path to a real win is either:
- Eliminate the bridge by changing `addExprs` upstream to be balanced (invasive but the bridge IS the bulk of the construction overhead post-A).
- Reduce per-Expr-construction cost (custom Expr allocator, fewer Array operations).

See `FastDischarger-TreeFold-PLAN.md` for the design and the measurement notes.

### B. Bigger benchmarks to find the asymptotic crossover

**Plausible gain: ring1's O(n²) polynomial normalisation eventually loses to our O(n log n) (post-A) discharger. At n=80 the constants nearly cancel; at n=200 or n=500 the curves should clearly separate.**

Add benchmarks at n=160, n=320, n=640. Measure crossover. Useful for:
- Demonstrating the architectural win
- Identifying real linarith problems in mathlib at that scale (some `polyrith`-shaped goals or large `linarith` chains in number theory might qualify)

Zero implementation cost beyond benchmark file generation. Do this before/alongside (A) to validate the speedup claim.

### C. External spine maintenance in the entry-point fold (SMALL)

**Plausible gain: 1.05–1.10× on Size80, marginal below.**

The accumulator's spine is recomputed inside each `proveMerge` call. After n merges, total spine recomputation is O(n²) entries built. Maintaining `accL`'s spine externally — `proveMerge` takes precomputed spines as input and returns the new accumulator's spine — would save those recomputations.

~50–100 LoC of careful work. Worth doing only after (A); without (A) the savings are dwarfed by the merge work itself.

### D. `mkRatLit` caching (SMALLEST)

**Plausible gain: 1.02–1.05× broadly.**

Common Q values recur many times: `⟨0,1⟩` for every constant slot, `⟨1,1⟩` and `⟨-1,1⟩` for atom-norm leaves, small Farkas multipliers. Cache them in an `IO.Ref (HashMap Q Expr)` initialised at the start of each discharger call.

~20 LoC. Lowest risk, lowest reward. Easy to bolt on after anything else.

### E. Inline `Q.toRat` projection in the rendered form (RISKY)

**Plausible gain: 1.05–1.15× kernel speedup IF the design works. Real risk of regression.**

Currently the rendered form is `Q.toRat (Q.mk n d p) * x + …`. The kernel reduces `Q.toRat (Q.mk n d p)` to `Rat.normalize n d p` at every check. If we emit `Rat.normalize n d p` directly, that step disappears.

But: all the bridging theorems and walk-step lemmas are stated for `q.toRat`-headed terms. Changing the rendered form requires either:
- Rewriting the lemma statements (substantial Types-section rewrite), or
- Bridging via `Eq.refl`-by-defeq at each leaf (might be free, might double the proof term)

~100–200 LoC of rewriting, uncertain payoff. Investigate only if everything else has been done and there's still a measurable kernel-checking cost in the `Q.toRat`-projection reduction.

## Minimum viable subset to reproduce current results

The current ~1.09× geometric mean comes from:
- The full lp-style structured discharger (Q type + walk-step lemmas + proveRatlit + proveMerge + proveSmul + proveNeg + normalizeR + per-row bridge in `buildScaledRowProof`)
- `precomputeSpine` (Optimisation 1)
- `mkAppN` removal in `proveRatlit` (Optimisation 2)
- Tree-fold combine (post-hoc Optimisation A, see commit `ee20ff7`)

The tree-fold (A) contributes ~0.02× of the gain. The biggest contributors are correctness of the architecture and Optimisations 1/2.

If you want to **further** push the speedup, look at (C), (D), (E) for incremental gains — none of them on their own is dramatic. Or look at the harder questions in "What's next" below.

## What's next, if you want a >1.3× speedup

The structured discharger as currently implemented is fundamentally bottlenecked by per-Expr-construction overhead on the tactic side. To meaningfully beat ring1 we'd need one of:

1. **Reduce per-Expr-construction cost.** Profile shows the construction-side work is comparable to ring1's tactic-time. Most of that is `mkApp` calls + Array operations. Investigate: custom Expr allocator? Smaller Expr representation? Lazy realisation?

2. **Eliminate the bridge entirely.** The tree-fold needs a bridge from linarith's left-folded `sm` to our balanced shape. The bridge is O(n log n) lemma applications but the construction cost has non-trivial constants. If `linarith`'s `addExprs` were balanced (or if the discharger were called *before* `addExprs` runs), no bridge is needed. Upstream change to `linarith` (`addExprs'` and `proveFalseByLinarith`) — invasive but cleanly cuts ~30% of the structured discharger's tactic time.

3. **Reflection-based checker.** Compile the certificate-checking logic into a `Decidable` instance and let the kernel run one `decide`. Completely different architecture (multi-week project) but could be a dramatic win.

Items 1 and 2 are tractable but each is a substantial engineering effort. Item 3 is out of scope per Kim's note.

## Things that are NOT worth doing

- Replacing more `mkAppM` calls. Already done in proveRatlit. Other `mkAppM` calls in the file are once-per-call (e.g., `mkAppM \`\`OfNat.ofNat` for the zero term), not hot.
- Adding a non-Rat fallback path. The fast discharger correctly returns `none` on non-Rat goals and lets `ring1` fire. Adding type-specific variants is upstream-shape work, not speedup work.
- Reflection-based checker (à la `bv_decide`). Different architecture, multi-week project, unclear payoff. Out of scope.

## How to verify any change

```bash
cd /tmp/mathlib4
lake build Mathlib.Tactic.Linarith.FastDischarger
lake build Mathlib.Tactic.Linarith.Frontend

# Correctness (default off):
lake env lean MathlibTest/Linarith/Basic.lean
lake env lean MathlibTest/Linarith/NNReal.lean

# Correctness (flag flipped on in LinarithConfig):
# (flip the default, then run the above)

# Per-benchmark speed:
for f in Size5 Size10 Size20 Size40 Size80 Coeffs NonTrivial RatCoeffs; do
  lake env lean Benchmark/${f}Fast.lean | grep "tactic execution"
done
```

Always benchmark against `linarith (config := {})`, **not** bare `linarith` — the latter is 2-3× slower for unrelated config-evaluation reasons and gives misleading "speedups".
