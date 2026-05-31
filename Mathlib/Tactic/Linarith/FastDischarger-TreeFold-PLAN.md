# Plan: balanced tree fold for the combine step

Goal: replace the linear left-fold of `proveMerge` calls in `FastDischarger.lean`'s entry point with a balanced binary tree fold, reducing the produced proof term from O(n²) to O(n log n) nodes. Targeted at the `combine` step that ties together the per-row `proveSmul`/`proveMerge` results into a single `sm = 0` proof.

## Context

After the current optimisations, the FastDischarger delivers ~1.08× geometric-mean speedup. The dominant remaining cost is the proof term size produced by the entry-point fold.

The current fold is left-associated to match `addExprs`'s shape:
```
accL₁ = L₀
accL₂ = merge(accL₁, L₁)   -- proof has O(2) nodes
accL₃ = merge(accL₂, L₂)   -- proof has O(3) nodes
...
accLₙ = merge(accLₙ₋₁, Lₙ₋₁)   -- proof has O(n) nodes
```
Total: O(n²) proof term nodes. Kernel checks each, so kernel time scales with this.

A balanced binary tree:
```
Level 0: n leaves
Level 1: n/2 pairwise merges of size 2
Level 2: n/4 merges of size 4
...
Level log n: 1 merge of size n
```
Total: O(n log n) proof term nodes.

For n=80: ~6400 nodes → ~560 nodes (~11× reduction). Kernel time should drop ~10× on the structured-proof portion.

## The bridge problem

`linarith` constructs `sm` by left-folded `addExprs`:
```
sm = (((mls[0] + mls[1]) + mls[2]) + … + mls[n-1])
```

Our balanced-tree merge proof has shape:
```
sm_norm = merge(merge(mls[0], mls[1]), merge(mls[2], mls[3])) + …   -- some balanced tree
```

These are propositionally equal by associativity (`Rat` is a `CommSemiring`) but **syntactically distinct**. We need a bridge proof `sm = sm_norm`.

**Key insight: the bridge cost is O(n) lemma applications, not O(n log n) or higher.** A list of `n` left-folded terms can be rebalanced into any binary tree using at most `O(n)` `add_assoc` (and possibly `add_comm`) rotations, because the additive structure is a free commutative monoid quotiented by the axioms. Each rotation produces one `Eq.trans` + one `add_assoc`/`add_comm` lemma application. The bridge is dominated by the merge proof savings.

(A standard algorithm: collect the left-fold's leaves in order, build a balanced tree bottom-up, and prove equality via a single right-pivoting walk that issues O(n) `add_assoc` applications. We do NOT need rotation-distance reasoning.)

## Critical files to modify

- `Mathlib/Tactic/Linarith/FastDischarger.lean` — replace the entry-point combine loop. Add a `proveBalancedSum` helper. Add a `bridgeLeftFoldToBalanced` helper. ~120–180 LoC change.

No other files need changes.

## Design

### Step 1: `proveBalancedSum` — the recursive balanced merger

```lean
/-- Given a slice [lo, hi) of `rowProofs`, recursively merge the
corresponding LinForms in a balanced binary tree, returning
`(L, pf, rL, lhsExpr)` where:
  - L is the merged LinForm
  - pf : lhsExpr = ⟦L⟧
  - lhsExpr is the balanced-tree-shaped Expr matching the merge structure
    (NOT linarith's left-fold)
  - rL is the rendered ⟦L⟧
For hi - lo = 1, returns the single row's data directly.
For hi - lo = 2, calls proveMerge once on the two rows.
For larger, splits in middle and recurses; combines via add_congr_eq +
proveMerge + mkEqTransFast. -/
partial def proveBalancedSum
    (atoms : Array Expr)
    (rowProofs : Array (LinForm × Expr × Expr × Expr))  -- (Lᵢ, pfᵢ, rLᵢ, mlsᵢ)
    (lo hi : Nat) :
    MetaM (LinForm × Expr × Expr × Expr) := do
  if hi == lo + 1 then
    let (L, pf, rL, mlsE) := rowProofs[lo]!
    return (L, pf, rL, mlsE)
  let mid := lo + (hi - lo) / 2
  let (L1, pf1, rL1, lhs1) ← proveBalancedSum atoms rowProofs lo mid
  let (L2, pf2, rL2, lhs2) ← proveBalancedSum atoms rowProofs mid hi
  let combinedLhs := mkRatAdd lhs1 lhs2
  let midRhs := mkRatAdd rL1 rL2
  let congPf := mkAppN (mkConst ``add_congr_eq) #[lhs1, rL1, lhs2, rL2, pf1, pf2]
  let (newL, mergePf, newRL) ← proveMerge atoms L1 L2
  let composed := mkEqTransFast ratType combinedLhs midRhs newRL congPf mergePf
  return (newL, composed, newRL, combinedLhs)
```

The output `lhsExpr` has shape `(slice_left_merge) + (slice_right_merge)` — a balanced binary tree, NOT linarith's left-fold.

### Step 2: `bridgeLeftFoldToBalanced` — convert sm's shape to ours

Given:
- `sm` — linarith's left-folded sum
- `balancedLhs` — our balanced-tree-shaped sum (output of `proveBalancedSum`)

Both contain the same `mls[i]` leaves in the same order. They differ only in parenthesisation.

The bridge proof can be built recursively by walking the balanced tree and the left-fold in parallel:

```lean
/-- Given a left-folded sum `sm = ((mls[0] + mls[1]) + …)` and a balanced
binary tree of the same leaves `balancedLhs`, produce a proof
`sm = balancedLhs` using O(n) `add_assoc` applications. -/
partial def bridgeLeftFoldToBalanced
    (sm balancedLhs : Expr) : MetaM Expr := do
  -- Walk both Exprs in parallel. Both decompose as repeated `+`. Use the
  -- structure of `balancedLhs` to guide which rotations to apply.
  -- Implementation: ring1 fallback is correct but slow; replace with
  -- explicit add_assoc chain matching tree structure.
  ...
```

For the first cut, **use `ring1` here**. The bridge IS one ring1 call but on a small expression (the renaming of parens, not the polynomial). It should be fast even from ring1 — much faster than ring1 on the original `sm = 0` goal because the goal is just associativity, not arithmetic. Measure first, then optimise if it's a bottleneck.

If `ring1` on the bridge turns out to be slow, replace with an explicit `add_assoc` chain. The structure can be derived by recursively decomposing balancedLhs:
- If `balancedLhs = l + r`, find where the split occurs in `sm`'s leaf list, recurse on each half, then issue one `add_assoc` to combine.
- Total: O(n) `add_assoc` applications.

### Step 3: rewire the entry point

Replace the current combine loop:

```lean
  -- OLD: left-fold
  let (L0, pf0, rL0, mls0) := rowProofs[0]!
  let mut accL := L0
  let mut accLhs := mls0
  let mut accRhs := rL0
  let mut accPf := pf0
  for h : i in [1:rowProofs.size] do
    let (Lᵢ, pfᵢ, rLᵢ, mlsᵢ) := rowProofs[i]!
    let newLhs := mkRatAdd accLhs mlsᵢ
    let midRhs := mkRatAdd accRhs rLᵢ
    let congPf := mkAppN (mkConst ``add_congr_eq)
      #[accLhs, accRhs, mlsᵢ, rLᵢ, accPf, pfᵢ]
    let (newL, mergePf, newRhs) ← proveMerge input.atoms accL Lᵢ
    let composed := mkEqTransFast ratType newLhs midRhs newRhs congPf mergePf
    accL := newL
    accLhs := newLhs
    accRhs := newRhs
    accPf := composed
```

with:

```lean
  -- NEW: balanced tree fold
  let (accL, balancedPf, accRhs, balancedLhs) ←
    proveBalancedSum input.atoms rowProofs 0 rowProofs.size
  -- Bridge from sm's left-fold to balancedLhs
  let bridgePf ← bridgeLeftFoldToBalanced input.sm balancedLhs
  -- Compose: sm = balancedLhs = accRhs
  let accPf := mkEqTransFast ratType input.sm balancedLhs accRhs bridgePf balancedPf
```

The closing step (`closePf : accRhs = 0` via `mkRatEqByDefeq`) is unchanged.

## Critical path

1. **Implement `proveBalancedSum`.** Verify correctness on Size5 first: the tree-folded proof of `sm_norm = 0` should compose with a hand-built bridge (or `ring1`-bridge) and pass kernel check.

2. **Implement `bridgeLeftFoldToBalanced` via `ring1`** as a first cut. This is correct and likely fast enough on the bridge sub-goal. Measure.

3. **Wire into the entry point.** Run all 8 benchmarks. Confirm correctness.

4. **Measure**: median-of-5 traces-off, both total tactic execution and kernel `type checking`. Compare with current `fast` numbers (Size5 13.1ms, …, Size80 72.1ms).

5. **If the `ring1`-bridge is slow**, replace with explicit `add_assoc` chain. (Structure: recursive walk on `balancedLhs`, parallel-decompose `sm`'s left fold, issue rotation per node.)

6. **If even with explicit bridge the speedup is below ~1.3×**, profile to see whether the savings on the merge side are showing up. The expected behaviour:
   - Kernel `type checking` drops ~5–10× on Size80 (proof term is much smaller)
   - Construction time drops modestly (the merges themselves are also smaller)
   - Bridge work adds O(n) — should be negligible

## Verification

Same as the parent NOTES — both `MathlibTest/Linarith` files pass with flag default-off and (after temporarily flipping the default) with flag on; all 8 `Benchmark/*Fast.lean` files pass; apples-to-apples timings vs `linarith (config := {})` show the speedup.

Add a coverage assertion: the fallback counter (`fastDischargerFallbackCount`) should be zero after running the whole benchmark suite with flag on.

## Risks

1. **Bridge proof term size.** If `ring1`-as-bridge expands into O(n²) of its own polynomial work, we don't win. Mitigation: replace with explicit chain if measurement shows this. The explicit chain is correct-by-construction and O(n).

2. **The `add_congr_eq` chain inside `proveBalancedSum` still grows.** Each internal node of the balanced tree applies one `add_congr_eq`. There are n−1 internal nodes total. So the OUTER chain is O(n) anyway — the savings come from the *inner* merge proofs being O(n log n) instead of O(n²).

3. **Edge cases:** n = 0 (no rows used — bail to fallback), n = 1 (single row — just use that row's proof + close), n = 2 (single merge). Handle these explicitly in `proveBalancedSum`.

4. **`mid := lo + (hi - lo) / 2` for split point** — make sure it's a balanced split, not lopsided. The expression as written gives the lower midpoint, which is fine for general balance.

5. **`proveMerge` is called n−1 times instead of n−1 times** (same count) — but each call is on smaller-on-average inputs. The merge at the root operates on two LinForms of size n/2 each, producing an O(n) proof. The two merges at level 1 each operate on LinForms of size n/4, producing O(n/2) proofs each. Etc.

   Sum: O(n) + 2·O(n/2) + 4·O(n/4) + … = O(n log n). ✓

## Out of scope (defer to a follow-up if even this doesn't deliver)

- Maintaining the accumulator spine externally across `proveBalancedSum` recursion. The internal `proveMerge` calls each precompute spines on their inputs — that's O(input size) per call, total O(n log n) across the tree. Acceptable.
- Replacing further `mkAppM` calls. None remain in the hot paths after Optimisation 2 from the parent notes.
- Bigger benchmarks. Worth doing separately — see parent notes (B) — to validate the asymptotic story.

## Expected outcome

Median-of-5 apples-to-apples after this change:

- Size5–Size20: small improvement or flat (n too small for the asymptotic win to dominate).
- Size40: ~1.2–1.4×
- Size80: ~1.5–2.0×
- Coeffs/RatCoeffs (n=40, similar shape): ~1.2–1.4×
- NonTrivial (n=20, non-trivial multipliers): ~1.2–1.5× — the per-merge work was already heavier, so the proof-term-size reduction helps more.

Geometric mean target: **≥1.3×**, ideally ≥1.4×.

If we hit ≥1.3× geometric mean here, the structured discharger is a real improvement on ring1 for typical mathlib `linarith` calls.
