/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.GroupTheory.Nilpotent

/-!
# Fitting's theorem

This file proves Fitting's theorem about nilpotent normal subgroups.

## Main results

* `Subgroup.lowerCentralSeries_sup_eq_bot`: The key technical lemma stating that if
  `lowerCentralSeries M (m + 1) = ⊥` and `lowerCentralSeries N (n + 1) = ⊥`, then
  `lowerCentralSeries (M ⊔ N) (m + n + 1) = ⊥`.
* `Subgroup.isNilpotent_sup`: If `M` and `N` are nilpotent normal subgroups of `G`,
  then their supremum `M ⊔ N` is also nilpotent.
* `Subgroup.nilpotencyClass_sup_le`: If `M` has nilpotency class `m` and `N` has
  nilpotency class `n`, then `M ⊔ N` has nilpotency class at most `m + n`.

## References

* [Wikipedia, Fitting's theorem](https://en.wikipedia.org/wiki/Fitting%27s_theorem)

-/

open Subgroup Group

variable {G : Type*} [Group G]

namespace Subgroup

/-- **Fitting's theorem** (explicit bound): If `lowerCentralSeries M m = ⊥` and
`lowerCentralSeries N n = ⊥`, then `lowerCentralSeries (M ⊔ N) (m + n) = ⊥`.

This is the key technical lemma from which both `isNilpotent_sup` and `nilpotencyClass_sup_le`
follow as immediate corollaries.

## Proof Sketch

**Step 1**: By hypothesis, `lowerCentralSeries M m = ⊥` and `lowerCentralSeries N n = ⊥`.

**Step 2**: We need to show `lowerCentralSeries (M ⊔ N) (m + n) = ⊥`. This means showing
every element in this subgroup is the identity.

**Step 3**: Expand `lowerCentralSeries (M ⊔ N) (m + n)` as an (m+n)-fold nested commutator
`⁅M ⊔ N, ⁅M ⊔ N, ⁅..., ⊤⁆...⁆⁆`. Using distributivity of commutators over suprema (since M and N
are normal), this can be written as a supremum of (m+n)-fold commutators where each position
is occupied by either `M` or `N`.

**Step 4**: For any such commutator, by pigeonhole principle, either `M` appears at least `m`
times or `N` appears at least `n` times.

**Step 5**: Key lemma needed: If `lowerCentralSeries M k = ⊥` and `H` is any subgroup, then
iterated commutators `⁅M, ⁅M, ⁅..., ⁅M, H⁆...⁆⁆⁆` (with M appearing k times) equals `⊥`.
This follows from the fact that `lowerCentralSeries M` is preserved under commutators with
normal subgroups.

**Step 6**: Applying Step 5, any commutator with M appearing ≥m times or N appearing ≥n
times must equal `⊥`.

**Step 7**: Since all commutators in the expansion are `⊥`, the entire supremum is `⊥`. -/
theorem lowerCentralSeries_sup_eq_bot (M N : Subgroup G) [M.Normal] [N.Normal]
    (m n : ℕ) (hM : lowerCentralSeries M m = ⊥) (hN : lowerCentralSeries N n = ⊥) :
    lowerCentralSeries (M ⊔ N : Subgroup G) (m + n) = ⊥ := by
  sorry

/-- **Fitting's theorem**: The supremum of two nilpotent normal subgroups is nilpotent.

In group theory, when `M` and `N` are normal subgroups, their supremum `M ⊔ N` equals their
product `{mn | m ∈ M, n ∈ N}`, which is also a normal subgroup. This theorem states that
if both `M` and `N` are nilpotent, then so is their product.

## Proof Sketch

By the definition of `IsNilpotent`, there exist `m` and `n` such that
`lowerCentralSeries M m = ⊥` and `lowerCentralSeries N n = ⊥`. We can take
`m = nilpotencyClass M` and `n = nilpotencyClass N` by `lowerCentralSeries_nilpotencyClass`.
Then `lowerCentralSeries_sup_eq_bot` gives us that
`lowerCentralSeries (M ⊔ N) (nilpotencyClass M + nilpotencyClass N) = ⊥`, which by
`nilpotent_iff_lowerCentralSeries` shows that `M ⊔ N` is nilpotent. -/
instance isNilpotent_sup (M N : Subgroup G) [M.Normal] [N.Normal]
    [IsNilpotent M] [IsNilpotent N] : IsNilpotent (M ⊔ N : Subgroup G) := by
  rw [nilpotent_iff_lowerCentralSeries]
  use nilpotencyClass M + nilpotencyClass N
  apply lowerCentralSeries_sup_eq_bot
  · rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
  · rw [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]

/-- **Fitting's theorem** with nilpotency class bound: If `M` has nilpotency class `m` and `N`
has nilpotency class `n`, then `M ⊔ N` has nilpotency class at most `m + n`.

## Proof Sketch

This follows directly from `lowerCentralSeries_sup_eq_bot`:
- Let `m = nilpotencyClass M` and `n = nilpotencyClass N`.
- By `lowerCentralSeries_nilpotencyClass`, we have
  `lowerCentralSeries M m = ⊥` and `lowerCentralSeries N n = ⊥`.
- By `lowerCentralSeries_sup_eq_bot`, we have `lowerCentralSeries (M ⊔ N) (m + n) = ⊥`.
- Therefore, by `lowerCentralSeries_eq_bot_iff_nilpotencyClass_le`, we have
  `Group.nilpotencyClass (M ⊔ N) ≤ m + n`.

Note: The bound is sharp in many cases. For example, when `M` and `N` generate a direct
product, the nilpotency class of `M ⊔ N` is exactly `max(m, n)` by `nilpotencyClass_prod`,
but in general the class can be as large as `m + n`. -/
theorem nilpotencyClass_sup_le (M N : Subgroup G) [M.Normal] [N.Normal]
    [IsNilpotent M] [IsNilpotent N] :
    nilpotencyClass (M ⊔ N : Subgroup G) ≤
      nilpotencyClass M + nilpotencyClass N := by
  rw [← lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
  have h := lowerCentralSeries_sup_eq_bot M N (nilpotencyClass M) (nilpotencyClass N)
  simp only [lowerCentralSeries_eq_bot_iff_nilpotencyClass_le] at h
  have h' := h (by omega) (by omega)
  exact lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr h'

end Subgroup
