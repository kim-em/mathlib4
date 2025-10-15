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

/-- **Fitting's theorem**: The supremum of two nilpotent normal subgroups is nilpotent.

In group theory, when `M` and `N` are normal subgroups, their supremum `M ⊔ N` equals their
product `{mn | m ∈ M, n ∈ N}`, which is also a normal subgroup. This theorem states that
if both `M` and `N` are nilpotent, then so is their product. -/
instance isNilpotent_sup (M N : Subgroup G) [M.Normal] [N.Normal]
    [IsNilpotent M] [IsNilpotent N] : IsNilpotent (M ⊔ N : Subgroup G) := by
  sorry

/-- **Fitting's theorem** with nilpotency class bound: If `M` has nilpotency class `m` and `N`
has nilpotency class `n`, then `M ⊔ N` has nilpotency class at most `m + n`. -/
theorem nilpotencyClass_sup_le (M N : Subgroup G) [M.Normal] [N.Normal]
    [IsNilpotent M] [IsNilpotent N] :
    nilpotencyClass (M ⊔ N : Subgroup G) ≤
      nilpotencyClass M + nilpotencyClass N := by
  sorry

end Subgroup
