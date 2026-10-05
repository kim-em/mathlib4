/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Kim Morrison, Oliver Nash
-/
module

public import Mathlib.Algebra.Group.Action.Defs  -- shake: keep (metaprogram output dependency)
public import JacobiOldAbel

/-! # The `jacobi_old_noncomm_ring` tactic

Solve goals in not necessarily commutative rings.

This tactic is rudimentary, but useful for solving simple goals in noncommutative rings. One
glaring flaw is that numeric powers are unfolded entirely with `pow_succ` and can easily exceed the
maximum recursion depth.

`jacobi_old_noncomm_ring` is just a `simp only [some lemmas]` followed by `jacobi_old_abel`. It automatically uses `jacobi_old_abel1`
to close the goal, and if that doesn't succeed, defaults to `jacobi_old_abel_nf`.
-/

public meta section

namespace Mathlib.Tactic.JacobiOldNoncommRing

section nat_lit_mul
variable {R : Type*} [NonAssocSemiring R] (r : R) (n : ℕ)

lemma nat_lit_mul_eq_nsmul [n.AtLeastTwo] : ofNat(n) * r = OfNat.ofNat n • r := by
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
lemma mul_nat_lit_eq_nsmul [n.AtLeastTwo] : r * ofNat(n) = OfNat.ofNat n • r := by
  simp only [nsmul_eq_mul', Nat.cast_ofNat]

end nat_lit_mul

open Lean.Parser.Tactic
/-- `jacobi_old_noncomm_ring` simplifies expressions in not-necessarily-commutative rings in the main goal
then tries closing it by "cheap" (reducible) `rfl`.
This tactic supports the operators `+`, `*`, `-`, `^` and `•` (for scalar multiplication by
natural numbers or integers).

If the ring is commutative, prefer the `ring` tactic instead, which is more powerful and efficient.
The tactic is implemented as a combination of `simp only [...]` and `jacobi_old_abel`. The precise invocation
of `simp only` can be customized using the options listed below.

Limitation: numeric powers are unfolded entirely with `pow_succ` and can easily exceed the
maximum recursion depth.

* `jacobi_old_noncomm_ring [h]` adds the term `h` as simplification lemma, rewriting from left to right.
  Multiple arguments can be combined as `jacobi_old_noncomm_ring [h₁, ..., hₙ]`.
* `jacobi_old_noncomm_ring [← h]` adds the term `h` as simplification lemma, rewriting from right to left.
* `jacobi_old_noncomm_ring [*]` simplifies using all hypotheses in the local context.
* `jacobi_old_noncomm_ring (config := cfg)` uses `cfg` as configuration for the simplification step.
  See `Lean.Meta.Simp.Config` for more details.
* `jacobi_old_noncomm_ring (discharger := tac)` uses the tactic sequence `tac` to discharge assumptions
  to the simplification lemmas. This only applies to user-supplied lemmas, since the default lemmas
  used by `jacobi_old_noncomm_ring` do not require a discharger.

Example:
```lean
example {R : Type*} [Ring R] (a b c : R) : a * (b + c + c - b) = 2 * a * c := by
  jacobi_old_noncomm_ring
```
-/
syntax (name := jacobi_old_noncomm_ring) "jacobi_old_noncomm_ring" optConfig (discharger)?
  (" [" ((simpStar <|> simpErase <|> simpLemma),*,?) "]")? : tactic

macro_rules
  | `(tactic| jacobi_old_noncomm_ring $cfg:optConfig $[$disch]? $[[$rules,*]]?) => do
    let rules' := rules.getD ⟨#[]⟩
    let tac ← `(tactic|
      (first | simp $cfg:optConfig $(disch)? only [
          -- Expand everything out.
          add_mul, mul_add, sub_eq_add_neg,
          -- Right associate all products.
          mul_assoc,
          -- Expand powers to numerals.
          pow_one, pow_zero, pow_succ,
          -- Replace multiplication by numerals with `zsmul`.
          one_mul, mul_one, zero_mul, mul_zero,
          nat_lit_mul_eq_nsmul, mul_nat_lit_eq_nsmul,
          -- Pull `zsmul n` out the front so `jacobi_old_abel` can see them.
          mul_smul_comm, smul_mul_assoc,
          -- Pull out negations.
          neg_mul, mul_neg,
          -- user-specified simp lemmas
          $rules',*] |
        fail "`jacobi_old_noncomm_ring` simp lemmas don't apply; try `jacobi_old_abel` instead") <;>
      first | jacobi_old_abel1 | jacobi_old_abel_nf)
    -- if a manual rewrite rule is provided, we repeat the tactic
    -- (since jacobi_old_abel might simplify and allow the rewrite to apply again)
    if rules.isSome then `(tactic| repeat1 ($tac;)) else `(tactic| $tac)

end Mathlib.Tactic.JacobiOldNoncommRing

/-!
We register `jacobi_old_noncomm_ring` with the `hint` tactic.
-/

register_hint 1000 jacobi_old_noncomm_ring
register_try?_tactic (priority := 1000) jacobi_old_noncomm_ring
