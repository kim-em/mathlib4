/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.RingTheory.Polynomial.FiniteFreeConvolution.Boxplus

/-!
# Finite Free Convolution: Fisher Information Properties

This file proves properties of the Fisher information functional Φ(p),
including its positivity for polynomials with distinct roots.

## Main results

* `Polynomial.phiFisher_pos`: Φ(p) > 0 for real-rooted polynomials with ≥ 2 distinct roots.

## References

* Garza-Vargas, Srivastava, Stier. "The Finite Free Stam Inequality". arXiv:2602.15822.
-/

open scoped BigOperators
open Polynomial Finset Real

noncomputable section

namespace Polynomial

set_option maxHeartbeats 800000 in
/-- Φ(p) is strictly positive for any polynomial p with real coefficients, degree at least 2,
    and distinct real roots. -/
lemma phiFisher_pos (p : ℝ[X]) (_h_splits : p.Splits (RingHom.id ℝ))
    (h_nodup : p.roots.Nodup) (h_card : p.roots.card ≥ 2) :
    phiFisher p > 0 := by
  unfold phiFisher
  -- β-reduce the let binding so Finset.single_le_sum can match the goal
  change ∑ r_i ∈ p.roots.toFinset,
    (∑ r_j ∈ p.roots.toFinset.erase r_i, 1 / (r_i - r_j)) ^ 2 > 0
  have h_card' : p.roots.toFinset.card ≥ 2 := by
    rwa [Multiset.toFinset_card_of_nodup h_nodup]
  -- Take the minimum root r_min.
  obtain ⟨r_min, hr_min, hr_min_le⟩ :=
    Finset.exists_min_image p.roots.toFinset id (Finset.card_pos.mp (by omega))
  -- hr_min_le : ∀ x' ∈ p.roots.toFinset, id r_min ≤ id x'
  -- (id is definitionally the identity, so this is r_min ≤ x')
  -- The score at r_min is strictly negative (each 1/(r_min - r_j) ≤ 0, with one < 0).
  have h_score_neg : (∑ r_j ∈ p.roots.toFinset.erase r_min, 1 / (r_min - r_j)) < 0 := by
    have h_nonpos : ∀ x ∈ p.roots.toFinset.erase r_min, (1 : ℝ) / (r_min - x) ≤ 0 := by
      intro x hx
      apply div_nonpos_of_nonneg_of_nonpos zero_le_one
      exact sub_nonpos.mpr (hr_min_le _ (Finset.mem_erase.mp hx).2)
    -- Find a second distinct root via cardinality of the erased set
    have h_erase_card : (p.roots.toFinset.erase r_min).card ≥ 1 := by
      rw [Finset.card_erase_of_mem hr_min]; omega
    obtain ⟨r2, hr2_erase⟩ := Finset.card_pos.mp (by omega :
      0 < (p.roots.toFinset.erase r_min).card)
    have hr2_ne : r2 ≠ r_min := (Finset.mem_erase.mp hr2_erase).1
    have hr2_mem : r2 ∈ p.roots.toFinset := (Finset.mem_erase.mp hr2_erase).2
    have h_neg : (1 : ℝ) / (r_min - r2) < 0 := by
      apply div_neg_of_pos_of_neg one_pos
      exact sub_neg.mpr (lt_of_le_of_ne (hr_min_le _ hr2_mem) (Ne.symm hr2_ne))
    calc ∑ r_j ∈ p.roots.toFinset.erase r_min, 1 / (r_min - r_j)
        < ∑ _ ∈ p.roots.toFinset.erase r_min, (0 : ℝ) :=
          Finset.sum_lt_sum h_nonpos ⟨r2, hr2_erase, h_neg⟩
      _ = 0 := Finset.sum_const_zero
  -- Since the score is negative, its square is positive.
  have h_sq_pos : (∑ r_j ∈ p.roots.toFinset.erase r_min, 1 / (r_min - r_j)) ^ 2 > 0 :=
    sq_pos_of_neg h_score_neg
  -- This positive square is ≤ the full sum (which is a sum of nonneg terms).
  exact lt_of_lt_of_le h_sq_pos
    (Finset.single_le_sum
      (fun x _ => sq_nonneg (∑ r_j ∈ p.roots.toFinset.erase x, 1 / (x - r_j))) hr_min)

end Polynomial
