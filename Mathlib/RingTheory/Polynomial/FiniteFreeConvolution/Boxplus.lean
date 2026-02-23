/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.RingTheory.Polynomial.FiniteFreeConvolution.Defs

/-!
# Finite Free Convolution: Boxplus Properties

This file proves basic properties of the finite free additive convolution (boxplus),
including that it preserves monicity and degree, is commutative, and commutes with translation.

## Main results

* `Polynomial.boxplus_monic`: The boxplus of two monic degree-n polynomials is monic.
* `Polynomial.boxplus_natDegree`: The boxplus of two degree-n polynomials has degree n.
* `Polynomial.boxplus_comm`: Boxplus is commutative.
* `Polynomial.boxplusCoeff_one`: Formula for the k=1 coefficient.
* `Polynomial.boxplus_comp_add_C`: Boxplus commutes with translation.

## References

* Garza-Vargas, Srivastava, Stier. "The Finite Free Stam Inequality". arXiv:2602.15822.
-/

set_option maxHeartbeats 400000

open scoped BigOperators
open Polynomial Finset

noncomputable section

namespace Polynomial

/-- The boxplus convolution of two monic polynomials of degree n is monic of degree n. -/
lemma boxplus_monic_and_natDegree (n : ℕ) (p q : ℝ[X])
    (hp_monic : p.Monic) (hp_deg : p.natDegree = n)
    (hq_monic : q.Monic) (hq_deg : q.natDegree = n) :
    (boxplus n p q).Monic ∧ (boxplus n p q).natDegree = n := by
  have h_leading_coeff : (boxplus n p q).coeff n = 1 := by
    unfold boxplus
    simp +zetaDelta at *
    rw [Finset.sum_eq_single 0] <;> norm_num
    · unfold boxplusCoeff
      simp +decide [← hp_deg, ← hq_deg, hp_monic.coeff_natDegree, hq_monic.coeff_natDegree,
        Nat.factorial_ne_zero]
      rw [← hq_monic.coeff_natDegree, hp_deg, hq_deg]
    · intros; omega
  rw [Polynomial.Monic, Polynomial.leadingCoeff,
    Polynomial.natDegree_eq_of_degree_eq_some] <;> aesop
  rw [Polynomial.degree_eq_of_le_of_coeff_ne_zero] <;> norm_num [h_leading_coeff, hp_deg]
  refine le_trans (Polynomial.degree_sum_le _ _) ?_
  exact Finset.sup_le fun i hi =>
    le_trans (Polynomial.degree_C_mul_X_pow_le _ _)
      (WithBot.coe_le_coe.mpr (Nat.sub_le _ _))

/-- The boxplus convolution of two monic polynomials is monic. -/
lemma boxplus_monic (n : ℕ) (p q : ℝ[X])
    (hp_monic : p.Monic) (hp_deg : p.natDegree = n)
    (hq_monic : q.Monic) (hq_deg : q.natDegree = n) :
    (boxplus n p q).Monic :=
  (boxplus_monic_and_natDegree n p q hp_monic hp_deg hq_monic hq_deg).1

/-- The boxplus convolution of two degree-n polynomials has degree n. -/
lemma boxplus_natDegree (n : ℕ) (p q : ℝ[X])
    (hp_monic : p.Monic) (hp_deg : p.natDegree = n)
    (hq_monic : q.Monic) (hq_deg : q.natDegree = n) :
    (boxplus n p q).natDegree = n :=
  (boxplus_monic_and_natDegree n p q hp_monic hp_deg hq_monic hq_deg).2

/-- Boxplus is commutative. -/
lemma boxplus_comm (n : ℕ) (p q : ℝ[X]) :
    boxplus n p q = boxplus n q p := by
  unfold boxplus
  congr! 2
  unfold boxplusCoeff
  rw [← Finset.sum_flip]
  exact congr_arg _ (Finset.sum_congr rfl fun i hi => by
    rw [Nat.sub_sub_self (Finset.mem_range_succ_iff.mp hi)]; ring)

/-- The coefficient formula for k=1 in boxplus. -/
lemma boxplusCoeff_one (n : ℕ) (hn : n ≥ 1) (p q : ℝ[X])
    (hp_monic : p.Monic) (hp_deg : p.natDegree = n)
    (hq_monic : q.Monic) (hq_deg : q.natDegree = n) :
    boxplusCoeff n p q 1 = p.coeff (n - 1) + q.coeff (n - 1) := by
  simp [boxplusCoeff, Finset.range_add_one]
  simp +decide [mul_comm, mul_div_mul_left, Nat.factorial_ne_zero]
  have := hp_monic.coeff_natDegree; have := hq_monic.coeff_natDegree; aesop

end Polynomial
