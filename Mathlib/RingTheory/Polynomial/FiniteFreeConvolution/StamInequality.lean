/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.RingTheory.Polynomial.FiniteFreeConvolution.Contraction

/-!
# Finite Free Convolution: The Stam Inequality

This file proves the finite free Stam inequality:
`1/Φ(p ⊞_n q) ≥ 1/Φ(p) + 1/Φ(q)` for monic real-rooted degree-n polynomials with distinct roots.

The proof derives the Stam inequality from the Φ contraction inequality
(`phiFisher_contraction`) via a Cauchy-Schwarz argument.

## Main results

* `Polynomial.finite_free_stam_inequality`: The Stam inequality for polynomials.
* `first_proof_problem4`: The formal problem statement from the "First Proof" benchmark.

## References

* Garza-Vargas, Srivastava, Stier. "The Finite Free Stam Inequality". arXiv:2602.15822.
-/

open scoped BigOperators
open Polynomial Finset Real

noncomputable section

namespace Polynomial

set_option maxHeartbeats 800000 in
-- The Cauchy-Schwarz argument from contraction inequality requires extra heartbeats.
/-- The finite free Stam inequality: `1/Φ(p ⊞_n q) ≥ 1/Φ(p) + 1/Φ(q)`.
    Derived from the Φ contraction inequality via a Cauchy-Schwarz argument:
    choosing a = Φ(q), b = Φ(p) in the contraction and simplifying. -/
theorem finite_free_stam_inequality (n : ℕ) (hn : n ≥ 2)
    (p q : ℝ[X])
    (hp : p.Splits (RingHom.id ℝ)) (hp_nodup : p.roots.Nodup)
    (hp_monic : p.Monic) (hp_deg : p.natDegree = n)
    (hq : q.Splits (RingHom.id ℝ)) (hq_nodup : q.roots.Nodup)
    (hq_monic : q.Monic) (hq_deg : q.natDegree = n)
    (hpq : (boxplus n p q).Splits (RingHom.id ℝ))
    (hpq_nodup : (boxplus n p q).roots.Nodup) :
    invPhiFisher (boxplus n p q) ≥ invPhiFisher p + invPhiFisher q := by
  -- Establish that root counts are ≥ 2
  have hp_card : p.roots.card ≥ 2 := by
    have := Polynomial.splits_iff_card_roots.mp hp; omega
  have hq_card : q.roots.card ≥ 2 := by
    have := Polynomial.splits_iff_card_roots.mp hq; omega
  have hpq_deg : (boxplus n p q).natDegree = n :=
    boxplus_natDegree n p q hp_monic hp_deg hq_monic hq_deg
  have hpq_card : (boxplus n p q).roots.card ≥ 2 := by
    have := Polynomial.splits_iff_card_roots.mp hpq; omega
  -- Establish positivity of Φ
  have h_pos_p : phiFisher p > 0 := phiFisher_pos p hp hp_nodup hp_card
  have h_pos_q : phiFisher q > 0 := phiFisher_pos q hq hq_nodup hq_card
  have h_pos_pq : phiFisher (boxplus n p q) > 0 :=
    phiFisher_pos _ hpq hpq_nodup hpq_card
  -- Unfold invPhiFisher and simplify the if-then-else
  unfold invPhiFisher
  simp only [hp_nodup, hq_nodup, hpq_nodup, true_and]
  simp only [show p.roots.card > 1 from by omega, show q.roots.card > 1 from by omega,
    show (boxplus n p q).roots.card > 1 from by omega, ite_true]
  -- Goal: 1 / phiFisher (boxplus n p q) ≥ 1 / phiFisher p + 1 / phiFisher q
  rw [ge_iff_le, div_add_div _ _ (ne_of_gt h_pos_p) (ne_of_gt h_pos_q),
    div_le_div_iff₀ (by positivity) h_pos_pq]
  have h_contr := phiFisher_contraction n hn (phiFisher q) (phiFisher p) p q
    hp hp_nodup hp_monic hp_deg hq hq_nodup hq_monic hq_deg hpq hpq_nodup
  nlinarith [sq_nonneg (phiFisher p - phiFisher q)]

end Polynomial

/-!
## Bridge to the formal problem statement

We connect the polynomial formulation to the root-vector formulation
from the "First Proof" benchmark (arXiv:2602.05192).
-/

section Bridge

open Polynomial Finset

/-- Φ_n(λ) = ∑ᵢ (∑_{j≠i} 1/(λᵢ - λⱼ))² for a tuple of distinct reals. -/
def phi (n : ℕ) (roots : Fin n → ℝ) : ℝ :=
  ∑ i, (∑ j ∈ univ.erase i, 1 / (roots i - roots j)) ^ 2

/-- The finite free additive convolution, defined identically to `Polynomial.boxplus`. -/
def freeAddConv (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  Polynomial.boxplus n p q

/-- `phi n f` equals `Polynomial.phiVec f` (definitional equality). -/
lemma phi_eq_phiVec {n : ℕ} (f : Fin n → ℝ) : phi n f = Polynomial.phiVec f := rfl

/-- ∏ᵢ (X - C(f i)) is monic. -/
lemma monic_prod_X_sub_C_fin {n : ℕ} (f : Fin n → ℝ) :
    (∏ i : Fin n, (X - C (f i))).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (f i)

/-- The degree of ∏ᵢ (X - C(f i)) is n. -/
lemma natDegree_prod_X_sub_C_fin {n : ℕ} (f : Fin n → ℝ) :
    (∏ i : Fin n, (X - C (f i))).natDegree = n := by
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (f i))]
  simp

/-- ∏ᵢ (X - C(f i)) splits over ℝ. -/
lemma splits_prod_X_sub_C_fin {n : ℕ} (f : Fin n → ℝ) :
    (∏ i : Fin n, (X - C (f i))).Splits (RingHom.id ℝ) :=
  splits_prod _ fun _ _ => splits_X_sub_C _

/-- When f is injective, ∏ᵢ (X - C(f i)) has distinct roots. -/
lemma nodup_roots_prod_X_sub_C_fin {n : ℕ} {f : Fin n → ℝ}
    (hf : Function.Injective f) :
    (∏ i : Fin n, (X - C (f i))).roots.Nodup := by
  rw [Polynomial.roots_prod_X_sub_C_fin]
  exact Finset.univ.nodup.map hf

/-- The root count of ∏ᵢ (X - C(f i)) is n. -/
lemma card_roots_prod_X_sub_C_fin {n : ℕ} (f : Fin n → ℝ) :
    (∏ i : Fin n, (X - C (f i))).roots.card = n := by
  rw [Polynomial.roots_prod_X_sub_C_fin]; simp

/-- The root-vector phi equals the polynomial phiFisher for root polynomials. -/
lemma phi_eq_phiFisher_prod {n : ℕ} {f : Fin n → ℝ} (hf : Function.Injective f) :
    phi n f = Polynomial.phiFisher (∏ i : Fin n, (X - C (f i))) := by
  rw [phi_eq_phiVec, ← Polynomial.phiFisher_eq_phiVec hf]

/-- **Problem 4 from "First Proof" (Spielman).**
    For monic real-rooted polynomials p and q of degree n with distinct roots,
    the finite free additive convolution satisfies
    1/Φ_n(p ⊞_n q) ≥ 1/Φ_n(p) + 1/Φ_n(q)
    where the roots of p ⊞_n q are also assumed to be distinct. -/
theorem first_proof_problem4 (n : ℕ) (_hn : 0 < n)
    (rp rq rpq : Fin n → ℝ)
    (hp : Function.Injective rp) (hq : Function.Injective rq) (hpq : Function.Injective rpq)
    (hconv : (∏ i : Fin n, (X - C (rpq i))) =
             freeAddConv n (∏ i : Fin n, (X - C (rp i))) (∏ i : Fin n, (X - C (rq i))))
    : 1 / phi n rpq ≥ 1 / phi n rp + 1 / phi n rq := by
  -- Handle the trivial case n < 2
  by_cases hn2 : n < 2
  · have h1 : n = 1 := by omega
    subst h1; simp [phi]
  push_neg at hn2
  -- Set up the root polynomials
  set pp := ∏ i : Fin n, (X - C (rp i))
  set qq := ∏ i : Fin n, (X - C (rq i))
  set ppqq := ∏ i : Fin n, (X - C (rpq i))
  -- Structural properties
  have pp_monic := monic_prod_X_sub_C_fin rp
  have pp_deg := natDegree_prod_X_sub_C_fin rp
  have pp_splits := splits_prod_X_sub_C_fin rp
  have pp_nodup := nodup_roots_prod_X_sub_C_fin hp
  have qq_monic := monic_prod_X_sub_C_fin rq
  have qq_deg := natDegree_prod_X_sub_C_fin rq
  have qq_splits := splits_prod_X_sub_C_fin rq
  have qq_nodup := nodup_roots_prod_X_sub_C_fin hq
  have ppqq_splits := splits_prod_X_sub_C_fin rpq
  have ppqq_nodup := nodup_roots_prod_X_sub_C_fin hpq
  -- The hypothesis says ppqq = boxplus n pp qq
  have hconv' : ppqq = Polynomial.boxplus n pp qq := hconv
  -- Apply the polynomial Stam inequality
  have h_stam := Polynomial.finite_free_stam_inequality n hn2 pp qq
    pp_splits pp_nodup pp_monic pp_deg
    qq_splits qq_nodup qq_monic qq_deg
    (hconv' ▸ ppqq_splits) (hconv' ▸ ppqq_nodup)
  -- h_stam : invPhiFisher (boxplus n pp qq) ≥ invPhiFisher pp + invPhiFisher qq
  -- Unfold invPhiFisher using the known properties
  have pp_card : pp.roots.card > 1 := by rw [card_roots_prod_X_sub_C_fin]; omega
  have qq_card : qq.roots.card > 1 := by rw [card_roots_prod_X_sub_C_fin]; omega
  have ppqq_card : ppqq.roots.card > 1 := by rw [card_roots_prod_X_sub_C_fin]; omega
  have bpq_card : (Polynomial.boxplus n pp qq).roots.card > 1 := by rwa [← hconv']
  have bpq_nodup : (Polynomial.boxplus n pp qq).roots.Nodup := by rwa [← hconv']
  -- Rewrite invPhiFisher in h_stam
  simp only [Polynomial.invPhiFisher,
    show pp.roots.Nodup ∧ pp.roots.card > 1 from ⟨pp_nodup, pp_card⟩,
    show qq.roots.Nodup ∧ qq.roots.card > 1 from ⟨qq_nodup, qq_card⟩,
    show (Polynomial.boxplus n pp qq).roots.Nodup ∧
      (Polynomial.boxplus n pp qq).roots.card > 1 from ⟨bpq_nodup, bpq_card⟩] at h_stam
  -- h_stam : 1 / phiFisher (boxplus n pp qq) ≥ 1 / phiFisher pp + 1 / phiFisher qq
  -- Rewrite using phi = phiFisher and ppqq = boxplus n pp qq
  rw [phi_eq_phiFisher_prod hp, phi_eq_phiFisher_prod hq, phi_eq_phiFisher_prod hpq]
  change 1 / Polynomial.phiFisher ppqq ≥
    1 / Polynomial.phiFisher pp + 1 / Polynomial.phiFisher qq
  rw [hconv']
  exact h_stam

end Bridge
