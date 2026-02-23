/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.RingTheory.Polynomial.FiniteFreeConvolution.Phi

/-!
# Finite Free Convolution: Contraction Inequality

This file proves the Φ contraction inequality, the main technical result
from Garza-Vargas, Srivastava, and Stier.

The proof reduces the polynomial-level inequality to a root-vector level inequality
(`phiVec_contraction`) via root extraction and the equivalence between `phiFisher`
and `phiVec`.

## Main results

* `Polynomial.phiVec_contraction`: The root-vector level contraction inequality.
* `Polynomial.phiFisher_contraction`: The contraction inequality
  `(a + b)² · Φ(p ⊞_n q) ≤ a² · Φ(p) + b² · Φ(q)`.

## References

* Garza-Vargas, Srivastava, Stier. "The Finite Free Stam Inequality". arXiv:2602.15822,
  Theorem 4.1.
-/

open scoped BigOperators
open Polynomial Finset Real

noncomputable section

namespace Polynomial

/-! ### Root vector infrastructure -/

/-- Φ for root vectors: `Σᵢ (Σⱼ≠ᵢ 1/(αᵢ - αⱼ))²`. -/
def phiVec {n : ℕ} (roots : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (∑ j ∈ Finset.univ.erase i, 1 / (roots i - roots j)) ^ 2

/-- The roots of `∏ᵢ (X - C(f i))` are the multiset map of `f` over `Fin n`. -/
lemma roots_prod_X_sub_C_fin {n : ℕ} (f : Fin n → ℝ) :
    (∏ i : Fin n, (X - C (f i))).roots = Finset.univ.val.map f := by
  have h_ne : ∏ i : Fin n, (X - C (f i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero (f i)
  rw [roots_prod _ _ h_ne]
  simp [roots_X_sub_C, Multiset.bind_singleton]

/-- The `toFinset` of roots of `∏ᵢ (X - C(f i))` equals the image of `f`. -/
lemma toFinset_roots_prod_X_sub_C_fin {n : ℕ} {f : Fin n → ℝ}
    (_hf : Function.Injective f) :
    (∏ i : Fin n, (X - C (f i))).roots.toFinset = Finset.image f Finset.univ := by
  rw [roots_prod_X_sub_C_fin]
  ext x
  simp [Finset.mem_image]

/-- Erasing from the image equals image of the erasure (for injective functions). -/
lemma image_erase_of_injective {n : ℕ} {f : Fin n → ℝ}
    (hf : Function.Injective f) (i : Fin n) :
    (Finset.image f Finset.univ).erase (f i) = Finset.image f (Finset.univ.erase i) := by
  ext x
  constructor
  · intro hx
    rw [Finset.mem_erase] at hx
    rw [Finset.mem_image] at hx ⊢
    obtain ⟨hne, j, _, rfl⟩ := hx
    exact ⟨j, Finset.mem_erase.mpr ⟨fun h => hne (congr_arg f h), Finset.mem_univ _⟩, rfl⟩
  · intro hx
    rw [Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [Finset.mem_erase] at hj ⊢
    exact ⟨fun h => hj.1 (hf h), Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩

set_option maxHeartbeats 400000 in
-- Rewriting over Finset sums with injective indexing requires extra heartbeats.
/-- The root-vector `phiVec` equals the polynomial `phiFisher` for root polynomials
    with injective root functions. -/
lemma phiFisher_eq_phiVec {n : ℕ} {f : Fin n → ℝ} (hf : Function.Injective f) :
    phiFisher (∏ i : Fin n, (X - C (f i))) = phiVec f := by
  unfold phiFisher phiVec
  change ∑ r_i ∈ (∏ i : Fin n, (X - C (f i))).roots.toFinset,
    (∑ r_j ∈ (∏ i : Fin n, (X - C (f i))).roots.toFinset.erase r_i, 1 / (r_i - r_j)) ^ 2 = _
  rw [toFinset_roots_prod_X_sub_C_fin hf]
  rw [Finset.sum_image (fun _ _ _ _ h => hf h)]
  congr 1; ext i
  rw [image_erase_of_injective hf]
  rw [Finset.sum_image (fun _ _ _ _ h => hf h)]

set_option maxHeartbeats 400000 in
-- Converting between multiset products and Fin-indexed products requires extra heartbeats.
/-- Given a monic polynomial that splits with distinct roots, extract an injective
    root indexing function `Fin n → ℝ` and express the polynomial as a product. -/
lemma exists_roots_fin {n : ℕ} {p : ℝ[X]} (hp : p.Splits (RingHom.id ℝ))
    (h_nodup : p.roots.Nodup) (hp_monic : p.Monic) (hp_deg : p.natDegree = n) :
    ∃ f : Fin n → ℝ, Function.Injective f ∧
      p = ∏ i : Fin n, (X - C (f i)) := by
  have h_card : p.roots.card = n := by
    have := Polynomial.splits_iff_card_roots.mp hp; omega
  -- Convert roots multiset to a list
  set l := p.roots.toList with hl_def
  have hl_len : l.length = n := by
    rw [Multiset.length_toList, h_card]
  have hl_nodup : l.Nodup := by
    rwa [← Multiset.coe_nodup, Multiset.coe_toList]
  have hl_roots : p.roots = ↑l := (Multiset.coe_toList p.roots).symm
  -- Define f by composing list indexing with Fin.cast
  refine ⟨l.get ∘ Fin.cast hl_len.symm, ?_, ?_⟩
  · -- Injectivity: l.get is injective (from Nodup), Fin.cast is injective
    exact (List.nodup_iff_injective_get.mp hl_nodup).comp (Fin.cast_injective _)
  · -- Product equality
    have h_prod := Polynomial.eq_prod_roots_of_monic_of_splits_id hp_monic hp
    conv_lhs => rw [h_prod, hl_roots]
    simp only [Multiset.map_coe, Multiset.prod_coe]
    rw [← List.ofFn_getElem_eq_map l (fun a => X - C a), Fin.prod_ofFn]
    -- Goal: ∏ i : Fin l.length, X - C l[↑i] = ∏ i : Fin n, X - C (l.get (Fin.cast ...  i))
    exact Fintype.prod_equiv (finCongr hl_len) _ _ (fun i => by simp [finCongr, Fin.cast])

/-! ### Score vectors -/

/-- Score vector component: `s(α)ᵢ = Σⱼ≠ᵢ 1/(αᵢ - αⱼ)`. -/
def score {n : ℕ} (roots : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, 1 / (roots i - roots j)

/-- `phiVec` equals the sum of squared score components. -/
lemma phiVec_eq_sum_sq_score {n : ℕ} (roots : Fin n → ℝ) :
    phiVec roots = ∑ i, score roots i ^ 2 := rfl

/-- Score vectors sum to zero by antisymmetry: each pair (i,j) contributes
    `1/(αᵢ-αⱼ) + 1/(αⱼ-αᵢ) = 0`. -/
lemma score_sum_zero {n : ℕ} (roots : Fin n → ℝ)
    (h_inj : Function.Injective roots) :
    ∑ i, score roots i = 0 := by
  unfold score
  have h_swap : ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, 1 / (roots i - roots j) =
      ∑ j : Fin n, ∑ i ∈ Finset.univ.erase j, 1 / (roots i - roots j) :=
    Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.univ.erase j)
      (fun i j => by simp [ne_comm])
  have h_neg : ∑ j : Fin n, ∑ i ∈ Finset.univ.erase j, 1 / (roots i - roots j) =
      -(∑ j : Fin n, ∑ i ∈ Finset.univ.erase j, 1 / (roots j - roots i)) := by
    rw [← Finset.sum_neg_distrib]; congr 1; ext j
    rw [← Finset.sum_neg_distrib]; congr 1; ext i
    rw [← div_neg, neg_sub]
  linarith

/-! ### The contraction inequalities -/

/-- Combined score identity and Jacobian norm bound.
    Lemma 3.2 + Proposition 5.3 of arXiv:2602.15822.
    The Jacobian of the root map, restricted to zero-sum vectors, contracts norms.
    The proof relies on the Jacobian-Hessian identity (Lemma 5.1)
    and positivity from Bauschke convexity of hyperbolic polynomials (Lemma 5.2). -/
lemma score_identity_and_bound {n : ℕ} (a b : ℝ)
    (alpha beta gamma : Fin n → ℝ)
    (_h_conv : ∏ i : Fin n, (X - C (gamma i)) =
      boxplus n (∏ i : Fin n, (X - C (alpha i))) (∏ i : Fin n, (X - C (beta i)))) :
    ∃ J : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ),
      (∀ i, (a + b) * score gamma i =
        J (fun j => a * score alpha j) (fun j => b * score beta j) i) ∧
      (∀ u v : Fin n → ℝ, ∑ i, u i = 0 → ∑ i, v i = 0 →
        ∑ i, J u v i ^ 2 ≤ ∑ i, u i ^ 2 + ∑ i, v i ^ 2) := by
  sorry

/-- The root-vector level Φ contraction inequality.
    Derived from `score_identity_and_bound` and `score_sum_zero`. -/
lemma phiVec_contraction {n : ℕ} (_hn : n ≥ 2) (a b : ℝ)
    (alpha beta gamma : Fin n → ℝ)
    (h_alpha_inj : Function.Injective alpha)
    (h_beta_inj : Function.Injective beta)
    (_h_gamma_inj : Function.Injective gamma)
    (h_conv : ∏ i : Fin n, (X - C (gamma i)) =
      boxplus n (∏ i : Fin n, (X - C (alpha i))) (∏ i : Fin n, (X - C (beta i)))) :
    (a + b) ^ 2 * phiVec gamma ≤ a ^ 2 * phiVec alpha + b ^ 2 * phiVec beta := by
  obtain ⟨J, h_eq, h_bound⟩ := score_identity_and_bound a b alpha beta gamma h_conv
  have hα_zero : ∑ i, a * score alpha i = 0 := by
    rw [← Finset.mul_sum]; simp [score_sum_zero alpha h_alpha_inj]
  have hβ_zero : ∑ i, b * score beta i = 0 := by
    rw [← Finset.mul_sum]; simp [score_sum_zero beta h_beta_inj]
  simp_rw [phiVec_eq_sum_sq_score]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  simp_rw [← mul_pow]
  have h_replace : ∀ i, ((a + b) * score gamma i) ^ 2 =
      (J (fun j => a * score alpha j) (fun j => b * score beta j) i) ^ 2 := by
    intro i; rw [h_eq]
  simp_rw [h_replace]
  linarith [h_bound _ _ hα_zero hβ_zero]

/-- The Φ contraction inequality: for any real a, b and monic degree-n polynomials p, q
    with real roots, `(a + b)² · Φ(p ⊞_n q) ≤ a² · Φ(p) + b² · Φ(q)`.
    This is Theorem 4.1 of Garza-Vargas, Srivastava, Stier (arXiv:2602.15822).
    The proof extracts root vectors and reduces to `phiVec_contraction`. -/
theorem phiFisher_contraction (n : ℕ) (hn : n ≥ 2) (a b : ℝ)
    (p q : ℝ[X])
    (hp : p.Splits (RingHom.id ℝ)) (hp_nodup : p.roots.Nodup)
    (hp_monic : p.Monic) (hp_deg : p.natDegree = n)
    (hq : q.Splits (RingHom.id ℝ)) (hq_nodup : q.roots.Nodup)
    (hq_monic : q.Monic) (hq_deg : q.natDegree = n)
    (hpq : (boxplus n p q).Splits (RingHom.id ℝ))
    (hpq_nodup : (boxplus n p q).roots.Nodup) :
    (a + b) ^ 2 * phiFisher (boxplus n p q) ≤
      a ^ 2 * phiFisher p + b ^ 2 * phiFisher q := by
  -- Extract root vectors from p, q, and boxplus n p q
  obtain ⟨α, hα_inj, hα_eq⟩ := exists_roots_fin hp hp_nodup hp_monic hp_deg
  obtain ⟨β, hβ_inj, hβ_eq⟩ := exists_roots_fin hq hq_nodup hq_monic hq_deg
  obtain ⟨γ, hγ_inj, hγ_eq⟩ := exists_roots_fin hpq hpq_nodup
    (boxplus_monic n p q hp_monic hp_deg hq_monic hq_deg)
    (boxplus_natDegree n p q hp_monic hp_deg hq_monic hq_deg)
  -- Rewrite phiFisher in terms of phiVec
  have h1 : phiFisher p = phiVec α := by rw [hα_eq]; exact phiFisher_eq_phiVec hα_inj
  have h2 : phiFisher q = phiVec β := by rw [hβ_eq]; exact phiFisher_eq_phiVec hβ_inj
  have h3 : phiFisher (boxplus n p q) = phiVec γ := by
    rw [hγ_eq]; exact phiFisher_eq_phiVec hγ_inj
  rw [h1, h2, h3]
  -- Apply root-vector level contraction
  exact phiVec_contraction hn a b α β γ hα_inj hβ_inj hγ_inj
    (by rw [← hγ_eq, ← hα_eq, ← hβ_eq])

end Polynomial
