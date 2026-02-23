import Mathlib

set_option maxHeartbeats 800000

open scoped BigOperators Matrix
open Polynomial Finset Real

noncomputable section

-- ===== Definitions =====

def ffc_coeff (n : ℕ) (p q : ℝ[X]) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    let j := k - i
    (Nat.factorial (n - i) * Nat.factorial (n - j) : ℝ) /
      (Nat.factorial n * Nat.factorial (n - k) : ℝ) *
    (p.coeff (n - i)) * (q.coeff (n - j))

def ffc (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (ffc_coeff n p q k) * Polynomial.X ^ (n - k)

def score_rv {n : ℕ} (roots : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, 1 / (roots i - roots j)

-- ===== Score sum zero =====

lemma score_rv_sum_zero {n : ℕ} (roots : Fin n → ℝ)
    (_h_inj : Function.Injective roots) :
    ∑ i, score_rv roots i = 0 := by
  unfold score_rv
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

-- ===== Doubly stochastic norm bound =====

-- Jensen's inequality for weighted sums: (∑ wⱼ xⱼ)² ≤ ∑ wⱼ xⱼ² when wⱼ ≥ 0, ∑ wⱼ = 1.
private lemma weighted_sq_le (w x : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hw_sum : ∑ j, w j = 1) :
    (∑ j, w j * x j) ^ 2 ≤ ∑ j, w j * x j ^ 2 := by
  have h := sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (r := fun j => w j * x j)
    (f := fun j => w j)
    (g := fun j => w j * x j ^ 2)
    (fun j _ => hw j)
    (fun j _ => mul_nonneg (hw j) (sq_nonneg _))
    (fun j _ => by ring)
  rw [hw_sum, one_mul] at h
  exact h

lemma doubly_stochastic_sq_norm_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M ∈ doublyStochastic ℝ (Fin n))
    (v : Fin n → ℝ) :
    ∑ i, (M.mulVec v i) ^ 2 ≤ ∑ i, v i ^ 2 := by
  -- Step 1: Jensen for each row
  have h_jensen : ∀ i, (∑ j, M i j * v j) ^ 2 ≤ ∑ j, M i j * (v j) ^ 2 :=
    fun i => weighted_sq_le (M i) v (fun j => nonneg_of_mem_doublyStochastic hM)
      (sum_row_of_mem_doublyStochastic hM i)
  -- Step 2: Sum over rows, swap sums, use column-stochasticity
  calc ∑ i, (M.mulVec v i) ^ 2
      = ∑ i, (∑ j, M i j * v j) ^ 2 := by
        simp only [Matrix.mulVec, dotProduct]
    _ ≤ ∑ i, ∑ j, M i j * (v j) ^ 2 :=
        Finset.sum_le_sum fun i _ => h_jensen i
    _ = ∑ j, (∑ i, M i j) * (v j) ^ 2 := by
        rw [Finset.sum_comm]; congr 1; ext j; rw [← Finset.sum_mul]
    _ = ∑ j, v j ^ 2 := by
        congr 1; ext j; rw [sum_col_of_mem_doublyStochastic hM j, one_mul]

-- ===== Contraction from DS + cross term bound =====

lemma contraction_from_ds {n : ℕ}
    (E_α E_β : Matrix (Fin n) (Fin n) ℝ)
    (hα : E_α ∈ doublyStochastic ℝ (Fin n))
    (hβ : E_β ∈ doublyStochastic ℝ (Fin n))
    (u v : Fin n → ℝ)
    (h_cross : ∑ i, (E_β.mulVec u i) * (E_α.mulVec v i) ≤ 0) :
    ∑ i, ((E_β.mulVec u) i + (E_α.mulVec v) i) ^ 2 ≤ ∑ i, u i ^ 2 + ∑ i, v i ^ 2 := by
  have expand : ∀ i : Fin n, ((E_β.mulVec u) i + (E_α.mulVec v) i) ^ 2 =
      (E_β.mulVec u i) ^ 2 + 2 * ((E_β.mulVec u i) * (E_α.mulVec v i)) + (E_α.mulVec v i) ^ 2 := by
    intro i; ring
  simp_rw [expand]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith [doubly_stochastic_sq_norm_le E_β hβ u, doubly_stochastic_sq_norm_le E_α hα v]

-- ===== Deep axiom =====

/-- The Jacobian decomposition and contraction for the root map of the finite free
    convolution. This combines several results from arXiv:2602.15822:
    - Lemma 3.4: The Jacobian decomposes via doubly stochastic conditional expectation
      matrices E_α, E_β with E_β · score(α) = score(γ) and E_α · score(β) = score(γ)
    - Lemma 5.1 (Jacobian-Hessian identity) + Lemma 5.2 (Bauschke positivity):
      The cross term ⟨E_β u, E_α v⟩ ≤ 0 for zero-sum u, v

    NOTE: The cross term non-positivity is the deepest part of the proof, relying on
    Bauschke-Güler-Lewis-Sendov convexity of eigenvalues of hyperbolic polynomials. -/
axiom jacobian_decomposition {n : ℕ}
    (alpha beta gamma : Fin n → ℝ)
    (_h_alpha_inj : Function.Injective alpha)
    (_h_beta_inj : Function.Injective beta)
    (h_conv : ∏ i : Fin n, (Polynomial.X - Polynomial.C (gamma i)) =
      ffc n (∏ i : Fin n, (Polynomial.X - Polynomial.C (alpha i)))
            (∏ i : Fin n, (Polynomial.X - Polynomial.C (beta i)))) :
    ∃ (E_α E_β : Matrix (Fin n) (Fin n) ℝ),
      E_α ∈ doublyStochastic ℝ (Fin n) ∧
      E_β ∈ doublyStochastic ℝ (Fin n) ∧
      -- Score identity: E_β · score(α) = score(γ)
      (∀ i, (E_β.mulVec (score_rv alpha)) i = score_rv gamma i) ∧
      -- Score identity: E_α · score(β) = score(γ)
      (∀ i, (E_α.mulVec (score_rv beta)) i = score_rv gamma i) ∧
      -- Cross term non-positivity (from Bauschke convexity)
      (∀ u v : Fin n → ℝ, ∑ i, u i = 0 → ∑ i, v i = 0 →
        ∑ i, (E_β.mulVec u i) * (E_α.mulVec v i) ≤ 0)

-- ===== Main theorem =====

theorem phi_rv_contraction {n : ℕ} (_hn : n ≥ 2) (a b : ℝ)
    (alpha beta gamma : Fin n → ℝ)
    (h_alpha_inj : Function.Injective alpha)
    (h_beta_inj : Function.Injective beta)
    (_h_gamma_inj : Function.Injective gamma)
    (h_conv : ∏ i : Fin n, (Polynomial.X - Polynomial.C (gamma i)) =
      ffc n (∏ i : Fin n, (Polynomial.X - Polynomial.C (alpha i)))
            (∏ i : Fin n, (Polynomial.X - Polynomial.C (beta i)))) :
    (a + b) ^ 2 * ∑ i, (score_rv gamma i) ^ 2 ≤
      a ^ 2 * ∑ i, (score_rv alpha i) ^ 2 + b ^ 2 * ∑ i, (score_rv beta i) ^ 2 := by
  -- Get the Jacobian decomposition
  obtain ⟨E_α, E_β, hα, hβ, h_scoreα, h_scoreβ, h_cross⟩ :=
    jacobian_decomposition alpha beta gamma h_alpha_inj h_beta_inj h_conv
  -- Scaled score vectors are zero-sum
  have hα_sum : ∑ i, (a * score_rv alpha i) = 0 := by
    rw [← Finset.mul_sum]; simp [score_rv_sum_zero alpha h_alpha_inj]
  have hβ_sum : ∑ i, (b * score_rv beta i) = 0 := by
    rw [← Finset.mul_sum]; simp [score_rv_sum_zero beta h_beta_inj]
  -- The key identity: (a+b) score(γ) = E_β(a·score(α)) + E_α(b·score(β))
  -- This follows from linearity of mulVec and the score identities
  have h_key : ∀ i, (a + b) * score_rv gamma i =
      (E_β.mulVec (fun j => a * score_rv alpha j)) i +
      (E_α.mulVec (fun j => b * score_rv beta j)) i := by
    intro i
    have h1 : a * score_rv gamma i = (E_β.mulVec (fun j => a * score_rv alpha j)) i := by
      rw [← h_scoreα i]; simp only [Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum]; congr 1; ext j; ring
    have h2 : b * score_rv gamma i = (E_α.mulVec (fun j => b * score_rv beta j)) i := by
      rw [← h_scoreβ i]; simp only [Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum]; congr 1; ext j; ring
    linarith [h1, h2]
  -- Get the cross term bound for scaled vectors
  have h_cross_scaled := h_cross
    (fun j => a * score_rv alpha j) (fun j => b * score_rv beta j)
    hα_sum hβ_sum
  -- Apply the contraction
  have h_contr := contraction_from_ds E_α E_β hα hβ
    (fun j => a * score_rv alpha j) (fun j => b * score_rv beta j)
    h_cross_scaled
  -- Connect to the goal
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  simp_rw [← mul_pow]
  have h_eq : ∀ i, ((a + b) * score_rv gamma i) ^ 2 =
      (E_β.mulVec (fun j => a * score_rv alpha j) i +
       E_α.mulVec (fun j => b * score_rv beta j) i) ^ 2 := by
    intro i; rw [h_key]
  simp_rw [h_eq]
  exact h_contr

end
