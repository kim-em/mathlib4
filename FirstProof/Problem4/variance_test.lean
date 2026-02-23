import Mathlib

set_option maxHeartbeats 1600000

open scoped BigOperators
open Polynomial Finset Real

noncomputable section

-- Using our own definitions to match the project
def boxplusCoeff' (n : ℕ) (p q : ℝ[X]) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    let j := k - i
    (Nat.factorial (n - i) * Nat.factorial (n - j) : ℝ) /
      (Nat.factorial n * Nat.factorial (n - k) : ℝ) *
    (p.coeff (n - i)) * (q.coeff (n - j))

def boxplus' (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (boxplusCoeff' n p q k) * Polynomial.X ^ (n - k)

-- For monic degree-n polynomials, the k=1 coefficient of boxplus gives
-- -(sum of alpha roots + sum of beta roots).
-- This is "mean additivity": the sum of gamma roots = sum(α) + sum(β).

-- Key fact: for k=1,
-- boxplusCoeff' n p q 1 = sum over i=0,1:
--   i=0, j=1: [n! * (n-1)! / (n! * (n-1)!)] * p.coeff(n) * q.coeff(n-1) = q.coeff(n-1)
--   i=1, j=0: [(n-1)! * n! / (n! * (n-1)!)] * p.coeff(n-1) * q.coeff(n) = p.coeff(n-1)
-- So boxplusCoeff' n p q 1 = p.coeff(n-1) + q.coeff(n-1)
-- = p.nextCoeff + q.nextCoeff (for monic degree-n polynomials)

-- The x^(n-1) coefficient of boxplus' is boxplusCoeff' n p q 1.
-- For a monic polynomial x^n - e₁ x^(n-1) + ..., the nextCoeff = -e₁.
-- So boxplus' has nextCoeff = -e₁(α) - e₁(β), meaning sum(γ) = sum(α) + sum(β).

-- Let me verify this for the coefficient formula:
-- For k=2:
-- boxplusCoeff' n p q 2 = sum over i=0,1,2:
--   i=0, j=2: [n!(n-2)!/(n!(n-2)!)] * 1 * q.coeff(n-2) = q.coeff(n-2) = e₂(β)
--   i=1, j=1: [(n-1)!(n-1)!/(n!(n-2)!)] * p.coeff(n-1) * q.coeff(n-1)
--           = [(n-1)/(n)] * (-e₁(α)) * (-e₁(β)) = (n-1)/n * e₁(α)e₁(β)
--   i=2, j=0: [(n-2)!n!/(n!(n-2)!)] * p.coeff(n-2) * 1 = p.coeff(n-2) = e₂(α)
-- So: boxplusCoeff' n p q 2 = e₂(α) + e₂(β) + (n-1)/n * e₁(α)e₁(β)

-- The variance of roots {rᵢ} is:
-- Var = (Σ rᵢ²)/n - ((Σ rᵢ)/n)² = (e₁² - 2e₂)/n - e₁²/n²
--     = e₁²(n-1)/n² - 2e₂/n

-- Var(γ) - Var(α) - Var(β) = (n-1)/n² [e₁(γ)² - e₁(α)² - e₁(β)²]
--                           - 2/n [e₂(γ) - e₂(α) - e₂(β)]
-- = (n-1)/n² * 2e₁(α)e₁(β)  (since e₁(γ) = e₁(α) + e₁(β))
-- - 2/n * (n-1)/n * e₁(α)e₁(β)
-- = 2(n-1)e₁(α)e₁(β)/n² - 2(n-1)e₁(α)e₁(β)/n²
-- = 0. ✓

-- Let me try to prove the k=1 coefficient formula:
lemma boxplusCoeff'_one {n : ℕ} (hn : n ≥ 1) (p q : ℝ[X])
    (hp : p.Monic) (hp_deg : p.natDegree = n)
    (hq : q.Monic) (hq_deg : q.natDegree = n) :
    boxplusCoeff' n p q 1 = p.coeff (n - 1) + q.coeff (n - 1) := by
  have hp_lead : p.coeff n = 1 := by rw [← hp_deg]; exact hp.coeff_natDegree
  have hq_lead : q.coeff n = 1 := by rw [← hq_deg]; exact hq.coeff_natDegree
  have hfact_ne : (↑(Nat.factorial n) * ↑(Nat.factorial (n - 1)) : ℝ) ≠ 0 := by positivity
  unfold boxplusCoeff'
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero,
    hp_lead, hq_lead, one_mul, mul_one, show (1 : ℕ) - 1 = 0 from rfl]
  have h1 : ↑n.factorial * ↑(n - 1).factorial / (↑n.factorial * ↑(n - 1).factorial : ℝ) = 1 :=
    div_self hfact_ne
  have h2 : ↑(n - 1).factorial * ↑n.factorial / (↑n.factorial * ↑(n - 1).factorial : ℝ) = 1 := by
    rw [mul_comm]; exact div_self hfact_ne
  rw [h1, one_mul, h2, one_mul, add_comm]
