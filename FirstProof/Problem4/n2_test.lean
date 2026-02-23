import Mathlib

set_option maxHeartbeats 800000

open scoped BigOperators
open Polynomial Finset Real

noncomputable section

/-- Coefficient of the finite free additive convolution ⊞_n. -/
def ffc_coeff (n : ℕ) (p q : ℝ[X]) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    let j := k - i
    (Nat.factorial (n - i) * Nat.factorial (n - j) : ℝ) /
      (Nat.factorial n * Nat.factorial (n - k) : ℝ) *
    (p.coeff (n - i)) * (q.coeff (n - j))

/-- The finite free additive convolution p ⊞_n q. -/
def ffc (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (ffc_coeff n p q k) * Polynomial.X ^ (n - k)

def phi_rv {n : ℕ} (roots : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (∑ j ∈ Finset.univ.erase i, 1 / (roots i - roots j)) ^ 2

-- For n=2, we can compute everything explicitly.
-- alpha = ![a₁, a₂], beta = ![b₁, b₂], gamma = ![g₁, g₂]
-- phi_rv alpha = (1/(a₁-a₂))² + (1/(a₂-a₁))² = 2/(a₁-a₂)²
-- The boxplus for n=2 gives (g₁-g₂)² = (a₁-a₂)² + (b₁-b₂)²
-- (variance additivity)
-- Then the inequality (a+b)² · 2/(X+Y) ≤ a² · 2/X + b² · 2/Y
-- where X = (a₁-a₂)², Y = (b₁-b₂)²
-- follows from (aY - bX)² ≥ 0.

-- Let me first check: for n=2, what does ffc do to the k=2 coefficient?
-- ffc_coeff 2 p q 2 = Σ_{i=0}^{2} [(2-i)!(2-j)! / (2! · 0!)] p.coeff(2-i) q.coeff(2-j)
-- where j = 2-i
-- i=0, j=2: [2!·0!/(2!·0!)] · p.coeff(2) · q.coeff(0) = 1 · 1 · q.coeff(0)
-- i=1, j=1: [1!·1!/(2!·0!)] · p.coeff(1) · q.coeff(1) = (1/2) · p.coeff(1) · q.coeff(1)
-- i=2, j=0: [0!·2!/(2!·0!)] · p.coeff(0) · q.coeff(2) = 1 · p.coeff(0) · 1

-- For p = (X - a₁)(X - a₂) = X² - (a₁+a₂)X + a₁a₂:
--   p.coeff(2) = 1, p.coeff(1) = -(a₁+a₂), p.coeff(0) = a₁a₂
-- For q = (X - b₁)(X - b₂) = X² - (b₁+b₂)X + b₁b₂:
--   q.coeff(2) = 1, q.coeff(1) = -(b₁+b₂), q.coeff(0) = b₁b₂

-- ffc_coeff 2 p q 2 = b₁b₂ + (1/2)(a₁+a₂)(b₁+b₂) + a₁a₂

-- The ffc polynomial is:
-- X² + ffc_coeff(2,p,q,1) · X + ffc_coeff(2,p,q,2)
-- ffc_coeff(2,p,q,1) = -(a₁+a₂) + -(b₁+b₂) = -(a₁+a₂+b₁+b₂)
-- So roots sum is a₁+a₂+b₁+b₂.

-- ffc_coeff(2,p,q,2) = a₁a₂ + b₁b₂ + (1/2)(a₁+a₂)(b₁+b₂)
-- = product of roots of gamma

-- (g₁-g₂)² = (g₁+g₂)² - 4g₁g₂
-- = (a₁+a₂+b₁+b₂)² - 4(a₁a₂ + b₁b₂ + (1/2)(a₁+a₂)(b₁+b₂))
-- = (a₁+a₂)² + 2(a₁+a₂)(b₁+b₂) + (b₁+b₂)² - 4a₁a₂ - 4b₁b₂ - 2(a₁+a₂)(b₁+b₂)
-- = (a₁+a₂)² - 4a₁a₂ + (b₁+b₂)² - 4b₁b₂
-- = (a₁-a₂)² + (b₁-b₂)²

-- So variance additivity holds for n=2. Now let me try to prove the inequality.

-- Simplified form for n=2: need to show
-- (a+b)² * 2/(X+Y) ≤ a² * 2/X + b² * 2/Y
-- where X = (α₁-α₂)² > 0, Y = (β₁-β₂)² > 0

-- This follows from (aY - bX)² ≥ 0, expanded and rearranged.

-- Let me try the simplest possible approach:
example (a b X Y : ℝ) (hX : X > 0) (hY : Y > 0) :
    (a + b) ^ 2 / (X + Y) ≤ a ^ 2 / X + b ^ 2 / Y := by
  have hXY : X + Y > 0 := by linarith
  rw [div_add_div _ _ (ne_of_gt hX) (ne_of_gt hY)]
  rw [div_le_div_iff₀ hXY (mul_pos hX hY)]
  nlinarith [sq_nonneg (a * Y - b * X)]
