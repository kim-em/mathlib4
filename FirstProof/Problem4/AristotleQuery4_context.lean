/-
Context file for Aristotle Query 4: Finite Free Stam Inequality — General n Case

This file collects all results proven by Aristotle (Queries 1-3) that are relevant
to proving the general n case. The key structural result is that finite free cumulants
are additive under ⊞_n (finite free additive convolution).

The missing piece: express 1/Φ_n in terms of finite free cumulants and prove
that the resulting function is superadditive (or concave).

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Polynomial BigOperators Finset Classical

/-! ## Core Definitions -/

/-- Coefficient formula for finite free additive convolution (⊞_n). -/
def boxplus_coeff (n : ℕ) (p q : ℝ[X]) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1),
    let j := k - i
    (Nat.factorial (n - i) * Nat.factorial (n - j) : ℝ) / (Nat.factorial n * Nat.factorial (n - k) : ℝ) *
    (p.coeff (n - i)) * (q.coeff (n - j))

/-- Finite free additive convolution p ⊞_n q. -/
def boxplus (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  Finset.sum (range (n + 1)) (fun k => C (boxplus_coeff n p q k) * X ^ (n - k))

/-- Φ_n(p) = Σ_i (Σ_{j≠i} 1/(r_i - r_j))² for roots r_1,...,r_n of p. -/
def Phi (p : ℝ[X]) : ℝ :=
  let roots := p.roots.toFinset
  ∑ r_i ∈ roots, (∑ r_j ∈ roots.erase r_i, 1 / (r_i - r_j))^2

/-- 1/Φ_n(p), defined as 0 when roots are not distinct or polynomial has degree ≤ 1. -/
def invPhi (p : ℝ[X]) : ℝ :=
  if p.roots.Nodup ∧ p.roots.card > 1 then
    1 / Phi p
  else 0

/-- Φ_n using Fin n → ℝ representation. -/
def phi (n : ℕ) (roots : Fin n → ℝ) : ℝ :=
  ∑ i, (∑ j ∈ univ.erase i, 1 / (roots i - roots j)) ^ 2

/-- Formal statement of the finite free additive convolution. -/
def freeAddConv (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (n + 1), C
    (∑ i ∈ range (k + 1),
      (((n - i).factorial : ℝ) * ((n - (k - i)).factorial : ℝ)) /
      (((n.factorial : ℝ) * ((n - k).factorial : ℝ))) *
      p.coeff (n - i) * q.coeff (n - (k - i))) * X ^ (n - k)

/-! ## Hat Polynomial Transform -/

/-- Hat transform: hat_p(X) = Σ_{i=0}^n coeff(p, n-i) · (n-i)! · X^i -/
def hat_poly (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  ∑ i ∈ range (n + 1), C (p.coeff (n - i) * (n - i).factorial) * X ^ i

/-- Normalized hat polynomial: hat_p / hat_p(0), so constant term = 1. -/
noncomputable def normalized_hat_poly (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (hat_poly n p) * C (1 / (hat_poly n p).coeff 0)

/-! ## Truncated Polynomial Operations -/

/-- Truncated polynomial inverse: Σ_{i=0}^n (1-p)^i, satisfying p · poly_inv ≡ 1 (mod X^{n+1}). -/
noncomputable def poly_inv (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  let q := 1 - p
  ∑ i ∈ range (n + 1), q ^ i

/-- Truncated polynomial logarithm: Σ_{i=0}^n (-1)^i/(i+1) · (p-1)^{i+1}. -/
noncomputable def poly_log (n : ℕ) (p : ℝ[X]) : ℝ[X] :=
  let q := p - 1
  ∑ i ∈ range (n + 1), C ((-1 : ℝ) ^ i / (i + 1 : ℝ)) * q ^ (i + 1)

/-! ## Finite Free Cumulants -/

/-- k-th finite free cumulant of p: coefficient of X^k in poly_log(normalized_hat_poly(p)). -/
noncomputable def finite_free_cumulant (n : ℕ) (p : ℝ[X]) (k : ℕ) : ℝ :=
  (poly_log n (normalized_hat_poly n p)).coeff k

/-! ## Centered Polynomial Predicate -/

/-- A polynomial is centered if it is monic, has degree n, and zero trace (coeff of x^{n-1} = 0). -/
def is_centered (n : ℕ) (p : ℝ[X]) : Prop :=
  p.Monic ∧ p.natDegree = n ∧ p.coeff (n - 1) = 0

/-! ## PROVEN RESULTS (General n) -/

/-- Φ_n = 2 Σ_{i<j} 1/(λ_i - λ_j)² (cross terms cancel). PROVEN for all n. -/
theorem phi_eq_sum_sq_diff (n : ℕ) (roots : Fin n → ℝ) (h_distinct : Function.Injective roots) :
    phi n roots = 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / (roots i - roots j) ^ 2 := by
  sorry -- Proven by Aristotle (Query 3), ~60 line proof

/-- Φ_n is translation invariant. PROVEN for all n. -/
theorem phi_translation_invariant (n : ℕ) (roots : Fin n → ℝ) (c : ℝ) :
    phi n (fun i => roots i + c) = phi n roots := by
  sorry -- Proven by Aristotle (Query 3)

/-- Φ_n scales by 1/c² when roots are scaled by c. PROVEN for all n. -/
theorem phi_scaling (n : ℕ) (roots : Fin n → ℝ) (c : ℝ) (hc : c ≠ 0) :
    phi n (fun i => c * roots i) = (1 / c ^ 2) * phi n roots := by
  sorry -- Proven by Aristotle (Query 3)

/-- Phi from polynomial roots equals phi from Fin n roots. PROVEN for all n. -/
theorem Phi_eq_phi (n : ℕ) (roots : Fin n → ℝ) (h_distinct : Function.Injective roots) :
    Phi (∏ i, (X - C (roots i))) = phi n roots := by
  sorry -- Proven by Aristotle (Query 3)

/-- The (n-1)-th coefficient of ⊞_n is additive. PROVEN for all n > 0. -/
theorem boxplus_coeff_n_minus_1 (n : ℕ) (hn : 0 < n) (p q : ℝ[X])
    (hp : p.natDegree = n) (hq : q.natDegree = n)
    (hp_monic : p.Monic) (hq_monic : q.Monic) :
    (boxplus n p q).coeff (n - 1) = p.coeff (n - 1) + q.coeff (n - 1) := by
  sorry -- Proven by Aristotle (Query 3)

/-- For centered polynomials, the (n-2)-th coefficient of ⊞_n is additive. PROVEN for all n ≥ 2. -/
theorem boxplus_coeff_n_minus_2_of_centered (n : ℕ) (hn : 2 ≤ n) (p q : ℝ[X])
    (hp : p.natDegree = n) (hq : q.natDegree = n)
    (hp_monic : p.Monic) (hq_monic : q.Monic)
    (hp_centered : p.coeff (n - 1) = 0) (hq_centered : q.coeff (n - 1) = 0) :
    (boxplus n p q).coeff (n - 2) = p.coeff (n - 2) + q.coeff (n - 2) := by
  sorry -- Proven by Aristotle (Query 3)

/-- Centered polynomials are closed under ⊞_n. PROVEN for all n. -/
theorem boxplus_centered_is_centered (n : ℕ) (p q : ℝ[X])
    (hp : is_centered n p) (hq : is_centered n q) :
    is_centered n (boxplus n p q) := by
  sorry -- Proven by Aristotle (Query 2)

/-- Hat transform key identity: hat(p ⊞_n q) ≡ (1/n!) · hat(p) · hat(q) (mod X^{n+1}). PROVEN. -/
theorem hat_poly_boxplus_coeff (n : ℕ) (p q : ℝ[X]) (k : ℕ) (hk : k ≤ n) :
    (hat_poly n (boxplus n p q)).coeff k =
    (1 / (n.factorial : ℝ)) * ((hat_poly n p) * (hat_poly n q)).coeff k := by
  sorry -- Proven by Aristotle (Query 3)

/-- Truncated polynomial inverse works: p · poly_inv(p) ≡ 1 (mod X^{n+1}). PROVEN. -/
theorem poly_inv_mul_mod (n : ℕ) (p : ℝ[X]) (hp : p.coeff 0 = 1) :
    (p * poly_inv n p) % (X ^ (n + 1)) = 1 := by
  sorry -- Proven by Aristotle (Query 3)

/-- Truncated inverse is unique. PROVEN. -/
theorem poly_inv_unique (n : ℕ) (p q : ℝ[X]) (hp : p.coeff 0 = 1)
    (h : (p * q) % (X ^ (n + 1)) = 1) :
    q % (X ^ (n + 1)) = (poly_inv n p) % (X ^ (n + 1)) := by
  sorry -- Proven by Aristotle (Query 3)

/-- Truncated log derivative is the logarithmic derivative. PROVEN. -/
theorem poly_log_derivative (n : ℕ) (p : ℝ[X]) (hp : p.coeff 0 = 1) :
    (Polynomial.derivative (poly_log n p)) % (X ^ n) =
    ((Polynomial.derivative p) * (poly_inv n p)) % (X ^ n) := by
  sorry -- Proven by Aristotle (Query 3)

/-- Truncated log of a product is additive modulo X^n. PROVEN. -/
theorem poly_log_derivative_mul_mod (n : ℕ) (p q : ℝ[X])
    (hp : p.coeff 0 = 1) (hq : q.coeff 0 = 1) :
    (Polynomial.derivative (poly_log n (p * q))) % (X ^ n) =
    ((Polynomial.derivative (poly_log n p)) + (Polynomial.derivative (poly_log n q))) % (X ^ n) := by
  sorry -- Proven by Aristotle (Query 3)

/-- The normalized hat polynomial has constant term 1. PROVEN. -/
theorem normalized_hat_poly_coeff_zero (n : ℕ) (p : ℝ[X])
    (hp : p.natDegree = n) (hp_monic : p.Monic) :
    (normalized_hat_poly n p).coeff 0 = 1 := by
  sorry -- Proven by Aristotle (Query 3)

/-- ⭐ KEY RESULT: Finite free cumulants are additive under ⊞_n. PROVEN for all n. -/
theorem finite_free_cumulant_additive (n : ℕ) (p q : ℝ[X]) (k : ℕ)
    (hk : k ≤ n) (hk0 : 0 < k)
    (hp : p.natDegree = n) (hq : q.natDegree = n)
    (hp_monic : p.Monic) (hq_monic : q.Monic) :
    finite_free_cumulant n (boxplus n p q) k =
    finite_free_cumulant n p k + finite_free_cumulant n q k := by
  sorry -- Proven by Aristotle (Query 3)

/-! ## PROVEN RESULTS (Small cases) -/

/-- n=2: 1/Φ_2 is additive under ⊞_2 (EQUALITY). PROVEN. -/
theorem conjecture_n_2 (p q : ℝ[X])
    (hp_monic : p.Monic) (hq_monic : q.Monic)
    (hp_deg : p.natDegree = 2) (hq_deg : q.natDegree = 2)
    (hp_real : p.Splits (RingHom.id ℝ)) (hq_real : q.Splits (RingHom.id ℝ)) :
    invPhi (boxplus 2 p q) = invPhi p + invPhi q := by
  sorry -- Proven by Aristotle (Query 1-2)

/-- n=3: Finite free Stam inequality holds for reduced cubics. PROVEN. -/
theorem conjecture_n_3_reduced (a1 b1 a2 b2 : ℝ)
    (h_real1 : (X^3 + C a1 * X + C b1).Splits (RingHom.id ℝ))
    (h_nodup1 : (X^3 + C a1 * X + C b1).roots.Nodup)
    (h_real2 : (X^3 + C a2 * X + C b2).Splits (RingHom.id ℝ))
    (h_nodup2 : (X^3 + C a2 * X + C b2).roots.Nodup)
    (h_real3 : (X^3 + C (a1+a2) * X + C (b1+b2)).Splits (RingHom.id ℝ))
    (h_nodup3 : (X^3 + C (a1+a2) * X + C (b1+b2)).roots.Nodup) :
    invPhi (X^3 + C (a1+a2) * X + C (b1+b2)) ≥
    invPhi (X^3 + C a1 * X + C b1) + invPhi (X^3 + C a2 * X + C b2) := by
  sorry -- Proven by Aristotle (Query 2-3), via Cauchy-Schwarz

/-- n=3: Auxiliary Cauchy-Schwarz inequality. PROVEN. -/
theorem n3_inequality (b1 b2 u1 u2 : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) :
    (b1 + b2)^2 / (u1 + u2)^2 ≤ b1^2 / u1^2 + b2^2 / u2^2 := by
  sorry -- Proven by Aristotle (Query 2)

/-- n=3: Superadditivity of 1/Φ_3 formula in coefficients. PROVEN. -/
theorem invPhi_deg3_superadditive (a1 b1 a2 b2 : ℝ) (ha1 : a1 < 0) (ha2 : a2 < 0) :
    let f := fun a b => (-4 * a^3 - 27 * b^2) / (18 * a^2)
    f (a1 + a2) (b1 + b2) ≥ f a1 b1 + f a2 b2 := by
  sorry -- Proven by Aristotle (Query 3)

/-! ## FORMAL PROBLEM STATEMENT -/

/-- The Finite Free Stam Inequality: 1/Φ_n(p ⊞_n q) ≥ 1/Φ_n(p) + 1/Φ_n(q). -/
theorem first_proof_problem4 (n : ℕ) (hn : 0 < n)
    (rp rq rpq : Fin n → ℝ)
    (hp : Function.Injective rp) (hq : Function.Injective rq) (hpq : Function.Injective rpq)
    (hconv : (∏ i : Fin n, (X - C (rpq i))) =
             freeAddConv n (∏ i : Fin n, (X - C (rp i))) (∏ i : Fin n, (X - C (rq i))))
    : 1 / phi n rpq ≥ 1 / phi n rp + 1 / phi n rq := by
  sorry
