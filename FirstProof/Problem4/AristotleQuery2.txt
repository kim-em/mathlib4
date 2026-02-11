/-
FINITE FREE STAM INEQUALITY — Second Aristotle Submission

Problem 4 from "First Proof" (arXiv:2602.05192):
For monic real-rooted degree-n polynomials p, q with distinct roots,
prove that 1/Φ_n(p ⊞_n q) ≥ 1/Φ_n(p) + 1/Φ_n(q).

This is the finite polynomial analog of the free Stam inequality
(Mingo-Speicher, Theorem 19 / equation 8.19).

STATUS:
- n=1: PROVEN (trivial — Phi undefined for single root)
- n=2: PROVEN AS EQUALITY (1/Φ₂ = discriminant/2, discriminant additive under ⊞₂)
- n=3: KEY INSIGHT BELOW — reduces to Cauchy-Schwarz
- General n: OPEN — see proof strategies below

=== SECTION A: PROBLEM DEFINITION AND PRIOR RESULTS ===

DEFINITIONS:
- Φ_n(p) = Σ_i (Σ_{j≠i} 1/(λ_i - λ_j))²  for roots λ_1,...,λ_n of p
- (p ⊞_n q)(x) = Σ_{k=0}^n c_k x^{n-k} where
    c_k = Σ_{i+j=k} ((n-i)!(n-j)!)/(n!(n-k)!) · a_i · b_j

KEY SIMPLIFICATION (for all n):
  Φ_n = 2 Σ_{i<j} 1/(λ_i - λ_j)²
  (Cross terms cancel: Σ_i (Σ_{j≠i} 1/(λ_i-λ_j))² = 2 Σ_{i<j} 1/(λ_i-λ_j)²)

DERIVATIVE FORM:
  Φ_n(p) = Σ_i [p''(λ_i)/(2p'(λ_i))]²
  where p'(λ_i) = Π_{j≠i}(λ_i - λ_j) and p''(λ_i)/2 = Σ_{j≠i} Π_{k≠i,j}(λ_i - λ_k)

GRADIENT INTERPRETATION:
  Define ξ_i = Σ_{j≠i} 1/(λ_i - λ_j) = (1/2) ∂/∂λ_i log Δ(λ)
  where Δ(λ) = Π_{i<j} (λ_i - λ_j)² is the (squared) Vandermonde determinant.
  Then Φ_n = Σ_i ξ_i² = |ξ|² and 1/Φ_n = 1/|ξ|².

=== SECTION B: PROVEN RESULTS ===

THEOREM (n=2, EQUALITY): For monic quadratic p, q with distinct roots:
  1/Φ₂(p ⊞₂ q) = 1/Φ₂(p) + 1/Φ₂(q)
Proof: For p(x) = x² + bx + c, we have Φ₂ = 2/(b² - 4c), so 1/Φ₂ = (b² - 4c)/2 = Δ/2.
Under ⊞₂: coefficients add (b₁+b₂, c₁+c₂+b₁b₂/2), and the discriminant is additive:
  Δ(p ⊞₂ q) = Δ(p) + Δ(q). Hence equality.

THEOREM (n=3, NEW — Cauchy-Schwarz):
For reduced cubic p(x) = x³ + ax + b with a < 0 and discriminant Δ = -4a³ - 27b² > 0:
  Φ₃ = 18a²/Δ,  so  1/Φ₃ = Δ/(18a²) = (-4a³ - 27b²)/(18a²)

Rewrite with u = -a > 0:
  1/Φ₃ = (4u³ - 27b²)/(18u²) = (2/9)u - (3/2)b²/u²

Under ⊞₃ for reduced cubics: the coefficients (a₁, b₁) and (a₂, b₂) ADD:
  a₃ = a₁ + a₂,  b₃ = b₁ + b₂  (since the x² coefficient is 0 for both)

So we need: F(u₁+u₂, b₁+b₂) ≥ F(u₁,b₁) + F(u₂,b₂)
where F(u,b) = (2/9)u - (3/2)b²/u².

The linear part (2/9)u is additive. For the concave part, we need:
  (b₁+b₂)²/(u₁+u₂)² ≤ b₁²/u₁² + b₂²/u₂²

This is Cauchy-Schwarz! Specifically, for positive u₁, u₂:
  (b₁/u₁ · u₁/(u₁+u₂) + b₂/u₂ · u₂/(u₁+u₂))² ≤ (b₁/u₁)² + (b₂/u₂)²
by convexity of x², or equivalently by:
  (b₁u₂ - b₂u₁)² ≥ 0  ⟹  b₁²u₂² + b₂²u₁² ≥ 2b₁b₂u₁u₂
  ⟹  (b₁² + b₂²)(u₁² + u₂²) + 2u₁u₂(b₁² + b₂²) ≥ (b₁+b₂)²(u₁² + 2u₁u₂ + u₂²)/(u₁+u₂)²
This completes the n=3 case. QED

=== SECTION C: KEY IDENTITIES FROM THE LITERATURE ===

1. RANDOM MATRIX REPRESENTATION (Marcus-Spielman-Srivastava, Thm 1.2):
   p ⊞_d q = E_Q[det(xI - A - QBQ*)]
   where A = diag(λ₁,...,λ_d), B = diag(μ₁,...,μ_d), Q uniform over O(d).

2. U-TRANSFORM (Marcus, Lemma 3.4):
   [p ⊞_d q](x) = E{(x - S - T)^d}
   where S, T are INDEPENDENT random variables (U-transforms of the root distributions).
   This reduces finite free convolution to ordinary addition of independent r.v.s!

3. FINITE FREE R-TRANSFORM (Marcus, §4):
   R-transform is ADDITIVE under ⊞_d: R_{p⊞q}^(d) = R_p^(d) + R_q^(d)
   The finite free cumulants κ_k^(d) are the coefficients of this R-transform.

4. HERMITE EQUALITY CASE:
   a^d H_d(x/a) ⊞_d b^d H_d(x/b) = c^d H_d(x/c) where c = √(a²+b²)
   For Hermite polynomials (equally-spaced roots), we expect EQUALITY.

5. PRODUCT OF DERIVATIVES AT ROOTS (for reduced cubic):
   Π_i (3λ_i² + a) = 4a³ + 27b²
   (This is related to the discriminant of the derivative.)

=== SECTION D: PROOF STRATEGIES TO ATTEMPT ===

STRATEGY 1 — Finite Free Cumulants / R-Transform (MOST PROMISING):
The R-transform is additive: κ_k(p ⊞_d q) = κ_k(p) + κ_k(q).
Express 1/Φ_n as a function of the finite free cumulants κ₁, κ₂, ..., κ_n.
Then prove that this function is SUPERADDITIVE (or concave) in cumulant space.

For n=2: κ₁ = -b (linear coeff), κ₂ = b²-2c. Then 1/Φ₂ = κ₂/2 is linear — hence additive.
For n=3: need to express 1/Φ₃ in terms of κ₁, κ₂, κ₃ and show superadditivity.

The additivity of R-transform reduces the problem to showing f(κ+κ') ≥ f(κ) + f(κ')
for the appropriate function f of cumulant vectors.

STRATEGY 2 — Discriminant / Resultant Approach:
For n=2: 1/Φ₂ = Δ₂/2 where Δ₂ is the discriminant.
For n=3: 1/Φ₃ = Δ₃/(18a²) where Δ₃ = -4a³ - 27b².

Conjecture: For general n, 1/Φ_n = Δ_n / (some explicit polynomial in coefficients).

The discriminant Δ_n = Res(p, p')/leading coeff. If we can express 1/Φ_n via
discriminant-like quantities and track their behavior under ⊞_n, we may get the inequality.

For reduced polynomials (zero trace): p(x) = x^n + a_{n-2}x^{n-2} + ... + a_0.
Under ⊞_n of reduced polynomials: coefficients ADD (since the ⊞_n formula for
c_k with i+j=k gives c_k = a_i + b_i when one of i,j is 0, plus correction terms).

STRATEGY 3 — U-Transform + Classical Stam:
Since [p ⊞_d q](x) = E{(x-S-T)^d} with S,T independent:
- The roots of p ⊞_d q are determined by the sum S+T of independent r.v.s
- Φ_n is related to Fisher information of the empirical root distribution
- The classical Stam inequality 1/J(X+Y) ≥ 1/J(X) + 1/J(Y) applies to Fisher info

Key challenge: Make the connection between Φ_n (discrete root-based) and the
Fisher information of the distributions of S and T precise enough to transfer
the classical inequality.

STRATEGY 4 — Random Matrix + Convexity (Jensen's inequality):
p ⊞_n q = E_Q[det(xI - A - QBQ*)].
The roots of det(xI - A - QBQ*) are the eigenvalues of A + QBQ*.

If Φ_n is a CONVEX function of the eigenvalue tuple, then by Jensen:
  Φ_n(p ⊞_n q) ≤ E_Q[Φ_n(eigenvalues of A+QBQ*)]

Combined with some averaging argument over Q, this could give the desired bound.
Note: 1/Φ_n being concave in eigenvalues would directly give:
  1/Φ_n(E_Q[...]) ≥ E_Q[1/Φ_n(...)] ≥ ... (need to connect to 1/Φ(p) + 1/Φ(q))

STRATEGY 5 — Electrostatic Energy:
Φ_n = 2 Σ_{i<j} 1/(λ_i-λ_j)² is the electrostatic energy of unit charges on the line.
Free convolution is known to "spread" roots apart (interlacing results from MSS).
Spreading charges apart DECREASES the energy Φ and INCREASES 1/Φ.

To formalize: Show that the root-spreading effect of ⊞_n is strong enough
that 1/Φ_n satisfies the desired superadditivity.

STRATEGY 6 — Finite Conjugate Variables:
The infinite free Stam inequality (Mingo-Speicher Thm 19) is proved using
conjugate systems / free score functions. Define finite analogs:

For the empirical spectral measure μ_p = (1/n)Σ δ_{λ_i}, the Cauchy transform is
G(z) = (1/n) Σ 1/(z-λ_i). Then ξ_i = Σ_{j≠i} 1/(λ_i-λ_j) plays the role
of the "conjugate variable" or "free score" at λ_i.

The infinite proof uses: Φ(μ⊞ν) = Var_μ(ξ^μ(X)) where ξ^μ is the score.
For the sum X+Y with X⊥Y (free): ξ^{X+Y}(x) = E[ξ^X(x) | X+Y].
Then Φ(X+Y) = Var(ξ^{X+Y}) ≤ Var(ξ^X) = Φ(X) by conditional variance inequality.

Translating to finite setting: use the random matrix representation
A + QBQ* and conditional expectation over Q.

STRATEGY 7 — De Bruijn / Heat Flow:
Define the finite free heat flow: p_t = p ⊞_n H_t where H_t = t^n H_n(x/t).
As t → ∞, this converges to the "free Gaussian" (Hermite polynomial).

Study d/dt [1/Φ_n(p_t)]. If this is non-decreasing, then the heat flow
monotonically increases 1/Φ_n. Combined with the semigroup property of ⊞_n,
this may imply the Stam inequality.

STRATEGY 8 — Induction on n:
Base cases n=1,2 are done. For the inductive step n → n+1:
- Take the derivative: p' has degree n with roots at critical points of p
- Relate Φ_{n+1}(p) to Φ_n(p') plus correction terms
- Use the fact that derivative and ⊞ interact well

Warning: No clean relation between Φ_n and Φ_{n-1} has been found.
However, the derivative quotient form Φ_n = Σ [p''/2p']² suggests
that the derivative might still be useful.

=== SECTION E: DETAILED COMPUTATIONS FOR GENERAL n ===

For a monic polynomial p(x) = Π_i (x - λ_i):
- p'(λ_i) = Π_{j≠i} (λ_i - λ_j)
- (log p)'(x) = Σ_i 1/(x - λ_i) = G(x) (partial fraction / Cauchy transform)
- (log p)''(x) = -Σ_i 1/(x - λ_i)²
- p''(λ_i)/p'(λ_i) = 2 Σ_{j≠i} 1/(λ_i - λ_j) = 2ξ_i

So Φ_n = Σ_i ξ_i² where ξ_i = p''(λ_i)/(2p'(λ_i)).

POWER SUM CONNECTION:
Let s_k(i) = Σ_{j≠i} (λ_i - λ_j)^{-k} for k ≥ 1.
Then ξ_i = s_1(i) and Φ_n = Σ_i s_1(i)².

For the convolution result: Under ⊞_n, the elementary symmetric polynomials
e_k of the roots transform via the convolution formula. The power sums p_k
transform less cleanly.

COEFFICIENT BEHAVIOR UNDER ⊞_n:
For reduced (zero-trace) polynomials p(x) = x^n + a_{n-2}x^{n-2} + ... + a_0:
- k=1: c_1 = 0 (both traces are 0)
- k=2: c_2 = a_{n-2} + b_{n-2} (the sub-leading coefficient adds!)
- k≥3: c_k involves cross terms

The fact that sub-leading coefficients add linearly is crucial.
For n=2: only k=2 matters → pure additivity → equality.
For n=3: k=2 (a-coefficient) adds, k=3 (b-coefficient) also adds for reduced cubics.

For general n with k≥3: the cross terms in c_k = Σ_{i+j=k} f(n,i,j) a_i b_j
introduce nonlinear mixing that makes the analysis harder.

=== PRIORITIES FOR ARISTOTLE ===

1. FIRST: Try to prove the n=3 case formally, using the Cauchy-Schwarz argument
   described in Section B. The informal proof is complete.

2. SECOND: Try Strategy 1 (cumulants). Express 1/Φ_n in terms of finite free
   cumulants and prove superadditivity.

3. THIRD: Try Strategy 6 (conjugate variables). This mirrors the infinite proof
   most closely.

4. FOURTH: Try Strategy 4 (random matrix + Jensen). This uses the most
   concrete representation.

=== SECTION F: PREVIOUS ARISTOTLE OUTPUT (930 lines) ===

The following is the complete output from the previous Aristotle run.
Key proven results you can REUSE:
- boxplus_coeff, boxplus, Phi, invPhi (definitions)
- conjecture_n_1 (n=1 case)
- conjecture_n_2 (n=2 case, equality)
- boxplus_deg2_coeffs, discrim_boxplus_deg2
- Phi_deg3_reduced_eq (formula for Phi of reduced cubic)
- cubic_distinct_real_roots_implies_a_neg
- cubic_splits_of_discrim_pos
- invPhi_deg3_inequality (partial; used nlinarith)
- boxplus_deg3_reduced_coeffs, boxplus_deg3_reduced_eq
- Many helper lemmas about cubic discriminants, Vieta's formulas, etc.

--- BEGIN PREVIOUS OUTPUT ---
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Checking availability of Finset.sum and Finset.antidiagonal
-/
open Finset
#check Finset.sum
#check Finset.antidiagonal
#check (Finset.antidiagonal 5 : Finset (ℕ × ℕ))

/-
Defining the coefficient formula for the boxplus convolution.
-/
open Polynomial BigOperators Finset Classical
open scoped BigOperators

def boxplus_coeff (n : ℕ) (p q : ℝ[X]) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1),
    let j := k - i
    (Nat.factorial (n - i) * Nat.factorial (n - j) : ℝ) / (Nat.factorial n * Nat.factorial (n - k) : ℝ) *
    (p.coeff (n - i)) * (q.coeff (n - j))

/-
Defining the boxplus polynomial.
-/
open Polynomial BigOperators Finset Classical
open scoped BigOperators

def boxplus (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  Finset.sum (range (n + 1)) (fun k => C (boxplus_coeff n p q k) * X ^ (n - k))

/-
Defining the Phi functional with safe variable names.
-/
open Polynomial BigOperators Finset Classical
open scoped BigOperators

def Phi (p : ℝ[X]) : ℝ :=
  let roots := p.roots.toFinset
  ∑ r_i ∈ roots, (∑ r_j ∈ roots.erase r_i, 1 / (r_i - r_j))^2

/-
Defining the inverse Phi functional.
-/
open Polynomial BigOperators Finset Classical
open scoped BigOperators

def invPhi (p : ℝ[X]) : ℝ :=
  if p.roots.Nodup ∧ p.roots.card > 1 then
    1 / Phi p
  else 0

/-
Marking definitions as irreducible to help the ATP.
-/
attribute [irreducible] boxplus Phi invPhi

/-
Checking for discrim
-/
#check discrim

/-
For a monic real-rooted polynomial of degree 2, 1/Phi(p) is half the discriminant.
-/
lemma Phi_deg2 (p : ℝ[X]) (h_monic : p.Monic) (h_deg : p.natDegree = 2) (h_real : p.Splits (RingHom.id ℝ)) :
  invPhi p = (discrim 1 (p.coeff 1) (p.coeff 0)) / 2 := by
    -- Let's denote the roots of $p$ as $r_1$ and $r_2$.
    obtain ⟨r1, r2, hr⟩ : ∃ r1 r2 : ℝ, p = Polynomial.C 1 * (Polynomial.X - Polynomial.C r1) * (Polynomial.X - Polynomial.C r2) := by
      rw [ Polynomial.eq_prod_roots_of_monic_of_splits_id h_monic h_real ];
      -- Since $p$ is a monic polynomial of degree 2, its roots form a multiset of cardinality 2.
      have h_card : Multiset.card p.roots = 2 := by
        rw [ Polynomial.splits_iff_card_roots ] at h_real ; aesop;
      rw [ Multiset.card_eq_two ] at h_card ; aesop;
    unfold invPhi discrim;
    by_cases h : r1 = r2 <;> simp_all +decide [ Polynomial.roots_mul, Polynomial.X_sub_C_ne_zero ];
    · norm_num [ sq, Polynomial.coeff_one, Polynomial.coeff_X, mul_sub ] ; ring;
    · unfold Phi;
      rw [ Polynomial.roots_mul <| mul_ne_zero ( Polynomial.X_sub_C_ne_zero _ ) ( Polynomial.X_sub_C_ne_zero _ ), Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C ] ; norm_num [ h, Polynomial.coeff_one, Polynomial.coeff_X, mul_sub ] ; ring;
      rw [ inv_inv ] ; ring

/-
Calculating the coefficients of the boxplus product for n=2.
-/
lemma boxplus_deg2_coeffs (p q : ℝ[X])
  (hp_monic : p.Monic) (hq_monic : q.Monic)
  (hp_deg : p.natDegree = 2) (hq_deg : q.natDegree = 2) :
  (boxplus 2 p q).coeff 2 = 1 ∧
  (boxplus 2 p q).coeff 1 = p.coeff 1 + q.coeff 1 ∧
  (boxplus 2 p q).coeff 0 = p.coeff 0 + q.coeff 0 + 1/2 * p.coeff 1 * q.coeff 1 := by
    unfold boxplus;
    norm_num [ Finset.sum_range_succ, boxplus_coeff ];
    simp_all +decide [ Polynomial.Monic.def, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some ];
    constructor <;> ring

/-
The discriminant of the boxplus of two monic quadratic polynomials is the sum of their discriminants.
-/
lemma discrim_boxplus_deg2 (p q : ℝ[X])
  (hp_monic : p.Monic) (hq_monic : q.Monic)
  (hp_deg : p.natDegree = 2) (hq_deg : q.natDegree = 2) :
  discrim 1 ((boxplus 2 p q).coeff 1) ((boxplus 2 p q).coeff 0) =
  discrim 1 (p.coeff 1) (p.coeff 0) + discrim 1 (q.coeff 1) (q.coeff 0) := by
    obtain ⟨h2, h1, h0⟩ := boxplus_deg2_coeffs p q hp_monic hq_monic hp_deg hq_deg;
    unfold discrim;
    rw [ h1, h0 ];
    ring

/-
A quadratic polynomial with non-negative discriminant splits over the reals.
-/
lemma splits_of_discrim_nonneg_deg2 (p : ℝ[X]) (h_deg : p.natDegree = 2) (h_disc : discrim (p.coeff 2) (p.coeff 1) (p.coeff 0) ≥ 0) : p.Splits (RingHom.id ℝ) := by
  rw [ Polynomial.splits_iff_card_roots ];
  rw [ show p = Polynomial.C ( p.coeff 2 ) * ( Polynomial.X - Polynomial.C ( ( -p.coeff 1 - Real.sqrt ( discrim ( p.coeff 2 ) ( p.coeff 1 ) ( p.coeff 0 ) ) ) / ( 2 * p.coeff 2 ) ) ) * ( Polynomial.X - Polynomial.C ( ( -p.coeff 1 + Real.sqrt ( discrim ( p.coeff 2 ) ( p.coeff 1 ) ( p.coeff 0 ) ) ) / ( 2 * p.coeff 2 ) ) ) from _ ];
  · rw [ Polynomial.natDegree_mul', Polynomial.natDegree_mul' ] <;> norm_num;
    · rw [ Polynomial.roots_mul, Polynomial.roots_mul ];
      · rw [ Polynomial.roots_C, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C ] ; norm_num;
      · exact mul_ne_zero ( Polynomial.C_ne_zero.mpr <| by { rw [ ← h_deg, Polynomial.coeff_natDegree ] ; aesop } ) <| Polynomial.X_sub_C_ne_zero _;
      · exact mul_ne_zero ( mul_ne_zero ( Polynomial.C_ne_zero.mpr <| by rw [ ← h_deg, Polynomial.coeff_natDegree ] ; aesop ) <| Polynomial.X_sub_C_ne_zero _ ) <| Polynomial.X_sub_C_ne_zero _;
    · rw [ ← h_deg, Polynomial.coeff_natDegree ] ; aesop;
    · rw [ ← h_deg, Polynomial.coeff_natDegree ] ; aesop;
  · convert Polynomial.as_sum_range_C_mul_X_pow p using 1 ; norm_num [ Finset.sum_range_succ', h_deg ] ; ring;
    refine' Polynomial.funext fun x => _ ; norm_num ; ring;
    by_cases h : p.coeff 2 = 0 <;> simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm ];
    · exact absurd h ( by rw [ ← h_deg, Polynomial.coeff_natDegree ] ; aesop );
    · unfold discrim; ring_nf at *; aesop;

/-
A quadratic polynomial that splits over the reals has non-negative discriminant.
-/
lemma discrim_nonneg_of_splits_deg2 (p : ℝ[X]) (h_deg : p.natDegree = 2) (h_splits : p.Splits (RingHom.id ℝ)) : discrim (p.coeff 2) (p.coeff 1) (p.coeff 0) ≥ 0 := by
  simp_all +decide [ discrim ];
  rw [ Polynomial.splits_iff_card_roots ] at h_splits;
  -- Since $p$ is a quadratic polynomial with real roots, we can write it as $p(x) = a(x - r_1)(x - r_2)$ for some real numbers $r_1$ and $r_2$.
  obtain ⟨r1, r2, hr⟩ : ∃ r1 r2 : ℝ, p = Polynomial.C (p.coeff 2) * (Polynomial.X - Polynomial.C r1) * (Polynomial.X - Polynomial.C r2) := by
    -- Since $p$ is a quadratic polynomial with real roots, we can write it as $p(x) = a(x - r_1)(x - r_2)$ for some real numbers $r_1$ and $r_2$.
    obtain ⟨r1, r2, hr⟩ : ∃ r1 r2 : ℝ, p.roots = {r1, r2} := by
      exact Multiset.card_eq_two.mp ( h_splits.trans h_deg );
    use r1, r2;
    convert Polynomial.eq_prod_roots_of_splits_id <| Polynomial.splits_iff_card_roots.mpr ?_ using 1;
    · simp_all +decide [ Polynomial.leadingCoeff, Polynomial.natDegree ];
      ring;
    · exact h_splits;
  rw [ hr ] at h_splits; norm_num [ Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_one, Polynomial.coeff_X, mul_sub ] at *;
  rw [ hr ] ; norm_num [ mul_assoc, sub_mul ] ; nlinarith [ sq_nonneg ( p.coeff 2 * ( r1 - r2 ) ) ] ;

/-
Proving the conjecture for n=2 (it is an equality).
-/
theorem conjecture_n_2 (p q : ℝ[X])
  (hp_monic : p.Monic) (hq_monic : q.Monic)
  (hp_deg : p.natDegree = 2) (hq_deg : q.natDegree = 2)
  (hp_real : p.Splits (RingHom.id ℝ)) (hq_real : q.Splits (RingHom.id ℝ)) :
  invPhi (boxplus 2 p q) = invPhi p + invPhi q := by
    rw [ Phi_deg2, Phi_deg2, Phi_deg2 ];
    any_goals assumption;
    · rw [ discrim_boxplus_deg2 p q hp_monic hq_monic hp_deg hq_deg ];
      ring;
    · unfold boxplus;
      unfold boxplus_coeff; norm_num [ Finset.sum_range_succ', hp_deg, hq_deg ] ;
      rw [ Polynomial.Monic, Polynomial.leadingCoeff_add_of_degree_lt ] <;> norm_num [ hp_deg, hq_deg, hp_monic, hq_monic ];
      · simp_all +decide [ Polynomial.Monic.def, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some ];
      · by_cases h : p.coeff 2 = 0 <;> by_cases h' : q.coeff 2 = 0 <;> simp_all +decide [ Polynomial.degree_add_eq_right_of_degree_lt ];
        · have := hp_monic.coeff_natDegree; have := hq_monic.coeff_natDegree; aesop;
        · have := hp_monic.coeff_natDegree; aesop;
        · have := hq_monic.coeff_natDegree; aesop;
        · erw [ Polynomial.degree_lt_iff_coeff_zero ] ; norm_num;
          intro m hm; rcases m with ( _ | _ | _ | m ) <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ] ;
    · rw [ Polynomial.natDegree_eq_of_degree_eq_some ] ; erw [ Polynomial.degree_eq_of_le_of_coeff_ne_zero ] <;> norm_num [ Polynomial.coeff_one, Polynomial.coeff_X, boxplus ];
      · exact le_trans ( Polynomial.degree_sum_le _ _ ) ( Finset.sup_le fun i hi => Polynomial.degree_C_mul_X_pow_le _ _ |> le_trans <| by fin_cases hi <;> norm_num );
      · norm_num [ Finset.sum_range_succ', boxplus_coeff ];
        exact ⟨ by rw [ ← hp_deg, Polynomial.coeff_natDegree ] ; aesop_cat, by rw [ ← hq_deg, Polynomial.coeff_natDegree ] ; aesop_cat ⟩;
    · -- By definition of boxplus, we know that its discriminant is the sum of the discriminants of p and q.
      have h_discrim : discrim 1 ((boxplus 2 p q).coeff 1) ((boxplus 2 p q).coeff 0) ≥ 0 := by
        have h_discrim_nonneg : discrim 1 (p.coeff 1) (p.coeff 0) ≥ 0 ∧ discrim 1 (q.coeff 1) (q.coeff 0) ≥ 0 := by
          apply And.intro;
          · convert discrim_nonneg_of_splits_deg2 p hp_deg hp_real using 1;
            rw [ ← hp_deg, hp_monic.coeff_natDegree ];
          · convert discrim_nonneg_of_splits_deg2 q hq_deg hq_real using 1;
            rw [ ← hq_deg, hq_monic.coeff_natDegree ];
        linarith [ discrim_boxplus_deg2 p q hp_monic hq_monic hp_deg hq_deg ];
      apply splits_of_discrim_nonneg_deg2;
      · unfold boxplus;
        norm_num [ Finset.sum_range_succ', boxplus_coeff ];
        refine' Polynomial.natDegree_eq_of_degree_eq_some _;
        refine' Polynomial.degree_eq_of_le_of_coeff_ne_zero _ _ <;> norm_num [ Polynomial.coeff_eq_zero_of_natDegree_lt, hp_deg, hq_deg ];
        · rw [ Polynomial.degree_le_iff_coeff_zero ] ; norm_num;
          rintro ( _ | _ | _ | m ) <;> simp +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt, hp_deg, hq_deg ];
        · simp_all +decide [ Polynomial.Monic.def, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some ];
      · convert h_discrim using 1;
        rw [ boxplus_deg2_coeffs p q hp_monic hq_monic hp_deg hq_deg |>.1 ]

/-
Proving the conjecture for n=1.
-/
theorem conjecture_n_1 (p q : ℝ[X])
  (hp_monic : p.Monic) (hq_monic : q.Monic)
  (hp_deg : p.natDegree = 1) (hq_deg : q.natDegree = 1)
  (hp_real : p.Splits (RingHom.id ℝ)) (hq_real : q.Splits (RingHom.id ℝ)) :
  invPhi (boxplus 1 p q) ≥ invPhi p + invPhi q := by
    unfold invPhi;
    rw [ Polynomial.eq_X_add_C_of_natDegree_le_one ( le_of_eq hp_deg ), Polynomial.eq_X_add_C_of_natDegree_le_one ( le_of_eq hq_deg ) ] ; norm_num;
    unfold boxplus;
    norm_num [ Finset.sum_range_succ, boxplus_coeff ];
    simp_all +decide [ Polynomial.Monic.def, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some ];
    erw [ show ( Polynomial.X + ( Polynomial.C ( q.coeff 0 ) + Polynomial.C ( p.coeff 0 ) ) ) = ( Polynomial.X - Polynomial.C ( - ( q.coeff 0 + p.coeff 0 ) ) ) by simpa using by ring, Polynomial.roots_X_sub_C ] at * ; aesop

/-
Proving the formula for Phi in the reduced cubic case.
-/
lemma Phi_deg3_reduced_eq (a b : ℝ)
  (h_real : (X^3 + C a * X + C b).Splits (RingHom.id ℝ))
  (h_nodup : (X^3 + C a * X + C b).roots.Nodup) :
  Phi (X^3 + C a * X + C b) = 18 * a^2 / (-4 * a^3 - 27 * b^2) := by
    obtain ⟨r1, r2, r3, hr⟩ : ∃ r1 r2 r3 : ℝ, r1 + r2 + r3 = 0 ∧ r1 * r2 + r2 * r3 + r3 * r1 = a ∧ r1 * r2 * r3 = -b ∧ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 := by
      obtain ⟨r1, r2, r3, hr⟩ : ∃ r1 r2 r3 : ℝ, r1 ∈ (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b).roots ∧ r2 ∈ (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b).roots ∧ r3 ∈ (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b).roots ∧ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 := by
        have h_card : Multiset.card (Polynomial.roots (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b)) = 3 := by
          rw [ Polynomial.splits_iff_card_roots ] at h_real;
          rw [ h_real, Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases ha : a = 0 <;> simp +decide [ ha ];
        rcases x : Polynomial.roots _ with ⟨ _ | ⟨ r1, _ | ⟨ r2, _ | ⟨ r3, _ | k ⟩ ⟩ ⟩ ⟩ <;> simp_all +decide;
      use r1, r2, r3;
      norm_num at hr;
      grind;
    have h_roots : (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b).roots = {r1, r2, r3} := by
      rw [ show ( Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial ℝ ) = ( Polynomial.X - Polynomial.C r1 ) * ( Polynomial.X - Polynomial.C r2 ) * ( Polynomial.X - Polynomial.C r3 ) by exact Polynomial.funext fun x => by norm_num; linear_combination hr.1 * x^2 - hr.2.1 * x + hr.2.2.1 ];
      rw [ Polynomial.roots_mul ( by exact mul_ne_zero ( mul_ne_zero ( Polynomial.X_sub_C_ne_zero _ ) ( Polynomial.X_sub_C_ne_zero _ ) ) ( Polynomial.X_sub_C_ne_zero _ ) ), Polynomial.roots_mul ( by exact mul_ne_zero ( Polynomial.X_sub_C_ne_zero _ ) ( Polynomial.X_sub_C_ne_zero _ ) ), Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C ] ; tauto;
    unfold Phi;
    simp_all +decide [ Finset.sum ];
    rw [ show a = r1 * r2 + r2 * r3 + r3 * r1 by linarith, show b = -r1 * r2 * r3 by linarith ];
    rw [ inv_add_inv, inv_add_inv, inv_add_inv ] <;> try cases lt_or_gt_of_ne hr.2.2.2.1 <;> cases lt_or_gt_of_ne hr.2.2.2.2.1 <;> cases lt_or_gt_of_ne hr.2.2.2.2.2 <;> nlinarith;
    rw [ div_pow, div_pow, div_pow, div_add_div, div_add_div ];
    · rw [ div_eq_div_iff ];
      · grind +ring;
      · simp +decide [ sub_eq_iff_eq_add, hr ];
        tauto;
      · grind;
    · exact pow_ne_zero 2 ( mul_ne_zero ( sub_ne_zero_of_ne <| by tauto ) ( sub_ne_zero_of_ne <| by tauto ) );
    · exact mul_ne_zero ( pow_ne_zero 2 ( mul_ne_zero ( sub_ne_zero_of_ne <| by tauto ) ( sub_ne_zero_of_ne <| by tauto ) ) ) ( pow_ne_zero 2 ( mul_ne_zero ( sub_ne_zero_of_ne <| by tauto ) ( sub_ne_zero_of_ne <| by tauto ) ) );
    · exact pow_ne_zero 2 ( mul_ne_zero ( sub_ne_zero_of_ne <| by tauto ) ( sub_ne_zero_of_ne <| by tauto ) );
    · exact pow_ne_zero 2 ( mul_ne_zero ( sub_ne_zero_of_ne <| by tauto ) ( sub_ne_zero_of_ne <| by tauto ) )

/-
Proving that a reduced cubic with 3 distinct real roots must have a < 0.
-/
lemma cubic_distinct_real_roots_implies_a_neg (a b : ℝ)
  (h_roots : (X^3 + C a * X + C b).roots.toFinset.card = 3) :
  a < 0 := by
    by_contra h_contra; push_neg at h_contra; (
    have h_increasing : StrictMono (fun x : ℝ => x^3 + a * x + b) := by
      exact fun x y hxy => by norm_num; nlinarith [ sq_nonneg ( x^2 - y^2 ), pow_pos ( sub_pos.mpr hxy ) 3, mul_le_mul_of_nonneg_left hxy.le h_contra ] ;
    exact absurd h_roots ( by exact ne_of_lt ( lt_of_le_of_lt ( Finset.card_le_one.mpr ( by intros x hx y hy; exact h_increasing.injective <| by aesop ) ) ( by norm_num ) ) ));

/-
A reduced cubic with positive discriminant splits and has distinct roots.
-/
lemma cubic_splits_of_discrim_pos (a b : ℝ) (h_disc : -4 * a^3 - 27 * b^2 > 0) :
  (X^3 + C a * X + C b).Splits (RingHom.id ℝ) ∧ (X^3 + C a * X + C b).roots.Nodup := by
    have h_splits : Polynomial.Splits (RingHom.id ℝ) (Polynomial.X ^ 3 + (Polynomial.C a) * Polynomial.X + (Polynomial.C b)) := by
      by_contra h_contra;
      obtain ⟨r, hr⟩ : ∃ r : ℝ, r^3 + a * r + b = 0 := by
        have h_ivt : ∃ r ∈ Set.Icc (-10 - |a| - |b|) (10 + |a| + |b|), r^3 + a * r + b = 0 := by
          apply_rules [ intermediate_value_Icc ] <;> norm_num;
          · linarith [ abs_nonneg a, abs_nonneg b ];
          · fun_prop (disch := norm_num);
          · constructor <;> cases abs_cases a <;> cases abs_cases b <;> nlinarith [ sq_abs a, sq_abs b ];
        aesop;
      have h_factor : Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b = (Polynomial.X - Polynomial.C r) * (Polynomial.X^2 + Polynomial.C r * Polynomial.X + Polynomial.C (r^2 + a)) := by
        exact Polynomial.funext fun x => by norm_num; cases le_or_gt x r <;> nlinarith;
      have h_quad_splits : Polynomial.Splits (RingHom.id ℝ) (Polynomial.X^2 + Polynomial.C r * Polynomial.X + Polynomial.C (r^2 + a)) := by
        have h_discriminant_pos : r^2 - 4 * (r^2 + a) > 0 := by
          rw [ show b = -r ^ 3 - a * r by linarith ] at h_disc ; nlinarith [ sq_nonneg ( a + 3 * r ^ 2 ) ];
        rw [ Polynomial.splits_iff_card_roots ];
        rw [ show ( Polynomial.X ^ 2 + Polynomial.C r * Polynomial.X + Polynomial.C ( r ^ 2 + a ) ) = ( Polynomial.X - Polynomial.C ( ( -r + Real.sqrt ( r ^ 2 - 4 * ( r ^ 2 + a ) ) ) / 2 ) ) * ( Polynomial.X - Polynomial.C ( ( -r - Real.sqrt ( r ^ 2 - 4 * ( r ^ 2 + a ) ) ) / 2 ) ) by exact Polynomial.funext fun x => by norm_num; linarith [ Real.mul_self_sqrt h_discriminant_pos.le ] ] ; rw [ Polynomial.roots_mul <| mul_ne_zero ( Polynomial.X_sub_C_ne_zero _ ) ( Polynomial.X_sub_C_ne_zero _ ) ] ; erw [ Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C ] ; norm_num;
        rw [ Polynomial.natDegree_mul' ] <;> norm_num [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ];
      simp_all +decide [ Polynomial.splits_mul_iff ];
      exact h_contra <| Polynomial.splits_mul _ ( Polynomial.splits_X_sub_C _ ) h_quad_splits
    have h_distinct : (Polynomial.X ^ 3 + (Polynomial.C a) * Polynomial.X + (Polynomial.C b)).roots.Nodup := by
      rw [ Multiset.nodup_iff_count_le_one ];
      intro x; by_contra h; have := Polynomial.card_roots' ( Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b ) ; simp_all +decide [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] ;
      have h_deriv_root : Polynomial.eval x (Polynomial.derivative (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b)) = 0 := by
        exact Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity h;
      norm_num at h_deriv_root;
      have h_sub : -4 * (-3 * x^2)^3 - 27 * b^2 > 0 := by
        rw [ show a = -3 * x ^ 2 by linarith ] at h_disc ; linarith;
      have h_sub : b = 2 * x^3 := by
        have h_sub : Polynomial.eval x (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) = 0 := by
          exact Polynomial.rootMultiplicity_pos ( by aesop ) |>.1 ( by linarith );
        norm_num at h_sub; cases le_or_gt 0 x <;> nlinarith;
      subst h_sub; nlinarith;
    exact ⟨h_splits, h_distinct⟩
    skip

/-
Proving that boxplus of reduced cubics is a reduced cubic with summed coefficients.
-/
lemma boxplus_deg3_reduced_eq (p q : ℝ[X])
  (hp_monic : p.Monic) (hq_monic : q.Monic)
  (hp_deg : p.natDegree = 3) (hq_deg : q.natDegree = 3)
  (hp_red : p.coeff 2 = 0) (hq_red : q.coeff 2 = 0) :
  boxplus 3 p q = X^3 + C (p.coeff 1 + q.coeff 1) * X + C (p.coeff 0 + q.coeff 0) := by
    unfold boxplus;
    simp_all +decide [ Finset.sum_range_succ, boxplus_coeff ];
    simp_all +decide [ Polynomial.Monic.def, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some ];
    ring

/-
Proving the discriminant of distinct real roots is positive.
-/
noncomputable def discrim_reduced_cubic (a b : ℝ) : ℝ := -4 * a^3 - 27 * b^2

lemma discrim_reduced_cubic_pos_of_distinct_roots (a b : ℝ)
  (h_real : (X^3 + C a * X + C b).Splits (RingHom.id ℝ))
  (h_nodup : (X^3 + C a * X + C b).roots.Nodup) :
  discrim_reduced_cubic a b > 0 := by
    by_contra h_contra;
    have h_discrim_pos : -4 * a^3 - 27 * b^2 > 0 := by
      have h_card : (Polynomial.X^3 + Polynomial.C a * Polynomial.X + Polynomial.C b).roots.toFinset.card = 3 := by
        rw [ Polynomial.splits_iff_card_roots ] at h_real;
        rw [ Multiset.toFinset_card_of_nodup h_nodup ] ; erw [ h_real ] ; erw [ Polynomial.natDegree_add_C ] ; erw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> by_cases ha : a = 0 <;> simp +decide [ ha ] ;
      obtain ⟨ r1, r2, r3, h ⟩ := Finset.card_eq_three.mp h_card;
      simp_all +decide [ Finset.ext_iff ];
      have h_vieta_sum : r1 + r2 + r3 = 0 := by
        exact mul_left_cancel₀ ( sub_ne_zero_of_ne h.1 ) <| mul_left_cancel₀ ( sub_ne_zero_of_ne h.2.1 ) <| mul_left_cancel₀ ( sub_ne_zero_of_ne h.2.2.1 ) <| by cases lt_or_gt_of_ne h.1 <;> cases lt_or_gt_of_ne h.2.1 <;> cases lt_or_gt_of_ne h.2.2.1 <;> nlinarith [ h.2.2.2 r1 |>.2 <| Or.inl rfl, h.2.2.2 r2 |>.2 <| Or.inr <| Or.inl rfl, h.2.2.2 r3 |>.2 <| Or.inr <| Or.inr rfl ] ;
      have h_vieta_prod_sum : r1 * r2 + r2 * r3 + r3 * r1 = a := by
        exact mul_left_cancel₀ ( sub_ne_zero_of_ne h.1 ) ( by ring_nf; nlinarith [ h.2.2.2 r1 |>.2 ( Or.inl rfl ), h.2.2.2 r2 |>.2 ( Or.inr ( Or.inl rfl ) ), h.2.2.2 r3 |>.2 ( Or.inr ( Or.inr rfl ) ) ] )
      have h_vieta_prod : r1 * r2 * r3 = -b := by
        have := h.2.2.2 r1; norm_num at this; cases le_or_gt 0 r1 <;> nlinarith [ sq_nonneg r1 ] ;
      rw [ ← eq_sub_iff_add_eq' ] at h_vieta_sum ; subst_vars ; ring_nf at *;
      rw [ show b = r1 * r2 ^ 2 + r1 ^ 2 * r2 by linarith ] ; nlinarith [ mul_self_pos.mpr ( sub_ne_zero.mpr h.1 ), mul_self_pos.mpr ( sub_ne_zero.mpr h.2.1 ), mul_self_pos.mpr ( sub_ne_zero.mpr h.2.2.1 ), mul_pos ( mul_self_pos.mpr ( sub_ne_zero.mpr h.1 ) ) ( mul_self_pos.mpr ( sub_ne_zero.mpr h.2.1 ) ), mul_pos ( mul_self_pos.mpr ( sub_ne_zero.mpr h.1 ) ) ( mul_self_pos.mpr ( sub_ne_zero.mpr h.2.2.1 ) ), mul_pos ( mul_self_pos.mpr ( sub_ne_zero.mpr h.2.1 ) ) ( mul_self_pos.mpr ( sub_ne_zero.mpr h.2.2.1 ) ) ];
    exact h_contra <| by unfold discrim_reduced_cubic; linarith;

/-
NOW: Prove the n=3 inequality using the Cauchy-Schwarz argument.

For reduced cubics p(x) = x³ + a₁x + b₁ and q(x) = x³ + a₂x + b₂:
- boxplus 3 p q = x³ + (a₁+a₂)x + (b₁+b₂)  (by boxplus_deg3_reduced_eq)
- 1/Φ₃ = (-4a³ - 27b²)/(18a²) = (2/9)(-a) - (3/2)b²/a²

Setting u₁ = -a₁ > 0, u₂ = -a₂ > 0:
  1/Φ₃(p) = (2/9)u₁ - (3/2)b₁²/u₁²
  1/Φ₃(q) = (2/9)u₂ - (3/2)b₂²/u₂²
  1/Φ₃(p⊞q) = (2/9)(u₁+u₂) - (3/2)(b₁+b₂)²/(u₁+u₂)²

The inequality reduces to:
  (b₁+b₂)²/(u₁+u₂)² ≤ b₁²/u₁² + b₂²/u₂²

which is Cauchy-Schwarz: (Σ xᵢyᵢ)² ≤ (Σ xᵢ²)(Σ yᵢ²) with appropriate substitution,
or equivalently: cross-multiply and expand to get (b₁u₂ - b₂u₁)² ≥ 0.
-/

theorem conjecture_n_3_reduced (a1 b1 a2 b2 : ℝ)
  (h_real1 : (X^3 + C a1 * X + C b1).Splits (RingHom.id ℝ))
  (h_nodup1 : (X^3 + C a1 * X + C b1).roots.Nodup)
  (h_real2 : (X^3 + C a2 * X + C b2).Splits (RingHom.id ℝ))
  (h_nodup2 : (X^3 + C a2 * X + C b2).roots.Nodup)
  (h_real3 : (X^3 + C (a1+a2) * X + C (b1+b2)).Splits (RingHom.id ℝ))
  (h_nodup3 : (X^3 + C (a1+a2) * X + C (b1+b2)).roots.Nodup) :
  invPhi (X^3 + C (a1+a2) * X + C (b1+b2)) ≥
  invPhi (X^3 + C a1 * X + C b1) + invPhi (X^3 + C a2 * X + C b2) := by
  sorry

/-
For the GENERAL n case, try the following approaches:

APPROACH 1 — Finite Free Cumulants:
The finite free R-transform is additive under ⊞_d:
  R_{p⊞q}^(d)(z) = R_p^(d)(z) + R_q^(d)(z)

The finite R-transform encodes the finite free cumulants κ_k^(d).
Express Φ_n in terms of these cumulants and show superadditivity of 1/Φ_n.

APPROACH 2 — Conjugate Variables (mirrors infinite proof):
For empirical measure μ = (1/n)Σ δ_{λ_i}, define:
  ξ_i = Σ_{j≠i} 1/(λ_i - λ_j)   (the "free score" at root i)
  Φ_n = Σ_i ξ_i²

Using the random matrix representation p ⊞_n q = E_Q[det(xI - A - QBQ*)]:
  The eigenvalues ν_i of A + QBQ* satisfy:
  ξ_i^{A+QBQ*} = E[ξ_i^A | eigenvalues of A+QBQ*]  (by conditional expectation)

By the conditional variance inequality:
  Var(ξ^{A+QBQ*}) ≤ Var(ξ^A)

This should give Φ_n(⊞) ≤ Φ_n(A) for each realization, hence after
careful averaging: 1/Φ_n(p⊞q) ≥ 1/Φ_n(p) + 1/Φ_n(q).

APPROACH 3 — Via n=2 equality + induction:
The n=2 case is an EQUALITY. For n ≥ 3, we need strict inequality in general.
Try reducing the n-root case to (n-1)-root subcases via:
- Removing one root and relating Φ_n to Φ_{n-1}
- Using the interlacing properties of ⊞_n from MSS

APPROACH 4 — Direct power sum / Newton identity approach:
Express Φ_n = 2 Σ_{i<j} 1/(λ_i-λ_j)² in terms of power sums p_k = Σ λ_i^k.
The power sums under ⊞_n transform via the convolution formula.
Show the inequality using Newton's identities relating power sums to
elementary symmetric polynomials.
-/

/-
FORMAL STATEMENT (for reference):
-/

-- The formal statement uses Fin n → ℝ for root tuples
-- and freeAddConv for the convolution.
-- See FirstProof/Problem4/Formal.lean for the exact statement.

/-
Alternative formulation using Fin n → ℝ for root tuples:
-/

def phi_fin (n : ℕ) (roots : Fin n → ℝ) : ℝ :=
  ∑ i, (∑ j ∈ Finset.univ.erase i, 1 / (roots i - roots j)) ^ 2

def freeAddConv_fin (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C
    (∑ i ∈ Finset.range (k + 1),
      (((n - i).factorial : ℝ) * ((n - (k - i)).factorial : ℝ)) /
      (((n.factorial : ℝ) * ((n - k).factorial : ℝ))) *
      p.coeff (n - i) * q.coeff (n - (k - i))) * X ^ (n - k)

theorem first_proof_problem4 (n : ℕ) (hn : 0 < n)
    (rp rq rpq : Fin n → ℝ)
    (hp : Function.Injective rp) (hq : Function.Injective rq) (hpq : Function.Injective rpq)
    (hconv : (∏ i : Fin n, (X - C (rpq i))) =
             freeAddConv_fin n (∏ i : Fin n, (X - C (rp i))) (∏ i : Fin n, (X - C (rq i))))
    : 1 / phi_fin n rpq ≥ 1 / phi_fin n rp + 1 / phi_fin n rq := by
  sorry
