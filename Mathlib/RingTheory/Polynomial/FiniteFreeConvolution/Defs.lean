/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic

/-!
# Finite Free Convolution: Definitions

This file defines the finite free additive convolution (boxplus) of polynomials,
along with the Fisher information functional Phi and its inverse.

These definitions formalize the key objects from:
- Garza-Vargas, Srivastava, Stier. "The Finite Free Stam Inequality". arXiv:2602.15822.

## Main definitions

* `Polynomial.boxplusCoeff n p q k`: The k-th coefficient of the boxplus convolution.
* `Polynomial.boxplus n p q`: The finite free additive convolution p ⊞_n q.
* `Polynomial.phiFisher p`: The Fisher information Φ(p) = Σᵢ (Σⱼ≠ᵢ 1/(rᵢ-rⱼ))².
* `Polynomial.invPhiFisher p`: The inverse Fisher information 1/Φ(p).
* `Polynomial.IsCentered n p`: Predicate for centered polynomials (monic, degree n, zero trace).
-/

open scoped BigOperators

noncomputable section

namespace Polynomial

/-- The k-th coefficient of the finite free additive convolution of two degree-n polynomials.
    For p(x) = Σ aₖ x^{n-k} and q(x) = Σ bₖ x^{n-k}, the k-th coefficient is
    cₖ = Σ_{i+j=k} ((n-i)!(n-j)!) / (n!(n-k)!) · aᵢ · bⱼ. -/
def boxplusCoeff (n : ℕ) (p q : ℝ[X]) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    let j := k - i
    (Nat.factorial (n - i) * Nat.factorial (n - j) : ℝ) /
      (Nat.factorial n * Nat.factorial (n - k) : ℝ) *
    (p.coeff (n - i)) * (q.coeff (n - j))

/-- The finite free additive convolution p ⊞_n q of two degree-n polynomials. -/
def boxplus (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (boxplusCoeff n p q k) * X ^ (n - k)

/-- The Fisher information functional Φ(p), defined as the sum of squared score components.
    Φ(p) = Σᵢ (Σⱼ≠ᵢ 1/(rᵢ - rⱼ))² where r₁, ..., rₙ are the roots of p. -/
def phiFisher (p : ℝ[X]) : ℝ :=
  let roots := p.roots.toFinset
  ∑ r_i ∈ roots, (∑ r_j ∈ roots.erase r_i, 1 / (r_i - r_j)) ^ 2

/-- The inverse Fisher information 1/Φ(p), or 0 if p has fewer than 2 distinct roots. -/
def invPhiFisher (p : ℝ[X]) : ℝ :=
  if p.roots.Nodup ∧ p.roots.card > 1 then
    1 / phiFisher p
  else 0

/-- A polynomial is centered if it is monic of degree n with zero coefficient of x^{n-1}. -/
def IsCentered (n : ℕ) (p : ℝ[X]) : Prop :=
  p.Monic ∧ p.natDegree = n ∧ p.coeff (n - 1) = 0

end Polynomial
