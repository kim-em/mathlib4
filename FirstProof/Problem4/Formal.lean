import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic

open Polynomial Finset

noncomputable section

/-- Φ_n(λ) = ∑ᵢ (∑_{j≠i} 1/(λᵢ - λⱼ))² for a tuple of distinct reals.
    This measures the "electrostatic energy" of the roots. -/
def phi (n : ℕ) (roots : Fin n → ℝ) : ℝ :=
  ∑ i, (∑ j ∈ univ.erase i, 1 / (roots i - roots j)) ^ 2

/-- The finite free additive convolution (p ⊞_n q) of two degree-n polynomials.
    If p(x) = ∑_{k=0}^n a_k x^{n-k} and q(x) = ∑_{k=0}^n b_k x^{n-k},
    then (p ⊞_n q)(x) = ∑_{k=0}^n c_k x^{n-k} where
    c_k = ∑_{i+j=k} ((n-i)!(n-j)!) / (n!(n-k)!) · a_i · b_j. -/
def freeAddConv (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (n + 1), C
    (∑ i ∈ range (k + 1),
      (((n - i).factorial : ℝ) * ((n - (k - i)).factorial : ℝ)) /
      (((n.factorial : ℝ) * ((n - k).factorial : ℝ))) *
      p.coeff (n - i) * q.coeff (n - (k - i))) * X ^ (n - k)

/-- **Problem 4 from "First Proof" (Spielman).**
    For monic real-rooted polynomials p and q of degree n with distinct roots,
    the finite free additive convolution satisfies
    1/Φ_n(p ⊞_n q) ≥ 1/Φ_n(p) + 1/Φ_n(q)
    where the roots of p ⊞_n q are also assumed to be distinct.

    Here λ_, μ_, ν_ are the roots of p, q, and p ⊞_n q respectively. -/
theorem first_proof_problem4 (n : ℕ) (hn : 0 < n)
    (rp rq rpq : Fin n → ℝ)
    (hp : Function.Injective rp) (hq : Function.Injective rq) (hpq : Function.Injective rpq)
    (hconv : (∏ i : Fin n, (X - C (rpq i))) =
             freeAddConv n (∏ i : Fin n, (X - C (rp i))) (∏ i : Fin n, (X - C (rq i))))
    : 1 / phi n rpq ≥ 1 / phi n rp + 1 / phi n rq := by
  sorry
