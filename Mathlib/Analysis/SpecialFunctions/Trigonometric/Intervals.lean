import Mathlib

-- https://github.com/leanprover-community/mathlib4/pull/29022
attribute [fun_prop] Real.contDiff_sin Real.contDiff_cos

section -- https://github.com/leanprover-community/mathlib4/pull/29023

@[simp]
theorem iteratedDeriv_add_one_sin (n : ℕ) :
    iteratedDeriv (n + 1) Real.sin = iteratedDeriv n Real.cos := by
  induction n with
  | zero => simp only [zero_add, iteratedDeriv_one, Real.deriv_sin, iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]

@[simp]
theorem iteratedDeriv_add_one_cos (n : ℕ) :
    iteratedDeriv (n + 1) Real.cos = - iteratedDeriv n Real.sin := by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ, deriv.neg']
    ext x
    simp

@[simp]
theorem iteratedDeriv_even_sin (n : ℕ) :
    iteratedDeriv (2 * n) Real.sin = (-1) ^ n * Real.sin := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

@[simp]
theorem iteratedDeriv_even_cos (n : ℕ) :
    iteratedDeriv (2 * n) Real.cos = (-1) ^ n * Real.cos := by
  induction n with
  | zero => simp
  | succ n ih => simp_all [mul_add, pow_succ]

theorem iteratedDeriv_odd_sin (n : ℕ) :
    iteratedDeriv (2 * n + 1) Real.sin = (-1) ^ n * Real.cos := by simp

@[simp]
theorem iteratedDeriv_odd_cos (n : ℕ) :
    iteratedDeriv (2 * n + 1) Real.cos = (-1) ^ (n + 1) * Real.sin := by simp [pow_succ]

theorem differentiable_iteratedDeriv_sin (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n Real.sin) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_sin]

theorem differentiable_iteratedDeriv_cos (n : ℕ) :
    Differentiable ℝ (iteratedDeriv n Real.cos) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [differentiable_iteratedDeriv_cos]

theorem abs_iteratedDeriv_sin_le_one (n : ℕ) (x : ℝ) :
    |iteratedDeriv n Real.sin x| ≤ 1 :=
  match n with
  | 0 => by simpa using Real.abs_sin_le_one x
  | 1 => by simpa using Real.abs_cos_le_one x
  | n + 2 => by simpa using abs_iteratedDeriv_sin_le_one n x

theorem abs_iteratedDeriv_cos_le_one (n : ℕ) (x : ℝ) :
    |iteratedDeriv n Real.cos x| ≤ 1 :=
  match n with
  | 0 => by simpa using Real.abs_cos_le_one x
  | 1 => by simpa using Real.abs_sin_le_one x
  | n + 2 => by simpa using abs_iteratedDeriv_cos_le_one n x

end

section -- https://github.com/leanprover-community/mathlib4/pull/29024

theorem iteratedDerivWithin_Ioo {n : ℕ} {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Set.Ioo a b)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ n f (Set.Icc a b)) :
    iteratedDerivWithin n f (Set.Ioo a b) x = iteratedDeriv n f x := by
  rw [iteratedDerivWithin_eq_iteratedDeriv]
  · exact uniqueDiffOn_convex (convex_Ioo a b) (by simp_all)
  · exact ContDiffOn.contDiffAt hf (x := x) (by rwa [Icc_mem_nhds_iff])
  · exact hx

theorem iteratedDerivWithin_Icc {n : ℕ} {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Set.Icc a b)
    {f : ℝ → ℝ} (hf : ContDiff ℝ n f) :
    iteratedDerivWithin n f (Set.Icc a b) x = iteratedDeriv n f x := by
  rw [iteratedDerivWithin_eq_iteratedDeriv]
  · exact uniqueDiffOn_convex (convex_Icc a b) (by simp_all)
  · exact ContDiff.contDiffAt hf
  · exact hx

end

@[simp]
theorem iteratedDerivWithin_sin_Icc (n : ℕ) {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    iteratedDerivWithin n Real.sin (Set.Icc a b) x = iteratedDeriv n Real.sin x :=
  iteratedDerivWithin_Icc h hx Real.contDiff_sin

@[simp]
theorem iteratedDerivWithin_cos_Icc (n : ℕ) {a b : ℝ} (h : a < b) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    iteratedDerivWithin n Real.cos (Set.Icc a b) x = iteratedDeriv n Real.cos x :=
  iteratedDerivWithin_Icc h hx Real.contDiff_cos

namespace Real.sin

open Nat

def iteratedDerivAtZero : ℕ → ℚ
| 0 => 0
| 1 => 1
| n + 2 => - iteratedDerivAtZero n

/-- The `n`-th Taylor polynomial of `sin` at `0`, as a function `ℚ → ℚ`. -/
def ratApprox (n : ℕ) (x : ℚ) : ℚ :=
  ∑ i ∈ Finset.range (n + 1), (iteratedDerivAtZero i * x ^ i) / i !

def ratApprox.errorBound (n : ℕ) (x : ℚ) : ℚ :=
  |x| ^ (n + 1) / (n + 1)!

attribute [simp] PolynomialModule.eval_smul

theorem iteratedDerivAtZero_eq (n : ℕ) :
    iteratedDerivAtZero n = iteratedDeriv n sin 0 :=
  match n with
  | 0 => by simp [iteratedDerivAtZero]
  | 1 => by simp [iteratedDerivAtZero]
  | n + 2 => by simp [iteratedDerivAtZero, iteratedDerivAtZero_eq]

theorem ratApprox_eq {x : ℚ} {n : ℕ} (h : 0 < x) :
    (ratApprox n x : ℝ) = taylorWithinEval sin n (Set.Icc 0 ↑x) 0 ↑x := by
  have : (0 : ℝ) ∈ Set.Icc 0 (x : ℝ) := by simp; grind
  simp_all [taylorWithinEval, taylorWithin, taylorCoeffWithin, ratApprox, iteratedDerivAtZero_eq]
  grind

theorem ratApprox_bound_aux (n : ℕ) {x : ℚ} (h : 0 < x) :
    |sin x - ratApprox n x| ≤ ratApprox.errorBound n x := by
  have h' : 0 < (x : ℝ) := by rify at h; exact h
  have w := taylor_mean_remainder_lagrange (f := sin) (n := n) h' ?_ ?_
  · obtain ⟨x', m, w⟩ := w
    rw [ratApprox_eq h, w]
    simp [abs_div, ratApprox.errorBound]
    gcongr
    rw [iteratedDerivWithin_sin_Icc _ h' (by grind)]
    have t₁ := abs_iteratedDeriv_sin_le_one (n + 1) x'
    have t₂ : 0 ≤ |(x : ℝ)| ^ (n + 1) := by positivity
    simpa using mul_le_mul_of_nonneg_right t₁ t₂
  · fun_prop
  · apply DifferentiableOn.congr (f := iteratedDeriv n Real.sin)
    · exact Differentiable.differentiableOn (differentiable_iteratedDeriv_sin n)
    · intro x' hx'
      simp_all
      rw [iteratedDerivWithin_sin_Icc] <;> grind

@[local simp]
theorem ratApprox_zero {n : ℕ} :
    ratApprox n 0 = 0 := by
  simp [ratApprox, Finset.sum_range_succ', iteratedDerivAtZero]

theorem iteratedDerivAtZero_mul_neg_one_pow {n : ℕ} :
    iteratedDerivAtZero n * (-1) ^ n = - iteratedDerivAtZero n :=
  match n with
  | 0 => by simp [iteratedDerivAtZero]
  | 1 => by simp [iteratedDerivAtZero]
  | n + 2 => by simp [iteratedDerivAtZero, pow_add, iteratedDerivAtZero_mul_neg_one_pow]

theorem ratApprox_neg {n : ℕ} {x : ℚ} :
    ratApprox n (-x) = -ratApprox n x := by
  simp [ratApprox, neg_pow x, ← mul_assoc, iteratedDerivAtZero_mul_neg_one_pow, neg_div]

theorem errorBound_nonneg {n : ℕ} {x : ℚ} :
    0 ≤ ratApprox.errorBound n x := by
  simp [ratApprox.errorBound]
  positivity

theorem errorBound_neg {n : ℕ} {x : ℚ} :
    ratApprox.errorBound n (-x) = ratApprox.errorBound n x := by
  simp [ratApprox.errorBound]

theorem ratApprox_bound (n : ℕ) (x : ℚ) :
    |sin x - ratApprox n x| ≤ ratApprox.errorBound n x := by
  obtain neg | rfl | pos := lt_trichotomy x 0
  · rw [← neg_neg x]
    rw [Rat.cast_neg, sin_neg, Rat.cast_neg, ratApprox_neg, sub_eq_add_neg, ← neg_add, abs_neg,
      Rat.cast_neg, ← sub_eq_add_neg, errorBound_neg, ← Rat.cast_neg]
    exact ratApprox_bound_aux n (by grind)
  · simpa using errorBound_nonneg
  · exact ratApprox_bound_aux n pos

def upperBound (n : ℕ) (x : ℚ) : ℚ :=
  ratApprox n x + ratApprox.errorBound n x

def lowerBound (n : ℕ) (x : ℚ) : ℚ :=
  ratApprox n x - ratApprox.errorBound n x

def interval (n : ℕ) (x y : ℚ) : ℚ × ℚ :=
  (lowerBound n x, upperBound n y)

/-- info: ((-25 : Rat)/48, (25 : Rat)/48) -/
#guard_msgs in
#eval interval 2 (-1/2) (1/2)

theorem mem_interval (n : ℕ) {x y : ℚ} (wx : -1 ≤ x) (wy : y ≤ 1) {z : ℝ} (h : x ≤ z ∧ z ≤ y) :
    lowerBound n x ≤ sin z ∧ sin z ≤ upperBound n y := by
  have m : MonotoneOn sin (Set.Icc x y) := by
    apply strictMonoOn_sin.monotoneOn.mono
    refine (Set.Icc_subset_Icc_iff ?_).mpr ?_
    · grind
    · have := Real.pi_gt_three
      rify at wx wy
      constructor <;> linarith
  have mx := @m x (by grind) z (by grind) (by grind)
  have my := @m z (by grind) y (by grind) (by grind)
  have rx := ratApprox_bound n x
  have ry := ratApprox_bound n y
  unfold lowerBound
  unfold upperBound
  grind [abs_le, Rat.cast_sub, Rat.cast_add]

end Real.sin

/--
A machine for propagating intervals through a function.

The propagator is only required to propagate subintervals of `Set.Icc a b`.

* `forward q x y h` must produce a pair of rationals `(r, s)` such that
  if `z ∈ Set.Icc x y` then `f x ∈ Set.Icc r s`

The parameter `q` is a "quality" parameter, which is used to control the effort expended in
producing a tight interval.
No guarantees are required regarding the dependence on `q`,
but we suggest that where possible the additional error introduced should be bounded by `q`.
-/
structure IntervalPropagator (f : ℝ → ℝ) (a b : ℚ) where
  forward (q : ℚ) (x : ℚ) (y : ℚ) (h : Set.Icc x y ⊆ Set.Icc a b) : ℚ × ℚ
  mem (q : ℚ) (x : ℚ) (y : ℚ) (h : Set.Icc x y ⊆ Set.Icc a b) (z : ℝ) (m : x ≤ z ∧ z ≤ y) :
    let (r, s) := forward q x y h
    r ≤ f z ∧ f z ≤ s

/--
An interval propagator for `sin` on the interval `Set.Icc (-1) 1`.

If we use the n-th Taylor polynomial,
the introduced error is bounded by `1 / (n + 1)! ≤ 1 / 2^n`.
So if we take `n = (q⁻¹).ceil.toNat.log2`, the error will be bounded by `q`.
One could do better (i.e. get away with a smaller `n`) by bounding the factorial more tightly,
or using the input interval, which may be closer to zero.
-/
def Real.sin.propagator : IntervalPropagator Real.sin (-1) 1 where
  forward q x y h := Real.sin.interval (q⁻¹).ceil.toNat.log2 x y
  mem q x y h z m :=
    have h := (Set.Icc_subset_Icc_iff (by rify; grind)).mp h
    Real.sin.mem_interval (q⁻¹).ceil.toNat.log2 h.1 h.2 m

-- We'll also have a user level gadget that says:
-- if you have an interval that doesn't lie inside `Set.Icc (-1) 1`
-- that you're trying to propagate through `sin`,
-- add the identity `sin x = 3 sin (x / 3) - 4 * (sin (x / 3)) ^ 3` instead.
-- This has the effect of shrinking the interval by a factor of 3:
-- recursing, we can shrink into the interval `Set.Icc (-1) 1`.
