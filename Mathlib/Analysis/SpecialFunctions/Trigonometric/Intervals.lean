import Mathlib

theorem Real.monotoneOn_sin : MonotoneOn sin (Set.Icc (-(Real.pi/2)) (Real.pi/2)) :=
  StrictMonoOn.monotoneOn strictMonoOn_sin

@[simp]
theorem iteratedDerivWithin_sin (n : ℕ) (s : Set ℝ) :
    iteratedDerivWithin n Real.sin s = iteratedDeriv n Real.sin := sorry

@[simp]
theorem iteratedDeriv_odd_sin (n : ℕ) :
    iteratedDeriv (2 * n + 1) Real.sin = (-1) ^ n * Real.cos := sorry

@[simp]
theorem iteratedDeriv_even_sin (n : ℕ) :
    iteratedDeriv (2 * n) Real.sin = (-1) ^ n * Real.sin := sorry

@[simp]
theorem contDiffOn_sin (n : WithTop ℕ∞) (s : Set ℝ) :
    ContDiffOn ℝ n Real.sin s := sorry

namespace Real.sin

open Nat

/-- The `2 * n`-th Taylor polynomial of `sin` at `0`, as a function `ℚ → ℚ`. -/
def ratApprox (x : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, ((-1) ^ i * x ^ (2 * i + 1)) / (2 * i + 1)!

def ratApprox.errorBound (x : ℚ) (n : ℕ) : ℚ :=
  |x| ^ (2 * n + 1) / (2 * n + 1)!

theorem ratApprox_eq {x : ℚ} {n : ℕ} :
   (ratApprox x n : ℝ) = taylorWithinEval sin (2 * n) (Set.Icc 0 ↑x) 0 ↑x := sorry

theorem ratApprox_bound' (x : ℚ) (h : 0 < x) (n : ℕ) :
    |sin x - ratApprox x n| ≤ ratApprox.errorBound x n := by
  have h' : 0 < (x : ℝ) := sorry
  have w := taylor_mean_remainder_lagrange (f := sin) (n := 2 * n) h' ?_ ?_
  · obtain ⟨x', m, h⟩ := w
    rw [ratApprox_eq, h]
    simp [abs_div, ratApprox.errorBound]
    gcongr
    sorry
  · simp
  · simp
    refine DifferentiableOn.mul ?_ ?_
    · sorry
    · sorry


theorem ratApprox_bound (x : ℚ) (n : ℕ) :
    |sin x - ratApprox x n| ≤ ratApprox.errorBound x n := by
  sorry -- Taylor's theorem, probably taylor_mean_remainder_lagrange

def upperBound (x : ℚ) (n : ℕ) : ℚ :=
  ratApprox x n + ratApprox.errorBound x n

def lowerBound (x : ℚ) (n : ℕ) : ℚ :=
  ratApprox x n - ratApprox.errorBound x n

def interval (x y : ℚ) (n : ℕ) : ℚ × ℚ :=
  (lowerBound x n, upperBound y n)

/-- info: ((-25 : Rat)/48, (25 : Rat)/48) -/
#guard_msgs in
#eval interval (-1/2) (1/2) 1

theorem mem_interval {x y : ℚ} (wx : -1 ≤ x) (wy : y ≤ 1) {n : ℕ} {z : ℝ} (h : x ≤ z ∧ z ≤ y) :
    lowerBound x n ≤ sin z ∧ sin z ≤ upperBound y n := by
  have m : MonotoneOn sin (Set.Icc x y) := by
    apply MonotoneOn.mono Real.monotoneOn_sin
    refine (Set.Icc_subset_Icc_iff ?_).mpr ?_
    · grind
    · have := Real.pi_gt_three
      rify at wx wy
      constructor <;> linarith
  have mx := @m x (by grind) z (by grind) (by grind)
  have my := @m z (by grind) y (by grind) (by grind)
  have rx := ratApprox_bound x n
  have ry := ratApprox_bound y n
  unfold lowerBound
  unfold upperBound
  grind [abs_le, Rat.cast_sub, Rat.cast_add]

end Real.sin
