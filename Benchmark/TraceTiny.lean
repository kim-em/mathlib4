import Mathlib.Tactic.Linarith
set_option trace.linarith.detail true in
example (x : ℚ) (h : 2 * x ≤ 1) : x ≤ 1/2 := by
  linarith (config := { useFastDischarger := true })
