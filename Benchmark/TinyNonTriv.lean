import Mathlib.Tactic.Linarith
-- Minimum non-trivial multiplier test:
-- Hypothesis: 2 * x ≤ 1, so x ≤ 1/2. Goal: x ≤ 1/2.
example (x : ℚ) (h : 2 * x ≤ 1) : x ≤ 1/2 := by
  linarith (config := { useFastDischarger := true })
