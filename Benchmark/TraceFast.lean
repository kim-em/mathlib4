import Mathlib.Tactic.Linarith

set_option trace.profiler true in
set_option trace.linarith.detail true in
example (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : ℚ)
    (a0 : 0 ≤ x0) (a1 : 0 ≤ x1) (a2 : 0 ≤ x2) (a3 : 0 ≤ x3) (a4 : 0 ≤ x4)
    (a5 : 0 ≤ x5) (a6 : 0 ≤ x6) (a7 : 0 ≤ x7) (a8 : 0 ≤ x8) (a9 : 0 ≤ x9)
    (a10 : 0 ≤ x10) (a11 : 0 ≤ x11) (a12 : 0 ≤ x12) (a13 : 0 ≤ x13) (a14 : 0 ≤ x14)
    (a15 : 0 ≤ x15) (a16 : 0 ≤ x16) (a17 : 0 ≤ x17) (a18 : 0 ≤ x18) (a19 : 0 ≤ x19)
    (b0 : x0 ≤ 1) (b1 : x1 ≤ 1) (b2 : x2 ≤ 1) (b3 : x3 ≤ 1) (b4 : x4 ≤ 1)
    (b5 : x5 ≤ 1) (b6 : x6 ≤ 1) (b7 : x7 ≤ 1) (b8 : x8 ≤ 1) (b9 : x9 ≤ 1)
    (b10 : x10 ≤ 1) (b11 : x11 ≤ 1) (b12 : x12 ≤ 1) (b13 : x13 ≤ 1) (b14 : x14 ≤ 1)
    (b15 : x15 ≤ 1) (b16 : x16 ≤ 1) (b17 : x17 ≤ 1) (b18 : x18 ≤ 1) (b19 : x19 ≤ 1) :
    x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 +
    x10 + x11 + x12 + x13 + x14 + x15 + x16 + x17 + x18 + x19 ≤ 20 := by
  linarith (config := { useFastDischarger := true })
