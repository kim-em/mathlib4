module
import Mathlib.Tactic.NoncommRing
public meta import Lean.Elab.Tactic

/-! Direct tactic timings, including simplification and proof construction. -/

open Lean Meta Elab Tactic
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedTactic false

elab "bench_noncomm " label:str count:num remaining:num tac:tactic : tactic => do
  let saved ← saveState
  let trial := do
    saved.restore
    evalTactic tac
    let goals ← getUnsolvedGoals
    unless goals.length == remaining.getNat do
      throwError "unexpected residual goals: {goals}"
  for _ in [:3] do trial
  let start ← IO.monoNanosNow
  for _ in [:count.getNat] do trial
  let elapsed := (← IO.monoNanosNow) - start
  saved.restore
  logInfo m!"NONCOMM_BENCH {label.getString} {count.getNat} {elapsed} {remaining.getNat}"
  evalTactic tac

example {R : Type*} [Ring R] (z x0 x1 x2 x3 x4 x5 x6 x7 : R) :
    (x0 + x1) * z + (x1 + x2) * z + (x2 + x3) * z + (x3 + x4) * z + (x4 + x5) * z + (x5 + x6) * z + (x6 + x7) * z + (x7 + x0) * z = 2 * (x0 * z) + 2 * (x1 * z) + 2 * (x2 * z) + 2 * (x3 * z) + 2 * (x4 * z) + 2 * (x5 * z) + 2 * (x6 * z) + 2 * (x7 * z) := by
  bench_noncomm "distribute-8" 30 0 (noncomm_ring)

example {R : Type*} [Ring R] (z x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : R) :
    (x0 + x1) * z + (x1 + x2) * z + (x2 + x3) * z + (x3 + x4) * z + (x4 + x5) * z + (x5 + x6) * z + (x6 + x7) * z + (x7 + x8) * z + (x8 + x9) * z + (x9 + x10) * z + (x10 + x11) * z + (x11 + x12) * z + (x12 + x13) * z + (x13 + x14) * z + (x14 + x15) * z + (x15 + x16) * z + (x16 + x17) * z + (x17 + x18) * z + (x18 + x19) * z + (x19 + x20) * z + (x20 + x21) * z + (x21 + x22) * z + (x22 + x23) * z + (x23 + x24) * z + (x24 + x25) * z + (x25 + x26) * z + (x26 + x27) * z + (x27 + x28) * z + (x28 + x29) * z + (x29 + x30) * z + (x30 + x31) * z + (x31 + x0) * z = 2 * (x0 * z) + 2 * (x1 * z) + 2 * (x2 * z) + 2 * (x3 * z) + 2 * (x4 * z) + 2 * (x5 * z) + 2 * (x6 * z) + 2 * (x7 * z) + 2 * (x8 * z) + 2 * (x9 * z) + 2 * (x10 * z) + 2 * (x11 * z) + 2 * (x12 * z) + 2 * (x13 * z) + 2 * (x14 * z) + 2 * (x15 * z) + 2 * (x16 * z) + 2 * (x17 * z) + 2 * (x18 * z) + 2 * (x19 * z) + 2 * (x20 * z) + 2 * (x21 * z) + 2 * (x22 * z) + 2 * (x23 * z) + 2 * (x24 * z) + 2 * (x25 * z) + 2 * (x26 * z) + 2 * (x27 * z) + 2 * (x28 * z) + 2 * (x29 * z) + 2 * (x30 * z) + 2 * (x31 * z) := by
  bench_noncomm "distribute-32" 10 0 (noncomm_ring)

example {R : Type*} [Ring R] (z x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 : R) :
    (x0 + x1) * z + (x1 + x2) * z + (x2 + x3) * z + (x3 + x4) * z + (x4 + x5) * z + (x5 + x6) * z + (x6 + x7) * z + (x7 + x8) * z + (x8 + x9) * z + (x9 + x10) * z + (x10 + x11) * z + (x11 + x12) * z + (x12 + x13) * z + (x13 + x14) * z + (x14 + x15) * z + (x15 + x16) * z + (x16 + x17) * z + (x17 + x18) * z + (x18 + x19) * z + (x19 + x20) * z + (x20 + x21) * z + (x21 + x22) * z + (x22 + x23) * z + (x23 + x24) * z + (x24 + x25) * z + (x25 + x26) * z + (x26 + x27) * z + (x27 + x28) * z + (x28 + x29) * z + (x29 + x30) * z + (x30 + x31) * z + (x31 + x32) * z + (x32 + x33) * z + (x33 + x34) * z + (x34 + x35) * z + (x35 + x36) * z + (x36 + x37) * z + (x37 + x38) * z + (x38 + x39) * z + (x39 + x40) * z + (x40 + x41) * z + (x41 + x42) * z + (x42 + x43) * z + (x43 + x44) * z + (x44 + x45) * z + (x45 + x46) * z + (x46 + x47) * z + (x47 + x48) * z + (x48 + x49) * z + (x49 + x50) * z + (x50 + x51) * z + (x51 + x52) * z + (x52 + x53) * z + (x53 + x54) * z + (x54 + x55) * z + (x55 + x56) * z + (x56 + x57) * z + (x57 + x58) * z + (x58 + x59) * z + (x59 + x60) * z + (x60 + x61) * z + (x61 + x62) * z + (x62 + x63) * z + (x63 + x0) * z = 2 * (x0 * z) + 2 * (x1 * z) + 2 * (x2 * z) + 2 * (x3 * z) + 2 * (x4 * z) + 2 * (x5 * z) + 2 * (x6 * z) + 2 * (x7 * z) + 2 * (x8 * z) + 2 * (x9 * z) + 2 * (x10 * z) + 2 * (x11 * z) + 2 * (x12 * z) + 2 * (x13 * z) + 2 * (x14 * z) + 2 * (x15 * z) + 2 * (x16 * z) + 2 * (x17 * z) + 2 * (x18 * z) + 2 * (x19 * z) + 2 * (x20 * z) + 2 * (x21 * z) + 2 * (x22 * z) + 2 * (x23 * z) + 2 * (x24 * z) + 2 * (x25 * z) + 2 * (x26 * z) + 2 * (x27 * z) + 2 * (x28 * z) + 2 * (x29 * z) + 2 * (x30 * z) + 2 * (x31 * z) + 2 * (x32 * z) + 2 * (x33 * z) + 2 * (x34 * z) + 2 * (x35 * z) + 2 * (x36 * z) + 2 * (x37 * z) + 2 * (x38 * z) + 2 * (x39 * z) + 2 * (x40 * z) + 2 * (x41 * z) + 2 * (x42 * z) + 2 * (x43 * z) + 2 * (x44 * z) + 2 * (x45 * z) + 2 * (x46 * z) + 2 * (x47 * z) + 2 * (x48 * z) + 2 * (x49 * z) + 2 * (x50 * z) + 2 * (x51 * z) + 2 * (x52 * z) + 2 * (x53 * z) + 2 * (x54 * z) + 2 * (x55 * z) + 2 * (x56 * z) + 2 * (x57 * z) + 2 * (x58 * z) + 2 * (x59 * z) + 2 * (x60 * z) + 2 * (x61 * z) + 2 * (x62 * z) + 2 * (x63 * z) := by
  bench_noncomm "distribute-64" 5 0 (noncomm_ring)

example {R : Type*} [Ring R] (a b c : R) :
    a * (b * c - c * b) - (b * c - c * b) * a +
    b * (c * a - a * c) - (c * a - a * c) * b +
    c * (a * b - b * a) - (a * b - b * a) * c = 0 := by
  bench_noncomm "jacobi" 50 0 (noncomm_ring)

example {R : Type*} [Ring R] (a : R) : a ^ 50 * a ^ 37 = a ^ 23 * a ^ 64 := by
  bench_noncomm "degree-87" 10 0 (noncomm_ring)

example {R : Type*} [Ring R] (a b : R) (P : R → Prop) (h : ∀ x, P x) :
    P ((a + b)^3) := by
  bench_noncomm "open-predicate-cube" 20 1 (noncomm_ring)
  exact h _

example {R₀ : Type*} [Ring R₀] (G Ginv P R : R₀)
    (hGinvG : Ginv * G = 1) (hGGinv : G * Ginv = 1) :
    4 * R - 2 * P - (G + R) * Ginv * P - P * Ginv * (G + R) +
        2 * (P * Ginv * P) =
      4 * (R - P) - (R - P) * Ginv * P - P * Ginv * (R - P) := by
  bench_noncomm "crouzeix-inverse-rewrites" 20 0 (noncomm_ring [hGinvG, hGGinv])

example {R : Type*} [Ring R] (a b c : R) (f : R → R) :
    f ((a + b) * c) + f ((b + a) * c) = 2 * f (a * c + b * c) := by
  bench_noncomm "recursive-atoms" 30 0 (noncomm_ring)
