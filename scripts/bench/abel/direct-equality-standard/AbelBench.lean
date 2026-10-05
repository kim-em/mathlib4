module
import AbelBenchCurrent
import JacobiOldAbel
public meta import Lean.Elab.Tactic

open Lean Meta Elab Tactic
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedTactic false

elab "bench_abel " label:str count:num remaining:num tac:tactic : tactic => do
  let saved ← saveState
  let trial := do
    saved.restore
    evalTactic tac
    let goals ← getUnsolvedGoals
    unless goals.length == remaining.getNat do
      throwError "unexpected residual goals: {goals}"
  for _ in [:3] do trial
  let start ← IO.monoNanosNow
  let hb ← IO.getNumHeartbeats
  for _ in [:count.getNat] do trial
  let elapsed := (← IO.monoNanosNow) - start
  let heartbeats := (← IO.getNumHeartbeats) - hb
  saved.restore
  logInfo m!"ABEL_BENCH {label.getString} {count.getNat} {elapsed} {heartbeats}"
  evalTactic tac

example {A : Type*} [AddCommMonoid A] (a b : A) :
    a + (b + a) = a + a + b := by
  bench_abel "monoid-small-1-A" 100 0 (jacobi_old_abel)

example {A : Type*} [AddCommMonoid A] (a b : A) :
    a + (b + a) = a + a + b := by
  bench_abel "monoid-small-1-B" 100 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (a b c d : A) :
    a + b + (c + d - a) = b + c + d := by
  bench_abel "group-subtraction-1-A" 100 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (a b c d : A) :
    a + b + (c + d - a) = b + c + d := by
  bench_abel "group-subtraction-1-B" 100 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x0) = 0 := by
  bench_abel "telescoping-8-1-A" 50 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x0) = 0 := by
  bench_abel "telescoping-8-1-B" 50 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x8) + (x8 - x9) + (x9 - x10) + (x10 - x11) + (x11 - x12) + (x12 - x13) + (x13 - x14) + (x14 - x15) + (x15 - x16) + (x16 - x17) + (x17 - x18) + (x18 - x19) + (x19 - x20) + (x20 - x21) + (x21 - x22) + (x22 - x23) + (x23 - x24) + (x24 - x25) + (x25 - x26) + (x26 - x27) + (x27 - x28) + (x28 - x29) + (x29 - x30) + (x30 - x31) + (x31 - x0) = 0 := by
  bench_abel "telescoping-32-1-A" 20 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x8) + (x8 - x9) + (x9 - x10) + (x10 - x11) + (x11 - x12) + (x12 - x13) + (x13 - x14) + (x14 - x15) + (x15 - x16) + (x16 - x17) + (x17 - x18) + (x18 - x19) + (x19 - x20) + (x20 - x21) + (x21 - x22) + (x22 - x23) + (x23 - x24) + (x24 - x25) + (x25 - x26) + (x26 - x27) + (x27 - x28) + (x28 - x29) + (x29 - x30) + (x30 - x31) + (x31 - x0) = 0 := by
  bench_abel "telescoping-32-1-B" 20 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x8) + (x8 - x9) + (x9 - x10) + (x10 - x11) + (x11 - x12) + (x12 - x13) + (x13 - x14) + (x14 - x15) + (x15 - x16) + (x16 - x17) + (x17 - x18) + (x18 - x19) + (x19 - x20) + (x20 - x21) + (x21 - x22) + (x22 - x23) + (x23 - x24) + (x24 - x25) + (x25 - x26) + (x26 - x27) + (x27 - x28) + (x28 - x29) + (x29 - x30) + (x30 - x31) + (x31 - x32) + (x32 - x33) + (x33 - x34) + (x34 - x35) + (x35 - x36) + (x36 - x37) + (x37 - x38) + (x38 - x39) + (x39 - x40) + (x40 - x41) + (x41 - x42) + (x42 - x43) + (x43 - x44) + (x44 - x45) + (x45 - x46) + (x46 - x47) + (x47 - x48) + (x48 - x49) + (x49 - x50) + (x50 - x51) + (x51 - x52) + (x52 - x53) + (x53 - x54) + (x54 - x55) + (x55 - x56) + (x56 - x57) + (x57 - x58) + (x58 - x59) + (x59 - x60) + (x60 - x61) + (x61 - x62) + (x62 - x63) + (x63 - x0) = 0 := by
  bench_abel "telescoping-64-1-A" 20 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x8) + (x8 - x9) + (x9 - x10) + (x10 - x11) + (x11 - x12) + (x12 - x13) + (x13 - x14) + (x14 - x15) + (x15 - x16) + (x16 - x17) + (x17 - x18) + (x18 - x19) + (x19 - x20) + (x20 - x21) + (x21 - x22) + (x22 - x23) + (x23 - x24) + (x24 - x25) + (x25 - x26) + (x26 - x27) + (x27 - x28) + (x28 - x29) + (x29 - x30) + (x30 - x31) + (x31 - x32) + (x32 - x33) + (x33 - x34) + (x34 - x35) + (x35 - x36) + (x36 - x37) + (x37 - x38) + (x38 - x39) + (x39 - x40) + (x40 - x41) + (x41 - x42) + (x42 - x43) + (x43 - x44) + (x44 - x45) + (x45 - x46) + (x46 - x47) + (x47 - x48) + (x48 - x49) + (x49 - x50) + (x50 - x51) + (x51 - x52) + (x52 - x53) + (x53 - x54) + (x54 - x55) + (x55 - x56) + (x56 - x57) + (x57 - x58) + (x58 - x59) + (x59 - x60) + (x60 - x61) + (x61 - x62) + (x62 - x63) + (x63 - x0) = 0 := by
  bench_abel "telescoping-64-1-B" 20 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : A) :
    ((3 : ℤ) • x0 - x1) + ((3 : ℤ) • x1 - x2) + ((3 : ℤ) • x2 - x3) + ((3 : ℤ) • x3 - x4) + ((3 : ℤ) • x4 - x5) + ((3 : ℤ) • x5 - x6) + ((3 : ℤ) • x6 - x7) + ((3 : ℤ) • x7 - x8) + ((3 : ℤ) • x8 - x9) + ((3 : ℤ) • x9 - x10) + ((3 : ℤ) • x10 - x11) + ((3 : ℤ) • x11 - x12) + ((3 : ℤ) • x12 - x13) + ((3 : ℤ) • x13 - x14) + ((3 : ℤ) • x14 - x15) + ((3 : ℤ) • x15 - x0) = (2 : ℤ) • x15 + (2 : ℤ) • x14 + (2 : ℤ) • x13 + (2 : ℤ) • x12 + (2 : ℤ) • x11 + (2 : ℤ) • x10 + (2 : ℤ) • x9 + (2 : ℤ) • x8 + (2 : ℤ) • x7 + (2 : ℤ) • x6 + (2 : ℤ) • x5 + (2 : ℤ) • x4 + (2 : ℤ) • x3 + (2 : ℤ) • x2 + (2 : ℤ) • x1 + (2 : ℤ) • x0 := by
  bench_abel "integer-coefficients-16-1-A" 20 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : A) :
    ((3 : ℤ) • x0 - x1) + ((3 : ℤ) • x1 - x2) + ((3 : ℤ) • x2 - x3) + ((3 : ℤ) • x3 - x4) + ((3 : ℤ) • x4 - x5) + ((3 : ℤ) • x5 - x6) + ((3 : ℤ) • x6 - x7) + ((3 : ℤ) • x7 - x8) + ((3 : ℤ) • x8 - x9) + ((3 : ℤ) • x9 - x10) + ((3 : ℤ) • x10 - x11) + ((3 : ℤ) • x11 - x12) + ((3 : ℤ) • x12 - x13) + ((3 : ℤ) • x13 - x14) + ((3 : ℤ) • x14 - x15) + ((3 : ℤ) • x15 - x0) = (2 : ℤ) • x15 + (2 : ℤ) • x14 + (2 : ℤ) • x13 + (2 : ℤ) • x12 + (2 : ℤ) • x11 + (2 : ℤ) • x10 + (2 : ℤ) • x9 + (2 : ℤ) • x8 + (2 : ℤ) • x7 + (2 : ℤ) • x6 + (2 : ℤ) • x5 + (2 : ℤ) • x4 + (2 : ℤ) • x3 + (2 : ℤ) • x2 + (2 : ℤ) • x1 + (2 : ℤ) • x0 := by
  bench_abel "integer-coefficients-16-1-B" 20 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (a : A) :
    (2 + 3 : ℤ) • a = (5 : ℤ) • a := by
  bench_abel "closed-coefficient-1-A" 100 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (a : A) :
    (2 + 3 : ℤ) • a = (5 : ℤ) • a := by
  bench_abel "closed-coefficient-1-B" 100 0 (bench_new_abel)

example (n : ℤ) :
    n + 1 = 2 + (n - 1) := by
  bench_abel "integer-constants-1-A" 100 0 (jacobi_old_abel)

example (n : ℤ) :
    n + 1 = 2 + (n - 1) := by
  bench_abel "integer-constants-1-B" 100 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (n : ℕ) (a b : A) :
    n • a + n • b - n • a = n • b := by
  bench_abel "symbolic-scalar-atoms-1-A" 100 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (n : ℕ) (a b : A) :
    n • a + n • b - n • a = n • b := by
  bench_abel "symbolic-scalar-atoms-1-B" 100 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (a b : A) (f : A → A) :
    f (a + (b + a)) + f ((a + a) + b) = (2 : ℤ) • f (b + (2 : ℤ) • a) := by
  bench_abel "recursive-atoms-1-A" 30 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (a b : A) (f : A → A) :
    f (a + (b + a)) + f ((a + a) + b) = (2 : ℤ) • f (b + (2 : ℤ) • a) := by
  bench_abel "recursive-atoms-1-B" 30 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (a b : A) (P : A → Prop) (h : P a) :
    P (a - b + b) := by
  bench_abel "open-predicate-1-A" 50 1 (jacobi_old_abel_nf)
  exact h

example {A : Type*} [AddCommGroup A] (a b : A) (P : A → Prop) (h : P a) :
    P (a - b + b) := by
  bench_abel "open-predicate-1-B" 50 1 (bench_new_abel_nf)
  exact h

example {A : Type*} [AddCommGroup A] (a b c : A) (h₁ : a + b - a = c) (h₂ : b - a + a = c) :
    a + (b - a) = c := by
  bench_abel "multiple-locations-1-A" 30 1 (jacobi_old_abel_nf at *)
  exact h₁

example {A : Type*} [AddCommGroup A] (a b c : A) (h₁ : a + b - a = c) (h₂ : b - a + a = c) :
    a + (b - a) = c := by
  bench_abel "multiple-locations-1-B" 30 1 (bench_new_abel_nf at *)
  exact h₁

example {A : Type*} [AddCommMonoid A] (a b : A) :
    a + (b + a) = a + a + b := by
  bench_abel "monoid-small-2-B" 100 0 (bench_new_abel)

example {A : Type*} [AddCommMonoid A] (a b : A) :
    a + (b + a) = a + a + b := by
  bench_abel "monoid-small-2-A" 100 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (a b c d : A) :
    a + b + (c + d - a) = b + c + d := by
  bench_abel "group-subtraction-2-B" 100 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (a b c d : A) :
    a + b + (c + d - a) = b + c + d := by
  bench_abel "group-subtraction-2-A" 100 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x0) = 0 := by
  bench_abel "telescoping-8-2-B" 50 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x0) = 0 := by
  bench_abel "telescoping-8-2-A" 50 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x8) + (x8 - x9) + (x9 - x10) + (x10 - x11) + (x11 - x12) + (x12 - x13) + (x13 - x14) + (x14 - x15) + (x15 - x16) + (x16 - x17) + (x17 - x18) + (x18 - x19) + (x19 - x20) + (x20 - x21) + (x21 - x22) + (x22 - x23) + (x23 - x24) + (x24 - x25) + (x25 - x26) + (x26 - x27) + (x27 - x28) + (x28 - x29) + (x29 - x30) + (x30 - x31) + (x31 - x0) = 0 := by
  bench_abel "telescoping-32-2-B" 20 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x8) + (x8 - x9) + (x9 - x10) + (x10 - x11) + (x11 - x12) + (x12 - x13) + (x13 - x14) + (x14 - x15) + (x15 - x16) + (x16 - x17) + (x17 - x18) + (x18 - x19) + (x19 - x20) + (x20 - x21) + (x21 - x22) + (x22 - x23) + (x23 - x24) + (x24 - x25) + (x25 - x26) + (x26 - x27) + (x27 - x28) + (x28 - x29) + (x29 - x30) + (x30 - x31) + (x31 - x0) = 0 := by
  bench_abel "telescoping-32-2-A" 20 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x8) + (x8 - x9) + (x9 - x10) + (x10 - x11) + (x11 - x12) + (x12 - x13) + (x13 - x14) + (x14 - x15) + (x15 - x16) + (x16 - x17) + (x17 - x18) + (x18 - x19) + (x19 - x20) + (x20 - x21) + (x21 - x22) + (x22 - x23) + (x23 - x24) + (x24 - x25) + (x25 - x26) + (x26 - x27) + (x27 - x28) + (x28 - x29) + (x29 - x30) + (x30 - x31) + (x31 - x32) + (x32 - x33) + (x33 - x34) + (x34 - x35) + (x35 - x36) + (x36 - x37) + (x37 - x38) + (x38 - x39) + (x39 - x40) + (x40 - x41) + (x41 - x42) + (x42 - x43) + (x43 - x44) + (x44 - x45) + (x45 - x46) + (x46 - x47) + (x47 - x48) + (x48 - x49) + (x49 - x50) + (x50 - x51) + (x51 - x52) + (x52 - x53) + (x53 - x54) + (x54 - x55) + (x55 - x56) + (x56 - x57) + (x57 - x58) + (x58 - x59) + (x59 - x60) + (x60 - x61) + (x61 - x62) + (x62 - x63) + (x63 - x0) = 0 := by
  bench_abel "telescoping-64-2-B" 20 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x8) + (x8 - x9) + (x9 - x10) + (x10 - x11) + (x11 - x12) + (x12 - x13) + (x13 - x14) + (x14 - x15) + (x15 - x16) + (x16 - x17) + (x17 - x18) + (x18 - x19) + (x19 - x20) + (x20 - x21) + (x21 - x22) + (x22 - x23) + (x23 - x24) + (x24 - x25) + (x25 - x26) + (x26 - x27) + (x27 - x28) + (x28 - x29) + (x29 - x30) + (x30 - x31) + (x31 - x32) + (x32 - x33) + (x33 - x34) + (x34 - x35) + (x35 - x36) + (x36 - x37) + (x37 - x38) + (x38 - x39) + (x39 - x40) + (x40 - x41) + (x41 - x42) + (x42 - x43) + (x43 - x44) + (x44 - x45) + (x45 - x46) + (x46 - x47) + (x47 - x48) + (x48 - x49) + (x49 - x50) + (x50 - x51) + (x51 - x52) + (x52 - x53) + (x53 - x54) + (x54 - x55) + (x55 - x56) + (x56 - x57) + (x57 - x58) + (x58 - x59) + (x59 - x60) + (x60 - x61) + (x61 - x62) + (x62 - x63) + (x63 - x0) = 0 := by
  bench_abel "telescoping-64-2-A" 20 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : A) :
    ((3 : ℤ) • x0 - x1) + ((3 : ℤ) • x1 - x2) + ((3 : ℤ) • x2 - x3) + ((3 : ℤ) • x3 - x4) + ((3 : ℤ) • x4 - x5) + ((3 : ℤ) • x5 - x6) + ((3 : ℤ) • x6 - x7) + ((3 : ℤ) • x7 - x8) + ((3 : ℤ) • x8 - x9) + ((3 : ℤ) • x9 - x10) + ((3 : ℤ) • x10 - x11) + ((3 : ℤ) • x11 - x12) + ((3 : ℤ) • x12 - x13) + ((3 : ℤ) • x13 - x14) + ((3 : ℤ) • x14 - x15) + ((3 : ℤ) • x15 - x0) = (2 : ℤ) • x15 + (2 : ℤ) • x14 + (2 : ℤ) • x13 + (2 : ℤ) • x12 + (2 : ℤ) • x11 + (2 : ℤ) • x10 + (2 : ℤ) • x9 + (2 : ℤ) • x8 + (2 : ℤ) • x7 + (2 : ℤ) • x6 + (2 : ℤ) • x5 + (2 : ℤ) • x4 + (2 : ℤ) • x3 + (2 : ℤ) • x2 + (2 : ℤ) • x1 + (2 : ℤ) • x0 := by
  bench_abel "integer-coefficients-16-2-B" 20 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : A) :
    ((3 : ℤ) • x0 - x1) + ((3 : ℤ) • x1 - x2) + ((3 : ℤ) • x2 - x3) + ((3 : ℤ) • x3 - x4) + ((3 : ℤ) • x4 - x5) + ((3 : ℤ) • x5 - x6) + ((3 : ℤ) • x6 - x7) + ((3 : ℤ) • x7 - x8) + ((3 : ℤ) • x8 - x9) + ((3 : ℤ) • x9 - x10) + ((3 : ℤ) • x10 - x11) + ((3 : ℤ) • x11 - x12) + ((3 : ℤ) • x12 - x13) + ((3 : ℤ) • x13 - x14) + ((3 : ℤ) • x14 - x15) + ((3 : ℤ) • x15 - x0) = (2 : ℤ) • x15 + (2 : ℤ) • x14 + (2 : ℤ) • x13 + (2 : ℤ) • x12 + (2 : ℤ) • x11 + (2 : ℤ) • x10 + (2 : ℤ) • x9 + (2 : ℤ) • x8 + (2 : ℤ) • x7 + (2 : ℤ) • x6 + (2 : ℤ) • x5 + (2 : ℤ) • x4 + (2 : ℤ) • x3 + (2 : ℤ) • x2 + (2 : ℤ) • x1 + (2 : ℤ) • x0 := by
  bench_abel "integer-coefficients-16-2-A" 20 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (a : A) :
    (2 + 3 : ℤ) • a = (5 : ℤ) • a := by
  bench_abel "closed-coefficient-2-B" 100 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (a : A) :
    (2 + 3 : ℤ) • a = (5 : ℤ) • a := by
  bench_abel "closed-coefficient-2-A" 100 0 (jacobi_old_abel)

example (n : ℤ) :
    n + 1 = 2 + (n - 1) := by
  bench_abel "integer-constants-2-B" 100 0 (bench_new_abel)

example (n : ℤ) :
    n + 1 = 2 + (n - 1) := by
  bench_abel "integer-constants-2-A" 100 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (n : ℕ) (a b : A) :
    n • a + n • b - n • a = n • b := by
  bench_abel "symbolic-scalar-atoms-2-B" 100 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (n : ℕ) (a b : A) :
    n • a + n • b - n • a = n • b := by
  bench_abel "symbolic-scalar-atoms-2-A" 100 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (a b : A) (f : A → A) :
    f (a + (b + a)) + f ((a + a) + b) = (2 : ℤ) • f (b + (2 : ℤ) • a) := by
  bench_abel "recursive-atoms-2-B" 30 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (a b : A) (f : A → A) :
    f (a + (b + a)) + f ((a + a) + b) = (2 : ℤ) • f (b + (2 : ℤ) • a) := by
  bench_abel "recursive-atoms-2-A" 30 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (a b : A) (P : A → Prop) (h : P a) :
    P (a - b + b) := by
  bench_abel "open-predicate-2-B" 50 1 (bench_new_abel_nf)
  exact h

example {A : Type*} [AddCommGroup A] (a b : A) (P : A → Prop) (h : P a) :
    P (a - b + b) := by
  bench_abel "open-predicate-2-A" 50 1 (jacobi_old_abel_nf)
  exact h

example {A : Type*} [AddCommGroup A] (a b c : A) (h₁ : a + b - a = c) (h₂ : b - a + a = c) :
    a + (b - a) = c := by
  bench_abel "multiple-locations-2-B" 30 1 (bench_new_abel_nf at *)
  exact h₁

example {A : Type*} [AddCommGroup A] (a b c : A) (h₁ : a + b - a = c) (h₂ : b - a + a = c) :
    a + (b - a) = c := by
  bench_abel "multiple-locations-2-A" 30 1 (jacobi_old_abel_nf at *)
  exact h₁

example {A : Type*} [AddCommMonoid A] (a b : A) :
    a + (b + a) = a + a + b := by
  bench_abel "monoid-small-3-A" 100 0 (jacobi_old_abel)

example {A : Type*} [AddCommMonoid A] (a b : A) :
    a + (b + a) = a + a + b := by
  bench_abel "monoid-small-3-B" 100 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (a b c d : A) :
    a + b + (c + d - a) = b + c + d := by
  bench_abel "group-subtraction-3-A" 100 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (a b c d : A) :
    a + b + (c + d - a) = b + c + d := by
  bench_abel "group-subtraction-3-B" 100 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x0) = 0 := by
  bench_abel "telescoping-8-3-A" 50 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x0) = 0 := by
  bench_abel "telescoping-8-3-B" 50 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x8) + (x8 - x9) + (x9 - x10) + (x10 - x11) + (x11 - x12) + (x12 - x13) + (x13 - x14) + (x14 - x15) + (x15 - x16) + (x16 - x17) + (x17 - x18) + (x18 - x19) + (x19 - x20) + (x20 - x21) + (x21 - x22) + (x22 - x23) + (x23 - x24) + (x24 - x25) + (x25 - x26) + (x26 - x27) + (x27 - x28) + (x28 - x29) + (x29 - x30) + (x30 - x31) + (x31 - x0) = 0 := by
  bench_abel "telescoping-32-3-A" 20 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x8) + (x8 - x9) + (x9 - x10) + (x10 - x11) + (x11 - x12) + (x12 - x13) + (x13 - x14) + (x14 - x15) + (x15 - x16) + (x16 - x17) + (x17 - x18) + (x18 - x19) + (x19 - x20) + (x20 - x21) + (x21 - x22) + (x22 - x23) + (x23 - x24) + (x24 - x25) + (x25 - x26) + (x26 - x27) + (x27 - x28) + (x28 - x29) + (x29 - x30) + (x30 - x31) + (x31 - x0) = 0 := by
  bench_abel "telescoping-32-3-B" 20 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x8) + (x8 - x9) + (x9 - x10) + (x10 - x11) + (x11 - x12) + (x12 - x13) + (x13 - x14) + (x14 - x15) + (x15 - x16) + (x16 - x17) + (x17 - x18) + (x18 - x19) + (x19 - x20) + (x20 - x21) + (x21 - x22) + (x22 - x23) + (x23 - x24) + (x24 - x25) + (x25 - x26) + (x26 - x27) + (x27 - x28) + (x28 - x29) + (x29 - x30) + (x30 - x31) + (x31 - x32) + (x32 - x33) + (x33 - x34) + (x34 - x35) + (x35 - x36) + (x36 - x37) + (x37 - x38) + (x38 - x39) + (x39 - x40) + (x40 - x41) + (x41 - x42) + (x42 - x43) + (x43 - x44) + (x44 - x45) + (x45 - x46) + (x46 - x47) + (x47 - x48) + (x48 - x49) + (x49 - x50) + (x50 - x51) + (x51 - x52) + (x52 - x53) + (x53 - x54) + (x54 - x55) + (x55 - x56) + (x56 - x57) + (x57 - x58) + (x58 - x59) + (x59 - x60) + (x60 - x61) + (x61 - x62) + (x62 - x63) + (x63 - x0) = 0 := by
  bench_abel "telescoping-64-3-A" 20 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x8) + (x8 - x9) + (x9 - x10) + (x10 - x11) + (x11 - x12) + (x12 - x13) + (x13 - x14) + (x14 - x15) + (x15 - x16) + (x16 - x17) + (x17 - x18) + (x18 - x19) + (x19 - x20) + (x20 - x21) + (x21 - x22) + (x22 - x23) + (x23 - x24) + (x24 - x25) + (x25 - x26) + (x26 - x27) + (x27 - x28) + (x28 - x29) + (x29 - x30) + (x30 - x31) + (x31 - x32) + (x32 - x33) + (x33 - x34) + (x34 - x35) + (x35 - x36) + (x36 - x37) + (x37 - x38) + (x38 - x39) + (x39 - x40) + (x40 - x41) + (x41 - x42) + (x42 - x43) + (x43 - x44) + (x44 - x45) + (x45 - x46) + (x46 - x47) + (x47 - x48) + (x48 - x49) + (x49 - x50) + (x50 - x51) + (x51 - x52) + (x52 - x53) + (x53 - x54) + (x54 - x55) + (x55 - x56) + (x56 - x57) + (x57 - x58) + (x58 - x59) + (x59 - x60) + (x60 - x61) + (x61 - x62) + (x62 - x63) + (x63 - x0) = 0 := by
  bench_abel "telescoping-64-3-B" 20 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : A) :
    ((3 : ℤ) • x0 - x1) + ((3 : ℤ) • x1 - x2) + ((3 : ℤ) • x2 - x3) + ((3 : ℤ) • x3 - x4) + ((3 : ℤ) • x4 - x5) + ((3 : ℤ) • x5 - x6) + ((3 : ℤ) • x6 - x7) + ((3 : ℤ) • x7 - x8) + ((3 : ℤ) • x8 - x9) + ((3 : ℤ) • x9 - x10) + ((3 : ℤ) • x10 - x11) + ((3 : ℤ) • x11 - x12) + ((3 : ℤ) • x12 - x13) + ((3 : ℤ) • x13 - x14) + ((3 : ℤ) • x14 - x15) + ((3 : ℤ) • x15 - x0) = (2 : ℤ) • x15 + (2 : ℤ) • x14 + (2 : ℤ) • x13 + (2 : ℤ) • x12 + (2 : ℤ) • x11 + (2 : ℤ) • x10 + (2 : ℤ) • x9 + (2 : ℤ) • x8 + (2 : ℤ) • x7 + (2 : ℤ) • x6 + (2 : ℤ) • x5 + (2 : ℤ) • x4 + (2 : ℤ) • x3 + (2 : ℤ) • x2 + (2 : ℤ) • x1 + (2 : ℤ) • x0 := by
  bench_abel "integer-coefficients-16-3-A" 20 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : A) :
    ((3 : ℤ) • x0 - x1) + ((3 : ℤ) • x1 - x2) + ((3 : ℤ) • x2 - x3) + ((3 : ℤ) • x3 - x4) + ((3 : ℤ) • x4 - x5) + ((3 : ℤ) • x5 - x6) + ((3 : ℤ) • x6 - x7) + ((3 : ℤ) • x7 - x8) + ((3 : ℤ) • x8 - x9) + ((3 : ℤ) • x9 - x10) + ((3 : ℤ) • x10 - x11) + ((3 : ℤ) • x11 - x12) + ((3 : ℤ) • x12 - x13) + ((3 : ℤ) • x13 - x14) + ((3 : ℤ) • x14 - x15) + ((3 : ℤ) • x15 - x0) = (2 : ℤ) • x15 + (2 : ℤ) • x14 + (2 : ℤ) • x13 + (2 : ℤ) • x12 + (2 : ℤ) • x11 + (2 : ℤ) • x10 + (2 : ℤ) • x9 + (2 : ℤ) • x8 + (2 : ℤ) • x7 + (2 : ℤ) • x6 + (2 : ℤ) • x5 + (2 : ℤ) • x4 + (2 : ℤ) • x3 + (2 : ℤ) • x2 + (2 : ℤ) • x1 + (2 : ℤ) • x0 := by
  bench_abel "integer-coefficients-16-3-B" 20 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (a : A) :
    (2 + 3 : ℤ) • a = (5 : ℤ) • a := by
  bench_abel "closed-coefficient-3-A" 100 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (a : A) :
    (2 + 3 : ℤ) • a = (5 : ℤ) • a := by
  bench_abel "closed-coefficient-3-B" 100 0 (bench_new_abel)

example (n : ℤ) :
    n + 1 = 2 + (n - 1) := by
  bench_abel "integer-constants-3-A" 100 0 (jacobi_old_abel)

example (n : ℤ) :
    n + 1 = 2 + (n - 1) := by
  bench_abel "integer-constants-3-B" 100 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (n : ℕ) (a b : A) :
    n • a + n • b - n • a = n • b := by
  bench_abel "symbolic-scalar-atoms-3-A" 100 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (n : ℕ) (a b : A) :
    n • a + n • b - n • a = n • b := by
  bench_abel "symbolic-scalar-atoms-3-B" 100 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (a b : A) (f : A → A) :
    f (a + (b + a)) + f ((a + a) + b) = (2 : ℤ) • f (b + (2 : ℤ) • a) := by
  bench_abel "recursive-atoms-3-A" 30 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (a b : A) (f : A → A) :
    f (a + (b + a)) + f ((a + a) + b) = (2 : ℤ) • f (b + (2 : ℤ) • a) := by
  bench_abel "recursive-atoms-3-B" 30 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (a b : A) (P : A → Prop) (h : P a) :
    P (a - b + b) := by
  bench_abel "open-predicate-3-A" 50 1 (jacobi_old_abel_nf)
  exact h

example {A : Type*} [AddCommGroup A] (a b : A) (P : A → Prop) (h : P a) :
    P (a - b + b) := by
  bench_abel "open-predicate-3-B" 50 1 (bench_new_abel_nf)
  exact h

example {A : Type*} [AddCommGroup A] (a b c : A) (h₁ : a + b - a = c) (h₂ : b - a + a = c) :
    a + (b - a) = c := by
  bench_abel "multiple-locations-3-A" 30 1 (jacobi_old_abel_nf at *)
  exact h₁

example {A : Type*} [AddCommGroup A] (a b c : A) (h₁ : a + b - a = c) (h₂ : b - a + a = c) :
    a + (b - a) = c := by
  bench_abel "multiple-locations-3-B" 30 1 (bench_new_abel_nf at *)
  exact h₁

example {A : Type*} [AddCommMonoid A] (a b : A) :
    a + (b + a) = a + a + b := by
  bench_abel "monoid-small-4-B" 100 0 (bench_new_abel)

example {A : Type*} [AddCommMonoid A] (a b : A) :
    a + (b + a) = a + a + b := by
  bench_abel "monoid-small-4-A" 100 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (a b c d : A) :
    a + b + (c + d - a) = b + c + d := by
  bench_abel "group-subtraction-4-B" 100 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (a b c d : A) :
    a + b + (c + d - a) = b + c + d := by
  bench_abel "group-subtraction-4-A" 100 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x0) = 0 := by
  bench_abel "telescoping-8-4-B" 50 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x0) = 0 := by
  bench_abel "telescoping-8-4-A" 50 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x8) + (x8 - x9) + (x9 - x10) + (x10 - x11) + (x11 - x12) + (x12 - x13) + (x13 - x14) + (x14 - x15) + (x15 - x16) + (x16 - x17) + (x17 - x18) + (x18 - x19) + (x19 - x20) + (x20 - x21) + (x21 - x22) + (x22 - x23) + (x23 - x24) + (x24 - x25) + (x25 - x26) + (x26 - x27) + (x27 - x28) + (x28 - x29) + (x29 - x30) + (x30 - x31) + (x31 - x0) = 0 := by
  bench_abel "telescoping-32-4-B" 20 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x8) + (x8 - x9) + (x9 - x10) + (x10 - x11) + (x11 - x12) + (x12 - x13) + (x13 - x14) + (x14 - x15) + (x15 - x16) + (x16 - x17) + (x17 - x18) + (x18 - x19) + (x19 - x20) + (x20 - x21) + (x21 - x22) + (x22 - x23) + (x23 - x24) + (x24 - x25) + (x25 - x26) + (x26 - x27) + (x27 - x28) + (x28 - x29) + (x29 - x30) + (x30 - x31) + (x31 - x0) = 0 := by
  bench_abel "telescoping-32-4-A" 20 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x8) + (x8 - x9) + (x9 - x10) + (x10 - x11) + (x11 - x12) + (x12 - x13) + (x13 - x14) + (x14 - x15) + (x15 - x16) + (x16 - x17) + (x17 - x18) + (x18 - x19) + (x19 - x20) + (x20 - x21) + (x21 - x22) + (x22 - x23) + (x23 - x24) + (x24 - x25) + (x25 - x26) + (x26 - x27) + (x27 - x28) + (x28 - x29) + (x29 - x30) + (x30 - x31) + (x31 - x32) + (x32 - x33) + (x33 - x34) + (x34 - x35) + (x35 - x36) + (x36 - x37) + (x37 - x38) + (x38 - x39) + (x39 - x40) + (x40 - x41) + (x41 - x42) + (x42 - x43) + (x43 - x44) + (x44 - x45) + (x45 - x46) + (x46 - x47) + (x47 - x48) + (x48 - x49) + (x49 - x50) + (x50 - x51) + (x51 - x52) + (x52 - x53) + (x53 - x54) + (x54 - x55) + (x55 - x56) + (x56 - x57) + (x57 - x58) + (x58 - x59) + (x59 - x60) + (x60 - x61) + (x61 - x62) + (x62 - x63) + (x63 - x0) = 0 := by
  bench_abel "telescoping-64-4-B" 20 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 : A) :
    (x0 - x1) + (x1 - x2) + (x2 - x3) + (x3 - x4) + (x4 - x5) + (x5 - x6) + (x6 - x7) + (x7 - x8) + (x8 - x9) + (x9 - x10) + (x10 - x11) + (x11 - x12) + (x12 - x13) + (x13 - x14) + (x14 - x15) + (x15 - x16) + (x16 - x17) + (x17 - x18) + (x18 - x19) + (x19 - x20) + (x20 - x21) + (x21 - x22) + (x22 - x23) + (x23 - x24) + (x24 - x25) + (x25 - x26) + (x26 - x27) + (x27 - x28) + (x28 - x29) + (x29 - x30) + (x30 - x31) + (x31 - x32) + (x32 - x33) + (x33 - x34) + (x34 - x35) + (x35 - x36) + (x36 - x37) + (x37 - x38) + (x38 - x39) + (x39 - x40) + (x40 - x41) + (x41 - x42) + (x42 - x43) + (x43 - x44) + (x44 - x45) + (x45 - x46) + (x46 - x47) + (x47 - x48) + (x48 - x49) + (x49 - x50) + (x50 - x51) + (x51 - x52) + (x52 - x53) + (x53 - x54) + (x54 - x55) + (x55 - x56) + (x56 - x57) + (x57 - x58) + (x58 - x59) + (x59 - x60) + (x60 - x61) + (x61 - x62) + (x62 - x63) + (x63 - x0) = 0 := by
  bench_abel "telescoping-64-4-A" 20 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : A) :
    ((3 : ℤ) • x0 - x1) + ((3 : ℤ) • x1 - x2) + ((3 : ℤ) • x2 - x3) + ((3 : ℤ) • x3 - x4) + ((3 : ℤ) • x4 - x5) + ((3 : ℤ) • x5 - x6) + ((3 : ℤ) • x6 - x7) + ((3 : ℤ) • x7 - x8) + ((3 : ℤ) • x8 - x9) + ((3 : ℤ) • x9 - x10) + ((3 : ℤ) • x10 - x11) + ((3 : ℤ) • x11 - x12) + ((3 : ℤ) • x12 - x13) + ((3 : ℤ) • x13 - x14) + ((3 : ℤ) • x14 - x15) + ((3 : ℤ) • x15 - x0) = (2 : ℤ) • x15 + (2 : ℤ) • x14 + (2 : ℤ) • x13 + (2 : ℤ) • x12 + (2 : ℤ) • x11 + (2 : ℤ) • x10 + (2 : ℤ) • x9 + (2 : ℤ) • x8 + (2 : ℤ) • x7 + (2 : ℤ) • x6 + (2 : ℤ) • x5 + (2 : ℤ) • x4 + (2 : ℤ) • x3 + (2 : ℤ) • x2 + (2 : ℤ) • x1 + (2 : ℤ) • x0 := by
  bench_abel "integer-coefficients-16-4-B" 20 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : A) :
    ((3 : ℤ) • x0 - x1) + ((3 : ℤ) • x1 - x2) + ((3 : ℤ) • x2 - x3) + ((3 : ℤ) • x3 - x4) + ((3 : ℤ) • x4 - x5) + ((3 : ℤ) • x5 - x6) + ((3 : ℤ) • x6 - x7) + ((3 : ℤ) • x7 - x8) + ((3 : ℤ) • x8 - x9) + ((3 : ℤ) • x9 - x10) + ((3 : ℤ) • x10 - x11) + ((3 : ℤ) • x11 - x12) + ((3 : ℤ) • x12 - x13) + ((3 : ℤ) • x13 - x14) + ((3 : ℤ) • x14 - x15) + ((3 : ℤ) • x15 - x0) = (2 : ℤ) • x15 + (2 : ℤ) • x14 + (2 : ℤ) • x13 + (2 : ℤ) • x12 + (2 : ℤ) • x11 + (2 : ℤ) • x10 + (2 : ℤ) • x9 + (2 : ℤ) • x8 + (2 : ℤ) • x7 + (2 : ℤ) • x6 + (2 : ℤ) • x5 + (2 : ℤ) • x4 + (2 : ℤ) • x3 + (2 : ℤ) • x2 + (2 : ℤ) • x1 + (2 : ℤ) • x0 := by
  bench_abel "integer-coefficients-16-4-A" 20 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (a : A) :
    (2 + 3 : ℤ) • a = (5 : ℤ) • a := by
  bench_abel "closed-coefficient-4-B" 100 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (a : A) :
    (2 + 3 : ℤ) • a = (5 : ℤ) • a := by
  bench_abel "closed-coefficient-4-A" 100 0 (jacobi_old_abel)

example (n : ℤ) :
    n + 1 = 2 + (n - 1) := by
  bench_abel "integer-constants-4-B" 100 0 (bench_new_abel)

example (n : ℤ) :
    n + 1 = 2 + (n - 1) := by
  bench_abel "integer-constants-4-A" 100 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (n : ℕ) (a b : A) :
    n • a + n • b - n • a = n • b := by
  bench_abel "symbolic-scalar-atoms-4-B" 100 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (n : ℕ) (a b : A) :
    n • a + n • b - n • a = n • b := by
  bench_abel "symbolic-scalar-atoms-4-A" 100 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (a b : A) (f : A → A) :
    f (a + (b + a)) + f ((a + a) + b) = (2 : ℤ) • f (b + (2 : ℤ) • a) := by
  bench_abel "recursive-atoms-4-B" 30 0 (bench_new_abel)

example {A : Type*} [AddCommGroup A] (a b : A) (f : A → A) :
    f (a + (b + a)) + f ((a + a) + b) = (2 : ℤ) • f (b + (2 : ℤ) • a) := by
  bench_abel "recursive-atoms-4-A" 30 0 (jacobi_old_abel)

example {A : Type*} [AddCommGroup A] (a b : A) (P : A → Prop) (h : P a) :
    P (a - b + b) := by
  bench_abel "open-predicate-4-B" 50 1 (bench_new_abel_nf)
  exact h

example {A : Type*} [AddCommGroup A] (a b : A) (P : A → Prop) (h : P a) :
    P (a - b + b) := by
  bench_abel "open-predicate-4-A" 50 1 (jacobi_old_abel_nf)
  exact h

example {A : Type*} [AddCommGroup A] (a b c : A) (h₁ : a + b - a = c) (h₂ : b - a + a = c) :
    a + (b - a) = c := by
  bench_abel "multiple-locations-4-B" 30 1 (bench_new_abel_nf at *)
  exact h₁

example {A : Type*} [AddCommGroup A] (a b c : A) (h₁ : a + b - a = c) (h₂ : b - a + a = c) :
    a + (b - a) = c := by
  bench_abel "multiple-locations-4-A" 30 1 (jacobi_old_abel_nf at *)
  exact h₁

