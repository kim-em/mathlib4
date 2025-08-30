/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Batteries.Data.Rat.Float
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Analysis.Real.Pi.AsTask
import Batteries.Util.Pickle
import Mathlib.Tactic.Eval

/-!
# Chudnovsky's formula for π

This file defines the infinite sum in Chudnovsky's formula for computing π⁻¹.
It does not (yet!) contain a proof; anyone is welcome to adopt this problem.

## Main definitions

* `chudnovskySum` : The infinite sum in Chudnovsky's formula

## Future work

* Prove the sum equals π⁻¹, as stated using `proof_wanted` below.
* Show that each imaginary quadratic field of class number 1 (corresponding to Heegner numbers)
  gives a Ramanujan type formula, and that this is the formula coming from 163,
  with $$j(\frac{1+\sqrt{-163}}{2}) = -640320^3$$, and the other magic constants coming from
  Eisenstein series.

## References
* [Milla, *A detailed proof of the Chudnovsky formula*][Milla_2018]
* [Chen and Glebov, *On Chudnovsky--Ramanujan type formulae*][Chen_Glebov_2018]

-/

open scoped Real BigOperators
open Nat

/-- The numerator of the nth term in Chudnovsky's series -/
def chudnovskyNum (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ n * (6 * n)! * (545140134 * n + 13591409)

/-- The denominator of the nth term in Chudnovsky's series -/
def chudnovskyDenom (n : ℕ) : ℕ :=
  (3 * n)! * (n)! ^ 3 * 640320 ^ (3 * n)

/-- The term at index n in Chudnovsky's series for π⁻¹ -/
def chudnovskyTerm (n : ℕ) : ℚ :=
  chudnovskyNum n / chudnovskyDenom n

-- Sanity check that when calculated in `Float` we get the right answer:
/-- info: 3.141593 -/
#guard_msgs in
#eval 1 / (12 / (640320 : Float) ^ (3 / 2) *
  (List.ofFn fun n : Fin 37 => (chudnovskyTerm n).toFloat).sum)

/-- The infinite sum in Chudnovsky's formula for π⁻¹ -/
noncomputable def chudnovskySum : ℝ :=
  12 / (640320 : ℝ) ^ (3 / 2) * ∑' n : ℕ, (chudnovskyTerm n : ℝ)

/-- **Chudnovsky's formula**: The sum equals π⁻¹ -/
proof_wanted chudnovskySum_eq_pi_inv : chudnovskySum = π⁻¹

namespace Chudnovsky

/-- The constant C = 640320^3 used in the binary splitting -/
def C : ℕ := 640320 ^ 3

/-- The A(k) term: 13591409 + 545140134 * k -/
def A (k : ℕ) : ℤ := 13591409 + 545140134 * k

/-- The p(j) function: -∏_{t=1}^6 (6j+t) for building up factorials incrementally -/
def p (j : ℕ) : ℤ :=
  let base := 6 * j
  (-((base + 1 : ℤ) * (base + 2) * (base + 3) * (base + 4) * (base + 5) * (base + 6)))

/-- The q(j) function: ∏_{t=1}^3 (3j+t) * (j+1)^3 * C for building up denominators incrementally -/
def q (j : ℕ) : ℤ :=
  let base := 3 * j
  (base + 1 : ℤ) * (base + 2) * (base + 3) * ((j + 1 : ℤ) ^ 3) * (640320 ^ 3 : ℤ)

/-- Binary splitting algorithm for computing the Chudnovsky sum.
    Returns (P, Q, T) such that T/Q = Σ_{k=n}^{m-1} chudnovskyTerm k -/
def binarySplit (n m : ℕ) : ℤ × ℤ × ℤ :=
  if n < m then
    if n + 1 = m then
      (p n, q n, A n * q n)
    else
      let r := n + (m - n) / 2
      let (p1, q1, t1) := binarySplit n r
      let (p2, q2, t2) := binarySplit r m
      (p1 * p2, q1 * q2, t1 * q2 + p1 * t2)
  else
    (1, 1, 0)
termination_by m - n

theorem binarySplit_helper_1 (n m : ℕ) (h : n + 1 = m) (p0 q0 t0 : ℤ)
    (hp : p0 = p n) (hq : q0 = q n) (ht : t0 = A n * q n) :
    binarySplit n m = (p0, q0, t0) := by
  rw [binarySplit, if_pos (by omega), if_pos h, hp, hq, ht]

theorem binarySplit_helper_2 (n m : ℕ) (h : Nat.blt (n + 1) m = true)
    {p0 q0 t0 p1 q1 t1 p2 q2 t2 : ℤ} {r : ℕ} (hr : r = n + (m - n) / 2)
    (w1 : binarySplit n r = (p1, q1, t1))
    (w2 : binarySplit r m = (p2, q2, t2))
    (hp : p0 = p1 * p2)
    (hq : q0 = q1 * q2)
    (ht : t0 = t1 * q2 + p1 * t2) :
    binarySplit n m = (p0, q0, t0) := by
  rw [binarySplit]
  simp at h
  rw [if_pos (by omega), if_neg (by omega), ← hr]
  dsimp only
  rw [w1, w2]
  dsimp
  rw [hp, hq, ht]

theorem binarySplit_helper_3 (n m : ℕ) (h : Nat.ble m n = true) :
    binarySplit n m = (1, 1, 0) := by
  simp at h
  rw [binarySplit, if_neg (by omega)]


open Qq Lean Meta

def binarySplit_helper_2_expr (n m : ℕ) (p0 q0 t0 p1 q1 t1 p2 q2 t2 : ℤ) (r : ℕ) (w1 w2 : Expr) :
    MetaM Expr := do
  pure <|
    mkApp3 (mkApp4 (mkApp9
      (mkApp3 (mkConst ``binarySplit_helper_2 []) (toExpr n) (toExpr m)
        (← mkEqRefl q(Nat.blt ($n + 1) $m)))
      (toExpr p0) (toExpr q0) (toExpr t0) (toExpr p1) (toExpr q1) (toExpr t1)
        (toExpr p2) (toExpr q2) (toExpr t2)) (toExpr r) (← mkEqRefl q($r)) w1 w2)
        (← mkEqRefl q($p0)) (← mkEqRefl q($q0)) (← mkEqRefl q($t0))

def binarySplit_proof (n m : ℕ) : MetaM ((ℤ × ℤ × ℤ) × Expr) := do
  if n < m then
    if n + 1 = m then
      let (p0, q0, t0) := (p n, q n, A n * q n)
      return ((p0, q0, t0),
        mkApp9 (mkConst ``binarySplit_helper_1 [])
          (toExpr n) (toExpr m) (← mkEqRefl q($n + 1)) (toExpr p0) (toExpr q0) (toExpr t0)
          (← mkEqRefl q($p0)) (← mkEqRefl q($q0)) (← mkEqRefl q($t0)))
    else
      let r := n + (m - n) / 2
      let ((p1, q1, t1), e1) ← binarySplit_proof n r
      let ((p2, q2, t2), e2) ← binarySplit_proof r m
      let p0 := p1 * p2
      let q0 := q1 * q2
      let t0 := t1 * q2 + p1 * t2
      let e1 ← abstractProof e1
      let e2 ← abstractProof e2
      let e ←
        binarySplit_helper_2_expr n m p0 q0 t0 p1 q1 t1 p2 q2 t2 r e1 e2
      return ((p0, q0, t0), e)
  else
    let (p0, q0, t0) := (1, 1, 0)
    return ((p0, q0, t0), mkApp3 (mkConst ``binarySplit_helper_3 [])
      (toExpr n) (toExpr m) (← mkEqRefl q(Nat.ble $m $n)))

open Lean Elab Tactic
def binarySplit_tac : TacticM Unit := do
  let g ← getMainGoal
  match_expr ← getMainTarget with
  | Eq _ x _ =>
    match_expr x with
    | binarySplit n m =>
      let some n := n.nat? | failure
      let some m := m.nat? | failure
      let (_, e) ← binarySplit_proof n m
      g.assign e
    | _ => failure
  | _ => failure

elab "binary_split_tac" : tactic => binarySplit_tac

example : binarySplit 0 1 = (-720, 1575224475844608000, 21409520118014687772672000) := by
  binary_split_tac

def pickleBinarySplit (n m : ℕ) : IO Unit := do
  pickle s!"Mathlib/Analysis/Real/Pi/chudnovsky_{n}_{m}.olean" ((n, m), binarySplit n m)

-- #eval pickleBinarySplit 0 1
-- #eval pickleBinarySplit 0 10
-- #eval pickleBinarySplit 0 100
-- #eval pickleBinarySplit 0 1000
-- #eval pickleBinarySplit 0 2000
-- #eval pickleBinarySplit 0 5000
-- #eval pickleBinarySplit 0 10000
-- #eval pickleBinarySplit 0 71000

def unpickleBinarySplit (n m : ℕ) : IO (ℤ × ℤ × ℤ) := unsafe do
  withUnpickle s!"Mathlib/Analysis/Real/Pi/chudnovsky_{n}_{m}.olean"
    fun t : ((ℕ × ℕ) × (ℤ × ℤ × ℤ)) =>
      if t.1.1 ≠ n ∨ t.1.2 ≠ m then
        throw <| IO.userError s!"Badly pickled file!"
      else
        return (t.2.1 * 1, t.2.2.1 * 1, t.2.2.2 * 1)

open Lean.Elab.Term in
elab "unpickleBinarySplit!" n:num m:num : term => unsafe do
  let n := n.getNat
  let m := m.getNat
  let (p, q, t) ← unpickleBinarySplit n m
  return toExpr (p, q, t)

#eval (binarySplit 0 71000).2.2.natAbs.log2
#eval (unpickleBinarySplit! 0 71000).2.2.natAbs.log2


-- set_option profiler true in  -- about 1s
-- theorem f1000 : binarySplit 0 1000 = eval% binarySplit 0 1000 := by binary_split_tac

-- set_option profiler true in  -- about 2s
-- theorem f2000 : binarySplit 0 2000 = eval% binarySplit 0 2000 := by binary_split_tac

-- set_option profiler true in  -- about 6s
-- theorem f5000 : binarySplit 0 5000 = eval% binarySplit 0 5000 := by binary_split_tac

-- set_option profiler true in  -- about 11s
-- theorem f10000 : binarySplit 0 10000 = eval% binarySplit 0 10000 := by binary_split_tac

-- set_option profiler true in
-- theorem f20000 : binarySplit 0 20000 = eval% binarySplit 0 20000 := by binary_split_tac

set_option profiler true in
theorem f30000 : binarySplit 0 30000 = eval% binarySplit 0 30000 := by binary_split_tac

-- set_option profiler true in
-- theorem f40000 : binarySplit 0 40000 = eval% binarySplit 0 40000 := by binary_split_tac

-- set_option profiler true in
-- theorem f50000 : binarySplit 0 50000 = eval% binarySplit 0 50000 := by binary_split_tac

-- set_option profiler true in
-- theorem f60000 : binarySplit 0 60000 = eval% binarySplit 0 60000 := by binary_split_tac


-- set_option profiler true in
-- -- `chudnovskyTerm 71000 < 10^(-1,001,000)`,
-- -- so this suffices to get `π` to over a million decimal places
-- theorem f71000 : binarySplit 0 71000 = eval% binarySplit 0 71000 := by binary_split_tac
#exit
/--
Variant of `binarySplit` that takes a fuel parameter, for evaluation in the kernel.
-/
def binarySplitFuel (fuel : ℕ) (n m : ℕ) (h : m - n < 2 ^ fuel + 1) : ℤ × ℤ × ℤ :=
  match fuel with
  | 0 =>
    if n = m then (1, 1, 0)
    else (p n, q n, A n * q n)
  | fuel + 1 =>
    if n < m then
      if n + 1 = m then
        (p n, q n, A n * q n)
      else
        let r := n + (m - n) / 2
        let (p1, q1, t1) := binarySplitFuel fuel n r (by omega)
        let (p2, q2, t2) := binarySplitFuel fuel r m (by omega)
        (p1 * p2, q1 * q2, t1 * q2 + p1 * t2)
    else
      (1, 1, 0)

def binarySplitFuel' (n m : ℕ) : ℤ × ℤ × ℤ :=
  binarySplitFuel ((m - n).log2 + 1) n m (by have := Nat.lt_log2_self (n := m - n); omega)

/-- Compute the sum of the first N Chudnovsky terms using binary splitting -/
def binarySplitSum (N : ℕ) : ℚ :=
  let (_, q, t) := binarySplitFuel' 0 N
  t / q

/-- info: true -/
#guard_msgs in
#eval let n := 163; binarySplitSum n = (List.ofFn fun n : Fin n => chudnovskyTerm n).sum

-- This will work on `v4.24.0-rc1`.
example : let n := 163; binarySplitSum n = (List.ofFn fun n : Fin n => chudnovskyTerm n).sum := by
  decide +kernel



/-- info: 0 -/
#guard_msgs in
#eval let n := 9; (2^(10^n) : Nat).log2 - 10^n
example : let n := 7; Nat.log 2 (2^(10^n) : Nat) = 10^n := by norm_num
example : let n := 4; (2^(10^n) : Nat).log2 = 10^n := by decide +kernel
example : let n := 2; (2^(10^n) : Nat).log2 = 10^n := by rfl

-- 70,000 terms would give about 1,000,000 digits of π; we can #eval that no problem.
/-- info: 21074918 -/
#guard_msgs in
#eval let n := 70000; let (_, q, t) := binarySplitFuel' 0 n; q.toNat.log2 + t.toNat.log2

-- But in the kernel we can only get around 150, enough for 2,000 digits of π
set_option maxRecDepth 100000 in
example :
  let n := 163
  let (_, q, t) := binarySplitFuel' 0 n
  q.toNat.log2 + t.toNat.log2 = 32030 := rfl -- or `by decide +kernel`

end Chudnovsky
