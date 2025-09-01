/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Batteries.Data.Rat.Float
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Analysis.Real.Pi.AsTask
import Batteries.Util.Pickle
import Mathlib.Tactic.Eval
import Std.Data.HashMap.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Batteries.Data.Rat.Float

/-!
# Chudnovsky's formula for π

This file defines the infinite sum in Chudnovsky's formula for computing `π⁻¹`.
It does not (yet!) contain a proof; anyone is welcome to adopt this problem,
but at present we are a long way off.

## Main definitions

* `chudnovskySum`: The infinite sum in Chudnovsky's formula

## Future work

* Use this formula to give approximations for `π`.
* Prove the sum equals `π⁻¹`, as stated using `proof_wanted` below.
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

/-- The term at index `n` in Chudnovsky's series for `π⁻¹` -/
def chudnovskyTerm (n : ℕ) : ℚ :=
  chudnovskyNum n / chudnovskyDenom n

-- Sanity check that when calculated in `Float` we get the right answer:
/-- info: 3.141593 -/
#guard_msgs in
#eval 1 / (12 / (640320 : Float) ^ (3 / 2) *
  (List.ofFn fun n : Fin 37 => (chudnovskyTerm n).toFloat).sum)

/-- The infinite sum in Chudnovsky's formula for `π⁻¹` -/
noncomputable def chudnovskySum : ℝ :=
  12 / (640320 : ℝ) ^ (3 / 2 : ℝ) * ∑' n : ℕ, (chudnovskyTerm n : ℝ)

/-- **Chudnovsky's formula**: The sum equals `π⁻¹` -/
proof_wanted chudnovskySum_eq_pi_inv : chudnovskySum = π⁻¹

namespace Chudnovsky

/-- The constant C = 640320^3 used in the binary splitting -/
def C : ℕ := 640320 ^ 3

/-- The A(k) term: 13591409 + 545140134 * k -/
def A (k : ℕ) : ℕ := 13591409 + 545140134 * k

/-- The p(j) function: -∏_{t=1}^6 (6j+t) for building up factorials incrementally -/
def p (j : ℕ) : ℤ :=
  let base := 6 * j
  (-((base + 1 : ℤ) * (base + 2) * (base + 3) * (base + 4) * (base + 5) * (base + 6)))

/-- The q(j) function: ∏_{t=1}^3 (3j+t) * (j+1)^3 * C for building up denominators incrementally -/
def q (j : ℕ) : ℕ :=
  let base := 3 * j
  (base + 1) * (base + 2) * (base + 3) * ((j + 1) ^ 3) * (640320 ^ 3)

/-- Binary splitting algorithm for computing the Chudnovsky sum.
    Returns (P, Q, T) such that T/Q = Σ_{k=n}^{m-1} chudnovskyTerm k -/
def binarySplit (n m : ℕ) : ℤ × ℕ × ℤ :=
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

theorem binarySplit_fst (n m : ℕ) :
    (binarySplit n m).1 = ∏ k ∈ Finset.Ico n m, p k := by
  rw [binarySplit]
  split <;> rename_i h
  · split <;> rename_i h'
    · subst h'
      simp
    · dsimp
      rw [binarySplit_fst, binarySplit_fst, Finset.prod_Ico_consecutive] <;> grind
  · have : Finset.Ico n m = ∅ := Finset.Ico_eq_empty h
    simp_all

theorem binarySplit_snd_fst (n m : ℕ) :
    (binarySplit n m).2.1 = ∏ k ∈ Finset.Ico n m, q k := by
  rw [binarySplit]
  split <;> rename_i h
  · split <;> rename_i h'
    · subst h'
      simp
    · dsimp
      rw [binarySplit_snd_fst, binarySplit_snd_fst, Finset.prod_Ico_consecutive] <;> grind
  · have : Finset.Ico n m = ∅ := Finset.Ico_eq_empty h
    simp_all

theorem binarySplit_snd_snd (n m : ℕ) :
    (binarySplit n m).2.2 =
      ∑ k ∈ Finset.Ico n m, A k * (∏ j ∈ Finset.Ico n k, p j) * (∏ j ∈ Finset.Ico k m, q j) := by
  rw [binarySplit]
  split <;> rename_i h
  · split <;> rename_i h'
    · subst h'
      simp
    · dsimp
      rw [binarySplit_fst, binarySplit_snd_fst, binarySplit_snd_snd, binarySplit_snd_snd]
      rw [Finset.sum_mul, Finset.mul_sum]
      conv =>
        rhs
        rw [← Finset.sum_Ico_consecutive _ (n := n + (m - n) / 2) (by grind) (by grind)]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        simp at hk
        simp only [mul_assoc]
        push_cast
        congr 2
        rw [Finset.prod_Ico_consecutive] <;> grind
      · apply Finset.sum_congr rfl
        intro k hk
        simp at hk
        simp only [mul_assoc]
        push_cast
        rw [mul_left_comm]
        congr 1
        rw [← mul_assoc]
        rw [Finset.prod_Ico_consecutive] <;> grind
  · have : Finset.Ico n m = ∅ := Finset.Ico_eq_empty h
    simp_all

/-- Compute the Chudnovsky partial sum using binary splitting -/
def binarySplitSum (n : ℕ) : ℚ :=
  let (_, q, t) := binarySplit 0 n
  t / q

def partialSum (n m : ℕ) : ℚ :=
  ∑ k ∈ Finset.Ico n m, chudnovskyTerm k

theorem prod_p {k} : ∏ i ∈ Finset.Ico 0 k, (p i : ℚ) = (-1)^k * (6 * k)! := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_Ico_succ_top (by grind), ih]
    simp [p, Nat.mul_add, factorial_succ, pow_succ]
    grind

theorem prod_q {k n} (h : k ≤ n) :
    ∏ x ∈ Finset.Ico k n, (q x : ℚ) =
      (3 * n)! / (3 * k)! * (n !) ^ 3 / (k !) ^ 3 * (640320 ^ 3) ^ (n - k) := by
  obtain ⟨c, rfl⟩ := exists_add_of_le h
  induction c with
  | zero =>
    field_simp
  | succ c ih =>
    simp [← Nat.add_assoc]
    rw [Finset.prod_Ico_succ_top (by grind), ih (by grind), q]
    have : k + c + 1 - k = c + 1 := by grind
    simp only [pow_succ, pow_zero, one_mul, add_tsub_cancel_left, cast_mul, cast_add,
      cast_ofNat, cast_one, this]
    simp [Nat.mul_add, factorial_succ]
    field_simp
    grind

theorem binarySplitSum_eq_partialSum (n : ℕ) :
    binarySplitSum n = partialSum 0 n := by
  rw [binarySplitSum]
  dsimp only
  rw [binarySplit_snd_snd]
  rw [binarySplit_snd_fst]
  push_cast
  rw [div_eq_mul_inv, Finset.sum_mul]
  rw [partialSum]
  apply Finset.sum_congr rfl
  intro k hk
  simp at hk
  simp only [chudnovskyTerm, chudnovskyNum, chudnovskyDenom, A, prod_p]
  rw [prod_q (by grind), prod_q (by grind)]
  -- Now really tedious...
  simp only [← Rat.zpow_natCast]
  have : ((n - k : ℕ) : ℤ) = (n : ℤ) - (k : ℤ) := by grind
  simp only [this]
  simp only [cast_add, cast_ofNat, cast_mul, zpow_natCast, Int.sub_eq_add_neg, mul_zero,
    factorial_zero, cast_one, div_one, one_zpow, tsub_zero, mul_inv_rev, Int.reduceNeg,
    Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, Int.cast_add,
    Int.cast_ofNat, cast_pow]
  rw [Rat.zpow_add (by decide)]
  rw [← zpow_mul, ← zpow_mul]
  simp only [← Rat.zpow_natCast]
  rw [← zpow_mul]
  field_simp
  grind

theorem binarySplit_helper_1 (n m : ℕ) (h : n + 1 = m) (p0 : ℤ) (q0 : ℕ) (t0 : ℤ)
    (hp : p0 = p n) (hq : q0 = q n) (ht : t0 = A n * q n) :
    binarySplit n m = (p0, q0, t0) := by
  rw [binarySplit, if_pos (by omega), if_pos h, hp, hq, ht]

theorem binarySplit_helper_2 (n m : ℕ) (h : Nat.blt (n + 1) m = true)
    {p0 t0 p1 t1 p2 t2 : ℤ} {q0 q1 q2 : ℕ} {r : ℕ} (hr : r = n + (m - n) / 2)
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

def binarySplit_helper_2_expr
    (n m : ℕ) (p0 t0 p1 t1 p2 t2 : ℤ) (q0 q1 q2 : ℕ) (r : ℕ) (w1 w2 : Expr) :
    MetaM Expr := do
  pure <|
    mkApp3 (mkApp4 (mkApp9
      (mkApp3 (mkConst ``binarySplit_helper_2 []) (toExpr n) (toExpr m)
        (← mkEqRefl q(Nat.blt ($n + 1) $m)))
      (toExpr p0) (toExpr t0) (toExpr p1) (toExpr t1) (toExpr p2) (toExpr t2)
      (toExpr q0) (toExpr q1) (toExpr q2)) (toExpr r) (← mkEqRefl q($r)) w1 w2)
        (← mkEqRefl q($p0)) (← mkEqRefl q($q0)) (← mkEqRefl q($t0))

def binarySplit_proof (n m : ℕ) : MetaM ((ℤ × ℕ × ℤ) × Expr) := do
  let mut memo : Std.HashMap (ℕ × ℕ) ((ℤ × ℕ × ℤ) × Expr) := Std.HashMap.emptyWithCapacity (m - n)

  let mut workList : Array (ℕ × ℕ) := Array.empty
  let mut toVisit : List (ℕ × ℕ × Bool) := [(n, m, false)]

  while !toVisit.isEmpty do
    match toVisit with
    | [] => break
    | (n', m', visited) :: rest =>
      if visited then
        workList := workList.push (n', m')
        toVisit := rest
      else if n' + 1 = m' || ¬(n' < m') then
        toVisit := rest
        workList := workList.push (n', m')
      else
        let r := n' + (m' - n') / 2
        toVisit := (n', r, false) :: (r, m', false) :: (n', m', true) :: rest

  memo ← workList.foldlM (init := memo) fun memo (n', m') => do
    if ¬(n' < m') then
      let (p0, q0, t0) := (1, 1, 0)
      let e := mkApp3 (mkConst ``binarySplit_helper_3 [])
        (toExpr n') (toExpr m') (← mkEqRefl q(Nat.ble $m' $n'))
      return memo.insert (n', m') ((p0, q0, t0), e)
    else if n' + 1 = m' then
      let (p0, q0, t0) := (p n', q n', (A n' * q n' : Int))
      let e := mkApp9 (mkConst ``binarySplit_helper_1 [])
        (toExpr n') (toExpr m') (← mkEqRefl q($n' + 1))
        (toExpr p0) (toExpr q0) (toExpr t0)
        (← mkEqRefl q($p0)) (← mkEqRefl q($q0)) (← mkEqRefl q($t0))
      return memo.insert (n', m') ((p0, q0, t0), e)
    else
      let r := n' + (m' - n') / 2

      let some ((p1, q1, t1), e1) := memo.get? (n', r) |
        panic! s!"Missing left child for range [{n'}, {r}) when processing [{n'}, {m'})"
      let some ((p2, q2, t2), e2) := memo.get? (r, m') |
        panic! s!"Missing right child for range [{r}, {m'}) when processing [{n'}, {m'})"

      let p0 := p1 * p2
      let q0 := q1 * q2
      let t0 := t1 * q2 + p1 * t2
      let e1 ← abstractProof e1
      let e2 ← abstractProof e2
      let e ← binarySplit_helper_2_expr n' m' p0 t0 p1 t1 p2 t2 q0 q1 q2 r e1 e2
      return memo.insert (n', m') ((p0, q0, t0), e)

  match memo.get? (n, m) with
  | some result => return result
  | none => panic! s!"Failed to compute result for range [{n}, {m})"

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

example : binarySplit 0 2 = eval% binarySplit 0 2 := by binary_split_tac
example : binarySplit 0 4 = eval% binarySplit 0 4 := by binary_split_tac
example : binarySplit 0 100 = eval% binarySplit 0 100 := by binary_split_tac

-- set_option profiler true in  -- about 1s
-- theorem f1000 : binarySplit 0 1000 = eval% binarySplit 0 1000 := by binary_split_tac

-- set_option profiler true in  -- about 2s
-- theorem f_1000_2000 : binarySplit 1000 2000 = eval% binarySplit 1000 2000 := by binary_split_tac

-- set_option profiler true in  -- about 2s
-- theorem f2000 : binarySplit 0 2000 = eval% binarySplit 0 2000 := by binary_split_tac

-- set_option profiler true in  -- about 6s
-- theorem f5000 : binarySplit 0 5000 = eval% binarySplit 0 5000 := by binary_split_tac

-- set_option profiler true in  -- about 11s
-- theorem f10000 : binarySplit 0 10000 = eval% binarySplit 0 10000 := by binary_split_tac

-- set_option profiler true in
-- theorem f20000 : binarySplit 0 20000 = eval% binarySplit 0 20000 := by binary_split_tac

-- set_option profiler true in
-- theorem f30000 : binarySplit 0 30000 = eval% binarySplit 0 30000 := by binary_split_tac

-- set_option profiler true in
-- theorem f40000 : binarySplit 0 40000 = eval% binarySplit 0 40000 := by binary_split_tac

-- set_option profiler true in
-- theorem f50000 : binarySplit 0 50000 = eval% binarySplit 0 50000 := by binary_split_tac

-- set_option profiler true in
-- theorem f60000 : binarySplit 0 60000 = eval% binarySplit 0 60000 := by binary_split_tac


-- set_option profiler true in
-- `chudnovskyTerm 71000 < 10^(-1,001,000)`,
-- so this suffices to get `π` to over a million decimal places
-- theorem f71000 : binarySplit 0 71000 = eval% binarySplit 0 71000 := by binary_split_tac

set_option Elab.async false

-- #time
-- example : binarySplit 0 100000 = eval% binarySplit 0 100000 := by binary_split_tac
-- #time
-- example : binarySplit 0 200000 = eval% binarySplit 0 200000 := by binary_split_tac
-- #time
-- example : binarySplit 0 500000 = eval% binarySplit 0 500000 := by binary_split_tac
-- #time
-- example : binarySplit 0 1000000 = eval% binarySplit 0 1000000 := by binary_split_tac
-- #time
-- example : binarySplit 0 2000000 = eval% binarySplit 0 2000000 := by binary_split_tac
-- #time
-- example : binarySplit 0 5000000 = eval% binarySplit 0 5000000 := by binary_split_tac


def sqrt_640320 : ℚ := Nat.sqrt (640320 * 4 * 10^(10^6))


#eval sqrt (10^(10^7)) |>.log2
-- #eval Nat.log 10 (Nat.sqrt (10^(10^5)))
-- #eval sqrt_640320 |>.floor.natAbs.log2

end Chudnovsky
