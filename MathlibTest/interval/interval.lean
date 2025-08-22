import Mathlib

universe u

/--
A type equipped with order comparisons with `Rat`.

This includes both subsets (e.g. `Nat`) and supersets (e.g. `ℝ`).
-/
class LERat (α : Type u) where
  leRat : α → Rat → Bool
  ratLE : Rat → α → Bool

namespace LERat

variable {α : Type u} [LERat α]

scoped infix:50 " ≤ℚ " => leRat
scoped infix:50 " ℚ≤ " => ratLE

def leRat? (a : α) (u : WithTop Rat) : Bool :=
  match u with
  | .some u => leRat a u
  | ⊤ => true

def ratLE? (l : WithBot Rat) (b : α) : Bool :=
  match l with
  | .some l => ratLE l b
  | ⊥ => true

scoped infix:50 " ≤ℚ? " => leRat?
scoped infix:50 " ℚ?≤ " => ratLE?

@[simp] theorem leRat?_top {a : α} : a ≤ℚ? ⊤ ↔ True := by
  simp [leRat?]
@[simp] theorem bot_ratLE? {a : α} : ⊥ ℚ?≤ a ↔ True := by
  simp [ratLE?]
@[simp] theorem leRat?_some {a : α} {u : Rat} : a ≤ℚ? .some u ↔ a ≤ℚ u := by
  simp [leRat?]
@[simp] theorem some_ratLE? {l : Rat} {b : α} : .some l ℚ?≤ b ↔ l ℚ≤ b := by
  simp [ratLE?]

end LERat

open LERat

structure RatInterval where
  lower : WithBot Rat
  upper : WithTop Rat

namespace RatInterval

variable {α : Type u} [LERat α]

@[simp]
def mem (i : RatInterval) (a : α) : Bool :=
  i.lower ℚ?≤ a && a ≤ℚ? i.upper

def isEmpty (i : RatInterval) : Bool :=
  match i with
  | ⟨.some l, .some u⟩ => l > u
  | ⟨_, _⟩ => false

def toString (i : RatInterval) : String :=
  match i with
  | ⟨.some l, .some u⟩ => s!"[{l}, {u}]"
  | ⟨.some l, ⊤⟩ => s!"[{l}, ∞)"
  | ⟨⊥, .some u⟩ => s!"(-∞, {u}]"
  | ⟨⊥, ⊤⟩ => s!"(-∞, ∞)"

instance : ToString RatInterval where
  toString i := toString i

/--
Map an interval by applying independent functions to the lower and upper bounds.
-/
@[simp]
def map₂ (g : WithBot Rat → WithBot Rat) (h : WithTop Rat → WithTop Rat)
    (i : RatInterval) : RatInterval where
  lower := g i.lower
  upper := h i.upper

theorem mem_map₂ {f : α → α} {g : WithBot Rat → WithBot Rat} {h : WithTop Rat → WithTop Rat}
    (wl : ∀ {l} {a}, l ℚ?≤ a → g l ℚ?≤ f a) (wu : ∀ {a} {u}, a ≤ℚ? u → f a ≤ℚ? h u)
    {i : RatInterval} {a : α} (m : i.mem a) : i.map₂ g h |>.mem (f a) := by
  simp at m ⊢
  exact ⟨wl m.1, wu m.2⟩

end RatInterval

structure IntervalPropagator {α : Type u} [LERat α] (f : α → α) where
  apply : RatInterval → RatInterval
  mem_apply : ∀ {i : RatInterval} {a : α}, i.mem a → (apply i).mem (f a)

namespace IntervalPropagator

variable {α : Type u} [LERat α] {f : α → α}

def of₂ (g : WithBot Rat → WithBot Rat) (h : WithTop Rat → WithTop Rat)
    (wl : ∀ {l} {a}, l ℚ?≤ a → g l ℚ?≤ f a) (wu : ∀ {a} {u}, a ≤ℚ? u → f a ≤ℚ? h u) :
    IntervalPropagator f where
  apply := fun i => i.map₂ g h
  mem_apply := RatInterval.mem_map₂ wl wu

end IntervalPropagator

/-! ### Instances for `Nat` -/

instance : LERat Nat where
  leRat (a : Nat) (b : Rat) := (a : Rat) ≤ b
  ratLE (a : Rat) (b : Nat) := a ≤ (b : Rat)

@[simp] theorem Nat.leRat_iff {a : Nat} {b : Rat} : a ≤ℚ b ↔ (a : Rat) ≤ b := decide_eq_true_iff
@[simp] theorem Nat.ratLE_iff {a : Rat} {b : Nat} : a ℚ≤ b ↔ a ≤ (b : Rat) := decide_eq_true_iff

theorem WithBot.ofNat_zero_eq_some :
    (OfNat.ofNat 0 : WithBot Rat) = .some 0 := rfl
theorem WithBot.ofNat_one_eq_some :
    (OfNat.ofNat 1 : WithBot Rat) = .some 1 := rfl
theorem WithBot.ofNat_eq_some {n : Nat} [n.AtLeastTwo] :
    (OfNat.ofNat n : WithBot Rat) = .some n := rfl

theorem WithTop.ofNat_zero_eq_some :
    (OfNat.ofNat 0 : WithTop Rat) = .some 0 := rfl
theorem WithTop.ofNat_one_eq_some :
    (OfNat.ofNat 1 : WithTop Rat) = .some 1 := rfl
theorem WithTop.ofNat_eq_some {n : Nat} [n.AtLeastTwo] :
    (OfNat.ofNat n : WithTop Rat) = .some n := rfl

@[simp] theorem Nat.ofNat_zero_ratLE? {b : Nat} : OfNat.ofNat 0 ℚ?≤ b ↔ 0 ≤ b := by
  have : (OfNat.ofNat 0 : WithBot Rat) = .some 0 := rfl
  rw [this, some_ratLE?]
  simp

theorem squareLowerBound {l : Rat} {a : Nat} (h : l ℚ≤ a) : (max l 0)^2 ℚ≤ a^2 := by
  rw [Nat.ratLE_iff] at h ⊢
  by_cases w : 0 ≤ l
  · simp only [max_eq_left w]
    rw [sq, sq, Nat.cast_mul]
    apply mul_le_mul h h <;> linarith
  · rw [max_eq_right]
    · simp
    · linarith

theorem squareLowerBound' {l : WithBot Rat} {a : Nat} (h : l ℚ?≤ a) : (max l 0)^2 ℚ?≤ a^2 :=
  match l, h with
  | .some l, h => squareLowerBound h
  | ⊥, h => by simp

theorem squareUpperBound {a : Nat} {u : Rat} (h : a ≤ℚ u) : a^2 ≤ℚ (u^2 : Rat) := by
  rw [Nat.leRat_iff] at h ⊢
  rw [sq, sq, Nat.cast_mul]
  apply mul_le_mul h h <;> linarith

theorem squareUpperBound' {a : Nat} {u : WithTop Rat} (h : a ≤ℚ? u) : a^2 ≤ℚ? u^2 :=
  -- I wish this worked by `grind [cases WithTop, squareUpperBound]`,
  -- but we probably need to make `WithTop` a structure first.
  match u, h with
  | .some u, h => squareUpperBound h
  | ⊤, h => by simp

def squarePropagator : IntervalPropagator (fun n : Nat => n^2) :=
  .of₂ ((max · 0)^2) (·^2) squareLowerBound' squareUpperBound'

/-- info: [-1, 1] -/
#guard_msgs in
#eval (RatInterval.mk (-1 : Rat) (1 : Rat))
/-- info: [0, 1] -/
#guard_msgs in
#eval squarePropagator.apply (.mk (-1 : Rat) (1 : Rat))
/-- info: [0, 9] -/
#guard_msgs in
#eval squarePropagator.apply (.mk (-2 : Rat) (3 : Rat))
/-- info: [4, 9] -/
#guard_msgs in
#eval squarePropagator.apply (.mk (2 : Rat) (3 : Rat))

structure Approximator {α : Type u} [LERat α] (a : α) (β : Type u) where
  interval : β → RatInterval
  initial : β
  improve : β → β
  valid : ∀ (b : β), (interval b).mem a
  -- TODO: a proof that the intervals get arbitrarily tight?

def seven : Nat := 7

def sevenApproximator : Approximator seven Nat where
  interval n := { lower := .some (7 - 2^(-n : Int)), upper := .some (7 + 2^(-n : Int)) }
  initial := 0
  improve n := n + 1
  valid n := by simp [seven, -WithTop.coe_add]

set_option linter.style.nativeDecide false in
example : seven^2 ≠ 50 := by
  -- We need to take the 4th approximation to get a sufficiently tight interval.
  let b := sevenApproximator.improve^[4] sevenApproximator.initial
  let I := sevenApproximator.interval b
  have p : I.mem seven := sevenApproximator.valid b
  let I' := squarePropagator.apply I
  have p' : I'.mem (seven ^ 2) := squarePropagator.mem_apply p
  have q : I'.mem 50 = false := by native_decide
  intro w
  simp_all

-- This describes some basic axioms for the `LERat` class,
-- giving transitivity with the order relations in `Rat` and `α`.
class RatCompare (α : Type u) [LE α] extends LERat α where
  leRat_le : ∀ {a : α} {b c : Rat}, a ≤ℚ b → b ≤ c → a ≤ℚ c
  le_leRat : ∀ {a b : α} {c : Rat}, a ≤ b → b ≤ℚ c → a ≤ℚ c
  le_ratLE : ∀ {a b : Rat} {c : α}, a ≤ b → b ℚ≤ c → a ℚ≤ c
  ratLE_le : ∀ {a : Rat} {b c : α}, a ℚ≤ b → b ≤ c → a ℚ≤ c

theorem _root_.Rat.natCast_le_natCast {a b : Nat} : (a : Rat) ≤ (b : Rat) ↔ a ≤ b := Nat.cast_le

instance : RatCompare Nat where
  leRat_le hab hbc :=
    decide_eq_true (Rat.le_trans (of_decide_eq_true hab) hbc)
  le_leRat hab hbc :=
    decide_eq_true (Rat.le_trans (Rat.natCast_le_natCast.mpr hab) (of_decide_eq_true hbc))
  le_ratLE hab hbc :=
    decide_eq_true (Rat.le_trans hab (of_decide_eq_true hbc))
  ratLE_le hab hbc :=
    decide_eq_true (Rat.le_trans (of_decide_eq_true hab) (Rat.natCast_le_natCast.mpr hbc))
