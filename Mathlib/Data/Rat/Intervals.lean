import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib

class LERat (α : Type) where
  leRat : α → Rat → Bool
  ratLE : Rat → α → Bool

namespace LERat

scoped infix:50 " ≤ℚ " => LERat.leRat
scoped infix:50 " ℚ≤ " => LERat.ratLE

class RatCompare (α : Type) [LE α] extends LERat α where
  leRat_le : ∀ {a : α} {b c : Rat}, a ≤ℚ b → b ≤ c → a ≤ℚ c
  le_leRat : ∀ {a b : α} {c : Rat}, a ≤ b → b ≤ℚ c → a ≤ℚ c
  le_ratLE : ∀ {a b : Rat} {c : α}, a ≤ b → b ℚ≤ c → a ℚ≤ c
  ratLE_le : ∀ {a : Rat} {b c : α}, a ℚ≤ b → b ≤ c → a ℚ≤ c

instance : LERat Nat where
  leRat a b := a ≤ b
  ratLE a b := a ≤ b

theorem _root_.Rat.natCast_le_natCast {a b : Nat} : (a : Rat) ≤ (b : Rat) ↔ a ≤ b := Nat.cast_le

instance : RatCompare Nat where
  leRat_le {a b c} hab hbc :=
    decide_eq_true (Rat.le_trans (of_decide_eq_true hab) hbc)
  le_leRat {a b c} hab hbc :=
    decide_eq_true (Rat.le_trans (Rat.natCast_le_natCast.mpr hab) (of_decide_eq_true hbc))
  le_ratLE {a b c} hab hbc :=
    decide_eq_true (Rat.le_trans hab (of_decide_eq_true hbc))
  ratLE_le {a b c} hab hbc :=
    decide_eq_true (Rat.le_trans (of_decide_eq_true hab) (Rat.natCast_le_natCast.mpr hbc))

end LERat
