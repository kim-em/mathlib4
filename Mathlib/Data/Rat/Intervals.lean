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

instance : RatCompare Nat where
  leRat_le {a b c} hab hbc := @le_trans _ _ (a : Rat) b c hab hbc
  le_leRat := sorry
  le_ratLE := sorry
  ratLE_le := sorry

end LERat
