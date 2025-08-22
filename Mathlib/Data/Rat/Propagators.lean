import Mathlib

namespace IntervalTactic

abbrev Interval := WithBot ℚ × WithTop ℚ

instance : Membership ℝ Interval where
  mem i x := (i.1.map ((↑) : ℚ → ℝ)) ≤ x ∧ x ≤ (i.2.map ((↑) : ℚ → ℝ))

theorem mem_def (i : Interval) (x : ℝ) :
  x ∈ i ↔ match i with
  | ⟨⊥, ⊤⟩ => True
  | ⟨⊥, (b : ℚ)⟩ => x ≤ b
  | ⟨(a : ℚ), ⊤⟩ => a ≤ x
  | ⟨(a : ℚ), (b : ℚ)⟩ => a ≤ x ∧ x ≤ b := sorry

notation "ℚ>0" => { x : ℚ // 0 < x }

structure Propagator (f : ℝ → ℝ) where
  state : Type := Unit
  initial : state := by exact ()
  interval : (quality : ℚ>0) → state → Interval → Interval
  mem : ∀ q s i x, x ∈ i → f x ∈ interval q s i

def neg_propagator : Propagator (fun x => -x) where
  interval q s i :=
    match i with
    | ⟨⊥, ⊤⟩ => ⟨⊥, ⊤⟩
    | ⟨⊥, (y : ℚ)⟩ => ⟨(-y : ℚ), ⊤⟩
    | ⟨(x : ℚ), ⊤⟩ => ⟨⊥, -x⟩
    | ⟨(x : ℚ), (y : ℚ)⟩ => ⟨(-y : ℚ), -x⟩
  mem q s i x hx := by
    simp only [mem_def] at hx ⊢
    match i with
    | ⟨⊥, ⊤⟩ => simp
    | ⟨⊥, (b : ℚ)⟩ => simp_all
    | ⟨(a : ℚ), ⊤⟩ => simp_all
    | ⟨(a : ℚ), (b : ℚ)⟩ => simp_all

end IntervalTactic
