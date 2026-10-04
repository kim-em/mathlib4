module
import Mathlib.Tactic.NoncommRing
public meta import Lean.Meta.Sym.Arith.Module
public meta import Lean.Elab.Tactic

/-! Check shared additive certificates after `noncomm_ring`'s existing distributivity step. -/

open Lean Meta Elab Tactic Sym

elab "shared_add_eq" : tactic => withMainContext do
  let g ← getMainGoal
  let some proof ← SymM.run (Arith.proveAddEq? (← instantiateMVars (← g.getType)))
    | throwError "additive normal forms differ"
  g.assign proof
  replaceMainGoal []

example {R : Type*} [NonAssocSemiring R] (a b c : R) :
    (a + b) * c = b * c + a * c := by noncomm_ring

example {R : Type*} [NonUnitalNonAssocRing R] (a b c : R) :
    a * (b - c) + a * c = a * b := by noncomm_ring

example {R : Type*} [NonUnitalSemiring R] (a b c : R) :
    (a + b) * c + (2 : Nat) • (b * c) = a * c + (3 : Nat) • (b * c) := by
  noncomm_ring

example {R : Type*} [Ring R] (a b : R) :
    (a - b)^2 = a^2 - a * b - b * a + b^2 := by noncomm_ring

example {R : Type*} [AddCommMonoid R] (a b : R) :
    (2 : Nat) • (a + b) + a = (3 : Nat) • a + (2 : Nat) • b := by shared_add_eq

example {R : Type*} [AddCommGroup R] (a b : R) :
    a + b + b - a = (2 : Int) • b := by shared_add_eq
