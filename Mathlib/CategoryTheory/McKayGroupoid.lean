import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.List.Defs

open CategoryTheory

class McKayGroupoidData (G : Type) [Groupoid G] where
  level : G ⥤ ℕ
  upper : G ⥤ Type
  upperResult : ∀ {x}, upper.obj x → G -- is this meant to be a functor??
  upperResult_level : ∀ {x}, ∀ u : upper.obj x, level.obj x < level.obj (upperResult u)
  lower : G ⥤ Type
  lowerResult : ∀ {x}, lower.obj x → G
  lowerResult_level : ∀ {x}, ∀ l : lower.obj x, level.obj (lowerResult l) < level.obj x
  inverse : ∀ {x}, ∀ u : upper.obj x, lower.obj (upperResult u)
  canonicalReduction : ∀ x, 0 < level.obj x → lower.obj x -- we only need to specify the orbit?
  candidateUppers : ∀ x, List (upper.obj x)
  lowerIsIso : ∀ {x}, lower.obj x → lower.obj x → Bool

section
variable {G : Type} [Groupoid G] [McKayGroupoidData G]

open McKayGroupoidData

def genuine {x : G} (u : upper.obj x) : Bool :=
  lowerIsIso (inverse u) (canonicalReduction (upperResult u)
    (Nat.lt_of_le_of_lt (Nat.zero_le _) (upperResult_level u)))

class McKayGroupoid (G : Type) [Groupoid G] extends McKayGroupoidData G where
  inverseResult : ∀ {x}, ∀ u : upper.obj x, lowerResult (inverse u) = x -- really on the nose?
  /-- `lowerIsIso u₁ u₂` reports `true` iff there is a morphism carrying `u₁` to `u₂`. -/
  lowerIsIso_spec : ∀ {x} (u₁ u₂ : lower.obj x),
    lowerIsIso u₁ u₂ ↔ ∃ f : x ⟶ x, lower.map f u₁ = u₂
  /-- Every genuine upper object is contained in the list of candidates. -/
  genuineCandidates : ∀ x, ∀ u : upper.obj x,
    genuine u → u ∈ candidateUppers x

end

class HasGenerators (H : Type) [Group H] where
  generators : List H
  -- non-constructive witness, not an algorithm:
  spec : ∀ h, ∃ l, l ⊆ generators ∧ l.prod = h

variable {G : Type} [Groupoid G] [McKayGroupoid G] [∀ x : G, HasGenerators (Aut x)]

open McKayGroupoidData

def children (x : G) : List G :=
  let candidates := candidateUppers x
  let representatives : List (upper.obj x) :=
    -- probably worth writing something generic about splitting a list of objects into orbits
    sorry
  let genuine := representatives.filter fun u => genuine u
  genuine.map upperResult
