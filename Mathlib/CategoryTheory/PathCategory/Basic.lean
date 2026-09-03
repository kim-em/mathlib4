/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Quotient

/-!
# The category paths on a quiver.

When `C` is a quiver, `paths C` is the category of paths.

## When the quiver is itself a category
We provide `path_composition : paths C ⥤ C`.

We check that the quotient of the path category of a category by the canonical relation
(paths are related if they compose to the same path) is equivalent to the original category.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

/-- A wrapper for the vertices of a quiver, used as the objects of the category of paths.
-/
@[ext]
structure Paths (V : Type u₁) : Type u₁ where
  /-- The underlying vertex of the quiver. -/
  as : V

instance (V : Type u₁) [Inhabited V] : Inhabited (Paths V) := ⟨⟨default⟩⟩
instance (V : Type u₁) [Unique V] : Unique (Paths V) where
  uniq _ := Paths.ext (Subsingleton.elim _ _)

variable (V : Type u₁) [Quiver.{v₁} V]

namespace Paths

instance categoryPaths : Category.{max u₁ v₁} (Paths V) where
  Hom X Y := Quiver.Path X.as Y.as
  id _ := Quiver.Path.nil
  comp f g := Quiver.Path.comp f g

/-- The inclusion of a quiver `V` into its path category, as a prefunctor.
-/
@[simps, implicit_reducible]
def of : V ⥤q Paths V where
  obj X := ⟨X⟩
  map f := f.toPath

variable {V}

/-- To prove a property on morphisms of a path category with given source `a`, it suffices to
prove it for the identity and prove that the property is preserved under composition on the right
with length 1 paths. -/
lemma induction_fixed_source {a : Paths V} (P : ∀ {b : Paths V}, (a ⟶ b) → Prop)
    (id : P (𝟙 a))
    (comp : ∀ {u v : V} (p : a ⟶ (of V).obj u) (q : u ⟶ v), P p → P (p ≫ (of V).map q)) :
    ∀ {b : Paths V} (f : a ⟶ b), P f := by
  rintro ⟨b⟩ (f : Quiver.Path a.as b)
  induction f with
  | nil => exact id
  | cons _ w h => exact comp _ w h

/-- To prove a property on morphisms of a path category with given target `b`, it suffices to prove
it for the identity and prove that the property is preserved under composition on the left
with length 1 paths. -/
lemma induction_fixed_target {b : Paths V} (P : ∀ {a : Paths V}, (a ⟶ b) → Prop)
    (id : P (𝟙 b))
    (comp : ∀ {u v : V} (p : (of V).obj v ⟶ b) (q : u ⟶ v), P p → P ((of V).map q ≫ p)) :
    ∀ {a : Paths V} (f : a ⟶ b), P f := by
  obtain ⟨b⟩ := b
  rintro ⟨a⟩ (f : Quiver.Path a b)
  generalize h : f.length = k
  induction k generalizing f a with
  | zero => cases f with
    | nil => exact id
    | cons _ _ => simp at h
  | succ k h' =>
    obtain ⟨c, f, q, hq, rfl⟩ := f.eq_toPath_comp_of_length_eq_succ h
    exact comp _ _ (h' _ _ hq)

/-- To prove a property on morphisms of a path category, it suffices to prove it for the identity
and prove that the property is preserved under composition on the right with length 1 paths. -/
lemma induction (P : ∀ {a b : Paths V}, (a ⟶ b) → Prop)
    (id : ∀ {v : V}, P (𝟙 ((of V).obj v)))
    (comp : ∀ {u v w : V}
      (p : (of V).obj u ⟶ (of V).obj v) (q : v ⟶ w), P p → P (p ≫ (of V).map q)) :
    ∀ {a b : Paths V} (f : a ⟶ b), P f :=
  fun {_} ↦ induction_fixed_source _ id comp

/-- To prove a property on morphisms of a path category, it suffices to prove it for the identity
and prove that the property is preserved under composition on the left with length 1 paths. -/
lemma induction' (P : ∀ {a b : Paths V}, (a ⟶ b) → Prop)
    (id : ∀ {v : V}, P (𝟙 ((of V).obj v)))
    (comp : ∀ {u v w : V} (p : u ⟶ v)
      (q : (of V).obj v ⟶ (of V).obj w), P q → P ((of V).map p ≫ q)) :
    ∀ {a b : Paths V} (f : a ⟶ b), P f := by
  intro a b
  revert a
  exact induction_fixed_target (P := fun f ↦ P f) id (fun _ _ ↦ comp _ _)

attribute [local ext (iff := false)] Functor.ext

/-- Any prefunctor from `V` lifts to a functor from `paths V` -/
@[implicit_reducible]
def lift {C} [Category* C] (φ : V ⥤q C) : Paths V ⥤ C where
  obj X := φ.obj X.as
  map {X} {Y} f :=
    @Quiver.Path.rec V _ X.as (fun Y _ => φ.obj X.as ⟶ φ.obj Y) (𝟙 <| φ.obj X.as)
      (fun _ f ihp => ihp ≫ φ.map f) Y.as f
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    obtain ⟨Z⟩ := Z
    change Quiver.Path Y.as Z at g
    induction g with
    | nil =>
      rw [Category.comp_id]
      rfl
    | cons g' p ih =>
      have : f ≫ Quiver.Path.cons g' p = (f ≫ g').cons p := by apply Quiver.Path.comp_cons
      rw [this]
      simp only at ih ⊢
      rw [ih, Category.assoc]

@[simp]
theorem lift_nil {C} [Category* C] (φ : V ⥤q C) (X : V) :
    (lift φ).map Quiver.Path.nil = 𝟙 (φ.obj X) := rfl

@[simp]
theorem lift_cons {C} [Category* C] (φ : V ⥤q C) {X Y Z : V} (p : Quiver.Path X Y) (f : Y ⟶ Z) :
    (lift φ).map (p.cons f) = (lift φ).map p ≫ φ.map f := rfl

@[simp]
theorem lift_toPath {C} [Category* C] (φ : V ⥤q C) {X Y : V} (f : X ⟶ Y) :
    (lift φ).map f.toPath = φ.map f := by
  dsimp [Quiver.Hom.toPath, lift]
  simp

theorem lift_spec {C} [Category* C] (φ : V ⥤q C) : of V ⋙q (lift φ).toPrefunctor = φ :=
  Prefunctor.ext (fun _ ↦ rfl) (fun _ _ f ↦ lift_toPath φ f)

/-- Two functors out of a path category are equal when they agree on singleton paths. -/
@[ext (iff := false)]
theorem ext_functor {C} [Category* C] {F G : Paths V ⥤ C} (h_obj : F.obj = G.obj)
    (h : ∀ (a b : V) (e : a ⟶ b), F.map e.toPath =
        eqToHom (congr_fun h_obj ⟨a⟩) ≫ G.map e.toPath ≫ eqToHom (congr_fun h_obj.symm ⟨b⟩)) :
    F = G := by
  fapply Functor.ext
  · intro X
    rw [h_obj]
  · rintro ⟨X⟩ ⟨Y⟩ (f : Quiver.Path X Y)
    induction f with
    | nil => erw [F.map_id, G.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
    | cons g e ih =>
      erw [F.map_comp g (Quiver.Hom.toPath e), G.map_comp g (Quiver.Hom.toPath e), ih, h]
      simp only [Category.id_comp, eqToHom_refl, eqToHom_trans_assoc, Category.assoc]

theorem lift_unique {C} [Category* C] (φ : V ⥤q C) (Φ : Paths V ⥤ C)
    (hΦ : of V ⋙q Φ.toPrefunctor = φ) : Φ = lift φ := by
  subst hΦ
  refine ext_functor rfl (fun _ _ e ↦ ?_)
  simp only [lift_toPath, Prefunctor.comp_map, of_map]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

end Paths

variable (W : Type u₂) [Quiver.{v₂} W]

-- A restatement of `Prefunctor.mapPath_comp` using `f ≫ g` instead of `f.comp g`.
@[simp]
theorem Prefunctor.mapPath_comp' (F : V ⥤q W) {X Y Z : Paths V} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.mapPath (f ≫ g) = (F.mapPath f).comp (F.mapPath g) :=
  Prefunctor.mapPath_comp _ _ _

end

section

variable {C : Type u₁} [Category.{v₁} C]

open Quiver

/-- A path in a category can be composed to a single morphism. -/
@[simp]
def composePath {X : C} : ∀ {Y : C} (_ : Path X Y), X ⟶ Y
  | _, .nil => 𝟙 X
  | _, .cons p e => composePath p ≫ e

-- This lemma was marked as `@[simp]` but it is generated by `@[simp]` on `composePath`.
lemma composePath_nil {X : C} : composePath (Path.nil : Path X X) = 𝟙 X := rfl

-- This lemma was marked as `@[simp]` but it is generated by `@[simp]` on `composePath`.
lemma composePath_cons {X Y Z : C} (p : Path X Y) (e : Y ⟶ Z) :
    composePath (p.cons e) = composePath p ≫ e := rfl

@[simp]
theorem composePath_toPath {X Y : C} (f : X ⟶ Y) : composePath f.toPath = f := Category.id_comp _

@[simp]
theorem composePath_comp {X Y Z : C} (f : Path X Y) (g : Path Y Z) :
    composePath (f.comp g) = composePath f ≫ composePath g := by
  induction g with
  | nil => simp
  | cons g e ih => simp [ih]

@[simp]
theorem composePath_id {X : Paths C} : composePath (𝟙 X) = 𝟙 X.as := rfl

@[simp]
theorem composePath_comp' {X Y Z : Paths C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    composePath (f ≫ g) = composePath f ≫ composePath g :=
  composePath_comp f g

variable (C)

/-- Composition of paths as functor from the path category of a category to the category. -/
@[simps, implicit_reducible]
def pathComposition : Paths C ⥤ C where
  obj X := X.as
  map f := composePath f

-- TODO: This, and what follows, should be generalized to
-- the `HomRel` for the kernel of any functor.
-- Indeed, this should be part of an equivalence between congruence relations on a category `C`
-- and full, essentially surjective functors out of `C`.
/-- The canonical relation on the path category of a category:
two paths are related if they compose to the same morphism. -/
@[simp]
def pathsHomRel : HomRel (Paths C) := fun _ _ p q =>
  (pathComposition C).map p = (pathComposition C).map q

#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/
attribute [nolint simpNF] pathsHomRel.eq_1

/-- The functor from a category to the canonical quotient of its path category. -/
@[simps, implicit_reducible]
def toQuotientPaths : C ⥤ Quotient (pathsHomRel C) where
  obj X := (Quotient.functor _).obj ((Paths.of C).obj X)
  map f := (Quotient.functor _).map ((Paths.of C).map f)
  map_id X := by
    rw [← (Quotient.functor _).map_id]
    exact Quotient.sound _ (by simp)
  map_comp f g := by
    rw [← (Quotient.functor _).map_comp]
    exact Quotient.sound _ (by simp)

/-- The functor from the canonical quotient of a path category of a category
to the original category. -/
@[implicit_reducible]
def quotientPathsTo : Quotient (pathsHomRel C) ⥤ C :=
  Quotient.lift _ (pathComposition C) fun _ _ _ _ w => w

@[simp]
lemma quotientPathsTo_obj_functor_obj (X : Paths C) :
    (quotientPathsTo C).obj ((Quotient.functor _).obj X) = X.as := rfl

@[simp]
lemma quotientPathsTo_map_functor_map {X Y : Paths C} (f : X ⟶ Y) :
    (quotientPathsTo C).map ((Quotient.functor _).map f) = composePath f := rfl

/-- The canonical quotient of the path category of a category
is equivalent to the original category. -/
def quotientPathsEquiv : Quotient (pathsHomRel C) ≌ C where
  functor := quotientPathsTo C
  inverse := toQuotientPaths C
  unitIso := Quotient.natIsoLift _ (NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    dsimp
    simp only [Category.comp_id, Category.id_comp]
    exact Quotient.sound _ (by simp)))
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp)
  functor_unitIso_comp := fun ⟨_⟩ => Category.comp_id _

end

end CategoryTheory
