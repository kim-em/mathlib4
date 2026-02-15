/-
Copyright (c) 2024 Weihong Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Amelia Livingston, Sophie Morel, Jujian Zhang, Weihong Xu,
  Andrew Yang
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures

/-!

# Construction of M^~

Given any commutative ring `R` and `R`-module `M`, we construct the sheaf `M^~` of `𝒪_SpecR`-modules
such that `M^~(U)` is the set of dependent functions that are locally fractions.

## Main definitions
* `AlgebraicGeometry.tilde` : `M^~` as a sheaf of `𝒪_{Spec R}`-modules.
* `AlgebraicGeometry.tilde.adjunction` : `~` is left adjoint to taking global sections.

-/

@[expose] public noncomputable section

universe u

open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

namespace AlgebraicGeometry

open _root_.PrimeSpectrum

/-- The forgetful functor from `𝒪_{Spec R}` modules to sheaves of `R`-modules. -/
def modulesSpecToSheaf :
    (Spec R).Modules ⥤ TopCat.Sheaf (ModuleCat R) (Spec R) :=
  SheafOfModules.forgetToSheafModuleCat (Spec R).ringCatSheaf (.op ⊤)
    (Limits.initialOpOfTerminal Limits.isTerminalTop) ⋙
  sheafCompose _ (ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso R).hom.hom)

/-- The global section functor for `𝒪_{Spec R}` modules -/
noncomputable
def moduleSpecΓFunctor : (Spec (.of R)).Modules ⥤ ModuleCat R :=
  modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op ⊤)

/--
The property of a function `f : ∏_{x ∈ U}, Mₓ` being a fraction is stable under restriction.
-/
def isFractionPrelocal : PrelocalPredicate (Localizations M) where
  pred {_} f := isFraction M f
  res := by rintro V U i f ⟨m, s, w⟩; exact ⟨m, s, fun x => w (i x)⟩

/--
For any open subset `U ⊆ Spec R`, `IsLocallyFraction` is the predicate expressing that a function
`f : ∏_{x ∈ U}, Mₓ` is such that for any `𝔭 ∈ U`, there exists an open neighbourhood `V ∋ 𝔭`, such
that for any `𝔮 ∈ V`, `f 𝔮 = m / s` for some `m : M` and `s ∉ 𝔮`.
In short `f` is locally a fraction on `U`.
-/
def isLocallyFraction : LocalPredicate (Localizations M) := (isFractionPrelocal M).sheafify

@[simp]
theorem isLocallyFraction_pred {U : Opens (PrimeSpectrum.Top R)}
    (f : ∀ x : U, Localizations M x) :
    (isLocallyFraction M).pred f =
      ∀ y : U,
        ∃ (V : _) (_ : y.1 ∈ V) (i : V ⟶ U),
          ∃ (m : M) (s : R), ∀ x : V, s ∉ x.1.asIdeal ∧ s • f (i x) =
            LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M m :=
  rfl

/- M_x is an O_SpecR(U)-module when x is in U -/
noncomputable instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) (x : U.unop) :
    Module ((Spec.structureSheaf R).val.obj U) (Localizations M x) :=
  Module.compHom (R := (Localization.AtPrime x.1.asIdeal)) _
    ((StructureSheaf.openToLocalization R U.unop x x.2).hom)

instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) (x : U.unop) :
    IsScalarTower R (Localization.AtPrime x.1.asIdeal) (Localizations M x) :=
  OreLocalization.instIsScalarTower_1 ..

instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) (x : U.unop) :
    IsScalarTower R ((Spec.structureSheaf R).val.obj U) (Localizations M x) :=
  .of_algebraMap_smul fun r m ↦
    IsScalarTower.algebraMap_smul (Localization.AtPrime x.1.asIdeal) r m

@[simp]
lemma sections_smul_localizations_def
    {U : (Opens (PrimeSpectrum.Top R))ᵒᵖ} (x : U.unop)
    (r : (Spec.structureSheaf R).val.obj U)
    (m : Localizations M ↑x) :
    r • m = (by exact r.1 x : Localization.AtPrime x.1.asIdeal) • m :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
For any `R`-module `M` and any open subset `U ⊆ Spec R`, `M^~(U)` is an `𝒪_{Spec R}(U)`-submodule
of `∏_{𝔭 ∈ U} M_𝔭`. -/
noncomputable def sectionsSubmodule (U : (Opens (PrimeSpectrum R))ᵒᵖ) :
    Submodule ((Spec.structureSheaf R).1.obj U) (∀ x : U.unop, Localizations M x.1) where
  carrier := { f | (isLocallyFraction M).pred f }
  zero_mem' x := ⟨unop U, x.2, 𝟙 _, 0, 1, fun y =>
    ⟨Ideal.ne_top_iff_one _ |>.1 y.1.isPrime.1, by simp⟩⟩
  add_mem' := by
    intro a b ha hb x
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩
    rcases hb x with ⟨Vb, mb, ib, rb, sb, wb⟩
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, sb • ra + sa • rb, sa * sb, ?_⟩
    intro y
    rcases wa (Opens.infLELeft _ _ y : Va) with ⟨nma, wa⟩
    rcases wb (Opens.infLERight _ _ y : Vb) with ⟨nmb, wb⟩
    fconstructor
    · intro H; cases y.1.isPrime.mem_or_mem H <;> contradiction
    · simp only [LocalizedModule.mkLinearMap_apply, Opens.comp_apply, Pi.add_apply, smul_add,
        map_add, map_smul] at wa wb ⊢
      rw [← wa, ← wb, ← mul_smul, ← mul_smul]
      congr 2
      simp [mul_comm]
  smul_mem' := by
    intro r a ha x
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩
    rcases r.2 x with ⟨Vr, mr, ir, rr, sr, wr⟩
    refine ⟨Va ⊓ Vr, ⟨ma, mr⟩, Opens.infLELeft _ _ ≫ ia, rr • ra, sr * sa, ?_⟩
    intro y
    rcases wa (Opens.infLELeft _ _ y : Va) with ⟨nma, wa⟩
    rcases wr (Opens.infLERight _ _ y) with ⟨nmr, wr⟩
    fconstructor
    · intro H; cases y.1.isPrime.mem_or_mem H <;> contradiction
    · simp only [Pi.smul_apply, LinearMapClass.map_smul, Opens.apply_def] at wa wr ⊢
      rw [mul_comm, ← Algebra.smul_def] at wr
      rw [sections_smul_localizations_def, ← wa, ← mul_smul, ← smul_assoc, mul_comm sr, mul_smul,
        wr, mul_comm rr, Algebra.smul_def,
        ← IsScalarTower.algebraMap_smul (R := R) (Localization.AtPrime y.1.asIdeal), map_mul]
      rfl

end Tilde

/--
For any `R`-module `M`, `TildeInType R M` is the sheaf of set on `Spec R` whose sections on `U` are
the dependent functions that are locally fractions. This is often denoted by `M^~`.

See also `Tilde.isLocallyFraction`.
-/
def tildeInType : Sheaf (Type u) (PrimeSpectrum.Top R) :=
  subsheafToTypes (Tilde.isLocallyFraction M)

noncomputable instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    AddCommGroup (M.tildeInType.1.obj U) :=
  inferInstanceAs <| AddCommGroup (Tilde.sectionsSubmodule M U)

set_option backward.isDefEq.respectTransparency false in
noncomputable instance (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Module ((Spec <| .of R).ringCatSheaf.1.obj U) (M.tildeInType.1.obj U) :=
  inferInstanceAs <| Module _ (Tilde.sectionsSubmodule M U)

/--
`M^~` as a sheaf of `𝒪_{Spec R}`-modules
-/
def tilde : (Spec R).Modules where
  val := moduleStructurePresheaf R M
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    (structureSheafInType R M).2

set_option backward.isDefEq.respectTransparency false in
/--
This is `M^~` as a sheaf of `R`-modules.
-/
noncomputable def tildeInModuleCat :
    TopCat.Presheaf (ModuleCat R) (PrimeSpectrum.Top R) :=
  (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) <|
    Limits.initialOpOfTerminal Limits.isTerminalTop).obj (tilde M).1 ⋙
  ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso R).hom.hom

/-- (Implementation). The image of `tilde` under `modulesSpecToSheaf` is isomorphic to
`structurePresheafInModuleCat`. They are defeq as types but the `Smul` instance are not defeq. -/
noncomputable
def modulesSpecToSheafIso :
    (modulesSpecToSheaf.obj (tilde M)).1 ≅ structurePresheafInModuleCat R M :=
  NatIso.ofComponents (fun U ↦ LinearEquiv.toModuleIso
    (X₁ := (modulesSpecToSheaf.obj (tilde M)).presheaf.obj _)
    { __ := AddEquiv.refl _,
      map_smul' r m := IsScalarTower.algebraMap_smul (M := ((structureSheafInType R M).val.obj U))
        ((structureSheafInType R R).val.obj U) r m }) fun _ ↦ rfl

/-- The map from `M` to `Γ(M, U)`. This is a localiation map when `U = D(f)`. -/
def toOpen (U : (Spec R).Opens) : M ⟶ (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (.op U) :=
  ModuleCat.ofHom (StructureSheaf.toOpenₗ R M U) ≫ ((modulesSpecToSheafIso M).app _).inv

lemma smul_section_apply (r : R) (U : Opens (PrimeSpectrum.Top R))
    (s : (tildeInModuleCat M).obj (op U)) (x : U) :
    (r • s).1 x = r • (s.1 x) :=
  IsScalarTower.algebraMap_smul ((Spec.structureSheaf R).val.obj (op U)) r (s.1 x)

lemma smul_stalk_no_nonzero_divisor {x : PrimeSpectrum R}
    (r : x.asIdeal.primeCompl) (st : (tildeInModuleCat M).stalk x) (hst : r.1 • st = 0) :
    st = 0 :=
  Limits.Concrete.colimit_no_zero_smul_divisor _ _ _
    ⟨op ⟨PrimeSpectrum.basicOpen r.1, r.2⟩, fun U i s hs ↦ Subtype.ext <| funext fun pt ↦
    LocalizedModule.eq_zero_of_smul_eq_zero _ (i.unop pt).2 _
    (by simpa [← smul_section_apply] using congr(($hs).1 pt))⟩ _ hst

set_option backward.isDefEq.respectTransparency false in
/--
If `U` is an open subset of `Spec R`, this is the morphism of `R`-modules from `M` to
`M^~(U)`.
-/
noncomputable def toOpen (U : Opens (PrimeSpectrum.Top R)) :
    ModuleCat.of R M ⟶ (tildeInModuleCat M).obj (op U) :=
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`
  -- This suggests `restrictScalars` needs to be redesigned.
  ModuleCat.ofHom (Y := (tildeInModuleCat M).obj (op U))
  { toFun := fun f =>
    ⟨fun x ↦ LocalizedModule.mkLinearMap _ _ f, fun x ↦
      ⟨U, x.2, 𝟙 _, f, 1, fun y ↦ ⟨(Ideal.ne_top_iff_one _).1 y.1.2.1, by simp⟩⟩⟩
    map_add' := fun f g => Subtype.ext <| funext fun x ↦ map_add _ _ _
    map_smul' := fun r m => by
      apply Subtype.val_injective
      ext x
      simp only [isLocallyFraction_pred, LocalizedModule.mkLinearMap_apply, LinearMapClass.map_smul,
        RingHom.id_apply, smul_section_apply] }

@[simp]
theorem toOpen_res (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U) :
    toOpen M U ≫ (modulesSpecToSheaf.obj (tilde M)).presheaf.map i.op = toOpen M V :=
  rfl

instance (f : R) : IsLocalizedModule (.powers f) (toOpen M (basicOpen f)).hom :=
  .of_linearEquiv (.powers f) (StructureSheaf.toOpenₗ R M (basicOpen f))
    ((modulesSpecToSheafIso M).app _).toLinearEquiv.symm

noncomputable
instance (x : PrimeSpectrum.Top R) : Module R ((tilde M).presheaf.stalk x) :=
  inferInstanceAs (Module R ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf x))

/--
If `x` is a point of `Spec R`, this is the morphism of `R`-modules from `M` to the stalk of
`M^~` at `x`.
-/
noncomputable def toStalk (x : PrimeSpectrum.Top R) :
    ModuleCat.of R M ⟶ TopCat.Presheaf.stalk (tildeInModuleCat M) x :=
  (toOpen M ⊤ ≫ TopCat.Presheaf.germ (tildeInModuleCat M) ⊤ x (by trivial))

set_option backward.isDefEq.respectTransparency false in
open LocalizedModule TopCat.Presheaf in
lemma isUnit_toStalk (x : PrimeSpectrum.Top R) (r : x.asIdeal.primeCompl) :
    IsUnit ((algebraMap R (Module.End R ((tildeInModuleCat M).stalk x))) r) := by
  rw [Module.End.isUnit_iff]
  refine ⟨LinearMap.ker_eq_bot.1 <| eq_bot_iff.2 fun st (h : r.1 • st = 0) ↦
    smul_stalk_no_nonzero_divisor M r st h, fun st ↦ ?_⟩
  obtain ⟨U, mem, s, rfl⟩ := germ_exist (F := M.tildeInModuleCat) x st
  let O := U ⊓ (PrimeSpectrum.basicOpen r)
  refine ⟨germ M.tildeInModuleCat O x ⟨mem, r.2⟩
    ⟨fun q ↦ (Localization.mk 1 ⟨r, q.2.2⟩ : Localization.AtPrime q.1.asIdeal) • s.1
      ⟨q.1, q.2.1⟩, fun q ↦ ?_⟩, by
        simpa only [Module.algebraMap_end_apply, ← map_smul] using
          germ_ext (C := ModuleCat R) (W := O) (hxW := ⟨mem, r.2⟩) (iWU := 𝟙 _)
            (iWV := homOfLE inf_le_left) _ <|
          Subtype.ext <| funext fun y ↦ by
            simp [smul_section_apply, ← smul_assoc, Localization.smul_mk]; rfl⟩
  obtain ⟨V, mem_V, iV, num, den, hV⟩ := s.2 ⟨q.1, q.2.1⟩
  refine ⟨V ⊓ O, ⟨mem_V, q.2⟩, homOfLE inf_le_right, num, r * den, fun y ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hV ⟨y, y.2.1⟩
  refine ⟨y.1.asIdeal.primeCompl.mul_mem y.2.2.2 h1, ?_⟩
  simp only [Opens.apply_def, isLocallyFraction_pred, mkLinearMap_apply,
    smul_eq_iff_of_mem (S := y.1.1.primeCompl) (hr := h1), mk_smul_mk, one_smul, mul_one] at h2 ⊢
  simpa only [h2, mk_smul_mk, one_smul, smul'_mk, mk_eq] using ⟨1, by simp only [one_smul]; rfl⟩

/--
The morphism of `R`-modules from the localization of `M` at the prime ideal corresponding to `x`
to the stalk of `M^~` at `x`.
-/
noncomputable def localizationToStalk (x : PrimeSpectrum.Top R) :
    ModuleCat.of R (LocalizedModule x.asIdeal.primeCompl M) ⟶
    (TopCat.Presheaf.stalk (tildeInModuleCat M) x) :=
  ModuleCat.ofHom <| LocalizedModule.lift _ (toStalk M x).hom <| isUnit_toStalk M x


set_option backward.isDefEq.respectTransparency false in
/-- The ring homomorphism that takes a section of the structure sheaf of `R` on the open set `U`,
implemented as a subtype of dependent functions to localizations at prime ideals, and evaluates
the section on the point corresponding to a given prime ideal. -/
noncomputable def openToLocalization
    (U : Opens (PrimeSpectrum R)) (x : PrimeSpectrum R) (hx : x ∈ U) :
    (tildeInModuleCat M).obj (op U) ⟶
    ModuleCat.of R (LocalizedModule x.asIdeal.primeCompl M) :=
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(X := ...)` and `(Y := ...)`
  -- This suggests `restrictScalars` needs to be redesigned.
  ModuleCat.ofHom
    (X := (tildeInModuleCat M).obj (op U))
    (Y := ModuleCat.of R (LocalizedModule x.asIdeal.primeCompl M))
  { toFun := fun s => (s.1 ⟨x, hx⟩ :)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => by simp [smul_section_apply] }

/--
The morphism of `R`-modules from the stalk of `M^~` at `x` to the localization of `M` at the
prime ideal of `R` corresponding to `x`.
-/
noncomputable def stalkToFiberLinearMap (x : PrimeSpectrum.Top R) :
    (tildeInModuleCat M).stalk x ⟶
    ModuleCat.of R (LocalizedModule x.asIdeal.primeCompl M) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (tildeInModuleCat M))
    { pt := _
      ι :=
      { app := fun U => openToLocalization M ((OpenNhds.inclusion _).obj U.unop) x U.unop.2 } }

@[simp]
theorem germ_comp_stalkToFiberLinearMap (U : Opens (PrimeSpectrum.Top R)) (x) (hx : x ∈ U) :
    (tildeInModuleCat M).germ U x hx ≫ stalkToFiberLinearMap M x =
    openToLocalization M U x hx :=
  Limits.colimit.ι_desc _ _

@[simp]
theorem stalkToFiberLinearMap_germ (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) (s : (tildeInModuleCat M).obj (op U)) :
    (stalkToFiberLinearMap M x).hom
      (TopCat.Presheaf.germ (tildeInModuleCat M) U x hx s) = (s.1 ⟨x, hx⟩ :) :=
  DFunLike.ext_iff.1 (ModuleCat.hom_ext_iff.mp (germ_comp_stalkToFiberLinearMap M U x hx)) s

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem toOpen_germ (U : Opens (PrimeSpectrum.Top R)) (x) (hx : x ∈ U) :
    toOpen M U ≫ M.tildeInModuleCat.germ U x hx = toStalk M x := by
  rw [← toOpen_res M ⊤ U (homOfLE le_top : U ⟶ ⊤), Category.assoc, Presheaf.germ_res]; rfl

@[reassoc (attr := simp)]
theorem toStalk_comp_stalkToFiberLinearMap (x : PrimeSpectrum.Top R) :
    toStalk M x ≫ stalkToFiberLinearMap M x =
    ofHom (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M) := by
  rw [toStalk, Category.assoc, germ_comp_stalkToFiberLinearMap]; rfl

theorem stalkToFiberLinearMap_toStalk (x : PrimeSpectrum.Top R) (m : M) :
    (stalkToFiberLinearMap M x).hom (toStalk M x m) =
    LocalizedModule.mk m 1 :=
  LinearMap.ext_iff.1 (ModuleCat.hom_ext_iff.mp (toStalk_comp_stalkToFiberLinearMap M x)) _

set_option backward.isDefEq.respectTransparency false in
/--
If `U` is an open subset of `Spec R`, `m` is an element of `M` and `r` is an element of `R`
that is invertible on `U` (i.e. does not belong to any prime ideal corresponding to a point
in `U`), this is `m / r` seen as a section of `M^~` over `U`.
-/
def const (m : M) (r : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : ∀ x ∈ U, r ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) :
    (tildeInModuleCat M).obj (op U) :=
  ⟨fun x => LocalizedModule.mk m ⟨r, hu x x.2⟩, fun x =>
    ⟨U, x.2, 𝟙 _, m, r, fun y => ⟨hu _ y.2, by
      simpa only [LocalizedModule.mkLinearMap_apply, LocalizedModule.smul'_mk,
        LocalizedModule.mk_eq] using ⟨1, by simp⟩⟩⟩⟩

@[simp]
theorem const_apply (m : M) (r : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : ∀ x ∈ U, r ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) (x : U) :
    (const M m r U hu).1 x = LocalizedModule.mk m ⟨r, hu x x.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem exists_const (U) (s : (tildeInModuleCat M).obj (op U)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) :
    ∃ (V : Opens (PrimeSpectrum.Top R)) (_ : x ∈ V) (i : V ⟶ U) (f : M) (g : R) (hg : _),
      const M f g V hg = (tildeInModuleCat M).map i.op s :=
  let ⟨V, hxV, iVU, f, g, hfg⟩ := s.2 ⟨x, hx⟩
  ⟨V, hxV, iVU, f, g, fun y hyV => (hfg ⟨y, hyV⟩).1, Subtype.ext <| funext fun y => by
    obtain ⟨h1, (h2 : g • s.1 ⟨y, _⟩ = LocalizedModule.mk f 1)⟩ := hfg y
    exact show LocalizedModule.mk f ⟨g, by exact h1⟩ = s.1 (iVU y) by
      set x := s.1 (iVU y); change g • x = _ at h2; clear_value x
      induction x using LocalizedModule.induction_on with
      | h a b =>
        rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at h2
        obtain ⟨c, hc⟩ := h2
        exact LocalizedModule.mk_eq.mpr ⟨c, by simpa using hc.symm⟩⟩

@[simp]
theorem res_const (f : M) (g : R) (U hu V hv i) :
    (tildeInModuleCat M).map i (const M f g U hu) = const M f g V hv :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem localizationToStalk_mk (x : PrimeSpectrum.Top R) (f : M) (s : x.asIdeal.primeCompl) :
    (localizationToStalk M x).hom (LocalizedModule.mk f s) =
      (tildeInModuleCat M).germ (PrimeSpectrum.basicOpen (s : R)) x s.2
        (const M f s (PrimeSpectrum.basicOpen s) fun _ => id) :=
  (Module.End.isUnit_iff _ |>.1 (isUnit_toStalk M x s)).injective <| by
  erw [← Module.End.mul_apply]
  simp only [IsUnit.mul_val_inv, Module.End.one_apply, Module.algebraMap_end_apply]
  change (M.tildeInModuleCat.germ ⊤ x ⟨⟩) ((toOpen M ⊤) f) = _
  rw [← map_smul]
  fapply TopCat.Presheaf.germ_ext (W := PrimeSpectrum.basicOpen s.1) (hxW := s.2)
    (F := M.tildeInModuleCat)
  · exact homOfLE le_top
  · exact 𝟙 _
  refine Subtype.ext <| funext fun y => show LocalizedModule.mk f 1 = _ from ?_
  dsimp
  simp only [CategoryTheory.Functor.map_id, hom_id, map_smul, LinearMap.id_coe, id_eq,
    smul_section_apply, isLocallyFraction_pred, Opens.val_apply, LocalizedModule.mkLinearMap_apply,
    const_apply, LocalizedModule.smul'_mk]
  exact (LocalizedModule.mk_cancel ⟨s.1, _⟩ f).symm

/--
The isomorphism of `R`-modules from the stalk of `M^~` at `x` to the localization of `M` at the
prime ideal corresponding to `x`.
-/
@[simps]
noncomputable def stalkIso (x : PrimeSpectrum.Top R) :
    TopCat.Presheaf.stalk (tildeInModuleCat M) x ≅
    ModuleCat.of R (LocalizedModule x.asIdeal.primeCompl M) where
  hom := stalkToFiberLinearMap M x
  inv := localizationToStalk M x
  hom_inv_id := TopCat.Presheaf.stalk_hom_ext _ fun U hxU ↦ ModuleCat.hom_ext <|
      LinearMap.ext fun s ↦ by
    change localizationToStalk M x (stalkToFiberLinearMap M x (M.tildeInModuleCat.germ U x hxU s)) =
      M.tildeInModuleCat.germ U x hxU s
    rw [stalkToFiberLinearMap_germ]
    obtain ⟨V, hxV, iVU, f, g, (hg : V ≤ PrimeSpectrum.basicOpen _), hs⟩ :=
      exists_const _ _ s x hxU
    have := res_apply M U V iVU s ⟨x, hxV⟩
    dsimp only [isLocallyFraction_pred, Opens.val_apply, LocalizedModule.mkLinearMap_apply,
      Opens.apply_mk] at this
    rw [← this, ← hs, const_apply, localizationToStalk_mk]
    exact (tildeInModuleCat M).germ_ext V hxV (homOfLE hg) iVU <| hs ▸ rfl
  inv_hom_id := by ext x; exact x.induction_on (fun _ _ => by
    simp only [hom_comp, LinearMap.coe_comp, Function.comp_apply, hom_id, LinearMap.id_coe, id_eq]
    rw [localizationToStalk_mk, stalkToFiberLinearMap_germ]
    simp)

instance (x : PrimeSpectrum.Top R) :
    IsLocalizedModule x.asIdeal.primeCompl (toStalk M x).hom :=
  inferInstanceAs (IsLocalizedModule x.asIdeal.primeCompl (StructureSheaf.toStalkₗ ..))

/-- The tilde construction is functorial. -/
protected noncomputable def map {M N : ModuleCat R} (f : M ⟶ N) : tilde M ⟶ tilde N :=
  SpecModulesToSheafFullyFaithful.preimage ⟨(modulesSpecToSheafIso M).hom ≫
    { app U := ModuleCat.ofHom (StructureSheaf.comapₗ f.hom _ _ .rfl) } ≫
    (modulesSpecToSheafIso N).inv⟩

@[reassoc (attr := simp)]
lemma toOpen_map_app {M N : ModuleCat R} (f : M ⟶ N)
    (U : TopologicalSpace.Opens (PrimeSpectrum R)) :
    toOpen M U ≫ (modulesSpecToSheaf.map (tilde.map f)).1.app _ =
    f ≫ toOpen N U := by
  ext x; exact Subtype.ext (funext fun y ↦ IsLocalizedModule.map_apply y.1.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl M)
     (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl N) _ x)

variable (R) in
/-- Tilde as a functor -/
@[simps] protected noncomputable def functor : ModuleCat R ⥤ (Spec (.of R)).Modules where
  obj := tilde
  map := tilde.map
  map_id M := by
    ext p x
    exact Subtype.ext (funext fun y ↦ DFunLike.congr_fun (LocalizedModule.map_id _) _)
  map_comp {M N P} f g := by
    ext p x
    exact Subtype.ext (funext
      fun y ↦ DFunLike.congr_fun (IsLocalizedModule.map_comp' y.1.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl M)
        (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl N)
        (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl P) _ _) _)

instance isIso_toOpen_top {M : ModuleCat R} : IsIso (toOpen M ⊤) := by
  rw [toOpen, isIso_comp_right_iff, ConcreteCategory.isIso_iff_bijective]
  exact StructureSheaf.toOpenₗ_top_bijective

/-- The isomorphism between the global sections of `M^~` and `M`. -/
@[simps! hom]
noncomputable def isoTop (M : ModuleCat R) :
    M ≅ (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (.op ⊤) :=
  asIso (toOpen M ⊤)

open PrimeSpectrum in
lemma isUnit_algebraMap_end_basicOpen (M : (Spec (.of R)).Modules) (f : R) :
    IsUnit (algebraMap R (Module.End R
      ((modulesSpecToSheaf.obj M).presheaf.obj (.op (basicOpen f)))) f) := by
  rw [Module.End.isUnit_iff]
  change Function.Bijective (algebraMap Γ(Spec R, basicOpen f)
      (Module.End Γ(Spec R, basicOpen f) Γ(M, basicOpen f)) (algebraMap R _ f))
  rw [← Module.End.isUnit_iff]
  exact (IsLocalization.Away.algebraMap_isUnit _).map _

end tilde

/-- This is the counit of the tilde-Gamma adjunction. -/
noncomputable def Scheme.Modules.fromTildeΓ (M : (Spec (.of R)).Modules) :
    tilde ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) ⟶ M :=
  SpecModulesToSheafFullyFaithful.preimage
    ⟨TopCat.Sheaf.restrictHomEquivHom _ _ isBasis_basic_opens
    { app (f : Rᵒᵖ) := by
        refine (ModuleCat.ofHom (IsLocalizedModule.lift (.powers (M := R) f.unop)
          (tilde.toOpen _ (PrimeSpectrum.basicOpen f.unop)).hom
          ((modulesSpecToSheaf.obj M).val.map (homOfLE le_top).op).hom ?_):)
        rw [Subtype.forall]
        change Submonoid.powers _ ≤ (IsUnit.submonoid _).comap _
        simp only [inducedFunctor_obj, Submonoid.powers_le, Submonoid.mem_comap]
        exact tilde.isUnit_algebraMap_end_basicOpen M f.unop
      naturality {f g : Rᵒᵖ} i := by
        letI N := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)
        ext1
        apply IsLocalizedModule.ext (.powers (M := R) f.unop)
          (tilde.toOpen _ (PrimeSpectrum.basicOpen (R := R) f.unop)).hom
        · rw [Subtype.forall]
          change Submonoid.powers _ ≤ (IsUnit.submonoid _).comap _
          simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
          obtain ⟨n, a, e⟩ : ∃ n, f.unop ∣ g.unop ^ n := by
            simpa only [Ideal.mem_radical_iff, Ideal.mem_span_singleton] using
              (basicOpen_le_basicOpen_iff _ _).mp (i.1.hom.le)
          refine ((Commute.isUnit_mul_iff (b := algebraMap R _ a) (.map (.all _ _) _)).mp ?_).1
          rw [← map_mul, ← e, map_pow]
          exact (tilde.isUnit_algebraMap_end_basicOpen M g.unop).pow n
        · dsimp [← ModuleCat.hom_comp]
          rw [tilde.toOpen_res_assoc]
          ext x
          dsimp
          simp only [IsLocalizedModule.lift_apply, ← ModuleCat.comp_apply, ← Functor.map_comp]
          rfl }⟩

@[reassoc]
lemma Scheme.Modules.toOpen_fromTildeΓ_app (M : (Spec (.of R)).Modules) (U) :
    tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) U ≫
      (modulesSpecToSheaf.map M.fromTildeΓ).1.app (.op U) =
    (modulesSpecToSheaf.obj M).1.map (homOfLE le_top).op := by
  wlog hU : U = PrimeSpectrum.basicOpen 1 generalizing U
  · rw [← tilde.toOpen_res _ (PrimeSpectrum.basicOpen 1) _ (homOfLE (by simp)), Category.assoc,
      NatTrans.naturality, ← Category.assoc, this, ← Functor.map_comp, ← op_comp, homOfLE_comp]
    simp
  subst hU
  simp only [fromTildeΓ, inducedFunctor_obj,
    homOfLE_leOfHom, Functor.FullyFaithful.map_preimage, TopCat.Sheaf.extend_hom_app]
  ext x
  refine (IsLocalizedModule.lift_apply (.powers (M := R) 1)
    (tilde.toOpen _ (PrimeSpectrum.basicOpen (R := R) 1)).hom
    ((modulesSpecToSheaf.obj M).val.map (homOfLE le_top).op).hom (by simp) x)

/-- This is the counit of the tilde-Gamma adjunction. -/
noncomputable def Scheme.Modules.fromTildeΓNatTrans :
    moduleSpecΓFunctor (R := R) ⋙ tilde.functor (R := R) ⟶ 𝟭 _ where
  app := fromTildeΓ
  naturality {M N} f := by
    apply SpecModulesToSheafFullyFaithful.map_injective
    apply CategoryTheory.Sheaf.hom_ext
    apply (TopCat.Sheaf.restrictHomEquivHom _ _ PrimeSpectrum.isBasis_basic_opens).symm.injective
    ext r : 3
    apply IsLocalizedModule.ext (.powers (M := R) r.unop)
      (tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤))
        (PrimeSpectrum.basicOpen (R := R) r.unop)).hom
    · rw [Subtype.forall]
      change Submonoid.powers _ ≤ (IsUnit.submonoid _).comap _
      simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      exact tilde.isUnit_algebraMap_end_basicOpen ..
    dsimp [TopCat.Sheaf.restrictHomEquivHom, Functor.IsCoverDense.restrictHomEquivHom,
      moduleSpecΓFunctor, Sheaf.forget]
    simp only [← ModuleCat.hom_comp, Functor.map_comp]
    rw [CategoryTheory.Sheaf.comp_val, CategoryTheory.Sheaf.comp_val]
    congr 1
    simp only [NatTrans.comp_app]
    rw [tilde.toOpen_map_app_assoc, toOpen_fromTildeΓ_app N (PrimeSpectrum.basicOpen r.unop),
      toOpen_fromTildeΓ_app_assoc M (PrimeSpectrum.basicOpen r.unop),
      ← (modulesSpecToSheaf.map f).val.naturality]

/-- `tilde.isoTop` bundled as a natural isomorphism.
This is the unit of the tilde-Gamma adjunction. -/
def tilde.toTildeΓNatIso : 𝟭 _ ≅ tilde.functor R ⋙ moduleSpecΓFunctor :=
  NatIso.ofComponents tilde.isoTop fun f ↦ (tilde.toOpen_map_app f _).symm

open Scheme.Modules in
/-- The tilde-Gamma adjuntion. -/
def tilde.adjunction : tilde.functor R ⊣ moduleSpecΓFunctor where
  unit := toTildeΓNatIso.hom
  counit := fromTildeΓNatTrans
  left_triangle_components M := by
    apply SpecModulesToSheafFullyFaithful.map_injective
    apply CategoryTheory.Sheaf.hom_ext
    apply (TopCat.Sheaf.restrictHomEquivHom _ _ PrimeSpectrum.isBasis_basic_opens).symm.injective
    ext r : 3
    apply IsLocalizedModule.ext (.powers (M := R) r.unop)
      (toOpen _ (PrimeSpectrum.basicOpen (R := R) r.unop)).hom
    · rw [Subtype.forall]
      change Submonoid.powers _ ≤ (IsUnit.submonoid _).comap _
      simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      exact isUnit_algebraMap_end_basicOpen ..
    dsimp [toTildeΓNatIso, isoTop,
      TopCat.Sheaf.restrictHomEquivHom, Functor.IsCoverDense.restrictHomEquivHom,
      fromTildeΓNatTrans, moduleSpecΓFunctor, Sheaf.forget, sheafToPresheaf]
    simp only [← ModuleCat.hom_comp, Functor.map_comp]
    congr 1
    rw [CategoryTheory.Sheaf.comp_val]
    dsimp
    rw [toOpen_map_app_assoc, toOpen_fromTildeΓ_app]
    rfl
  right_triangle_components M := by
    dsimp [toTildeΓNatIso, fromTildeΓNatTrans, tilde.isoTop, moduleSpecΓFunctor, Sheaf.forget]
    rw [toOpen_fromTildeΓ_app]
    exact (modulesSpecToSheaf.obj M).val.map_id _

instance : IsIso (tilde.adjunction (R := R)).unit := by
  dsimp [tilde.adjunction]; infer_instance

/-- The tilde functor is fully faithful. We will later show that the essential image is
exactly quasi-coherent modules. -/
def tilde.fullyFaithfulFunctor : (tilde.functor R).FullyFaithful :=
  tilde.adjunction.fullyFaithfulLOfIsIsoUnit

instance : (tilde.functor (R := R)).Full := tilde.fullyFaithfulFunctor.full
instance : (tilde.functor (R := R)).Faithful :=
  tilde.fullyFaithfulFunctor.faithful
instance : (tilde.functor (R := R)).IsLeftAdjoint := tilde.adjunction.isLeftAdjoint

end AlgebraicGeometry

namespace ModuleCat

@[deprecated (since := "2026-02-11")] noncomputable alias tilde := AlgebraicGeometry.tilde
@[deprecated (since := "2026-02-11")] noncomputable alias Tilde.toOpen := tilde.toOpen
@[deprecated (since := "2026-02-11")] alias Tilde.toOpen_res := tilde.toOpen_res
@[deprecated (since := "2026-02-11")] noncomputable alias Tilde.toStalk := tilde.toStalk

end ModuleCat
