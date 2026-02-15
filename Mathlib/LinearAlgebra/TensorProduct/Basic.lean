/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Defs

/-!
# Universal property of the tensor product

Given any bilinear map `f : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂`, there is a unique semilinear map
`TensorProduct.lift f : TensorProduct R M N →ₛₗ[σ₁₂] P₂` whose composition with the canonical
bilinear map `TensorProduct.mk` is the given bilinear map `f`.  Uniqueness is shown in the theorem
`TensorProduct.lift.unique`.

## Tags

bilinear, tensor, tensor product
-/

@[expose] public section

section Semiring

variable {R R₂ R₃ R' R'' : Type*}
variable [CommSemiring R] [CommSemiring R₂] [CommSemiring R₃] [Monoid R'] [Semiring R'']
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variable {A M N P Q S : Type*}
variable {M₂ M₃ N₂ N₃ P' P₂ P₃ Q' Q₂ Q₃ : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [AddCommMonoid S]
variable [AddCommMonoid P'] [AddCommMonoid Q']
variable [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P₂] [AddCommMonoid Q₂]
variable [AddCommMonoid M₃] [AddCommMonoid N₃] [AddCommMonoid P₃] [AddCommMonoid Q₃]
variable [DistribMulAction R' M]
variable [Module R'' M]
variable [Module R M] [Module R N] [Module R S]
variable [Module R P'] [Module R Q']
variable [Module R₂ M₂] [Module R₂ N₂] [Module R₂ P₂] [Module R₂ Q₂]
variable [Module R₃ M₃] [Module R₃ N₃] [Module R₃ P₃] [Module R₃ Q₃]

variable (M N)

namespace TensorProduct

section Module

variable {M N}

/-- Lift an `R`-balanced map to the tensor product.
A map `f : M →+ N →+ P` additive in both components is `R`-balanced, or middle linear with respect
to `R`, if scalar multiplication in either argument is equivalent, `f (r • m) n = f m (r • n)`.
Note that strictly the first action should be a right-action by `R`, but for now `R` is commutative
so it doesn't matter. -/
-- TODO: use this to implement `lift` and `SMul.aux`. For now we do not do this as it causes
-- performance issues elsewhere.
def liftAddHom (f : M →+ N →+ P)
    (hf : ∀ (r : R) (m : M) (n : N), f (r • m) n = f m (r • n)) :
    M ⊗[R] N →+ P :=
  (addConGen (TensorProduct.Eqv R M N)).lift (FreeAddMonoid.lift (fun mn : M × N => f mn.1 mn.2)) <|
    AddCon.addConGen_le fun x y hxy =>
      match x, y, hxy with
      | _, _, .of_zero_left n =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, map_zero,
          AddMonoidHom.zero_apply]
      | _, _, .of_zero_right m =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, map_zero]
      | _, _, .of_add_left m₁ m₂ n =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, FreeAddMonoid.lift_eval_of, map_add,
          AddMonoidHom.add_apply]
      | _, _, .of_add_right m n₁ n₂ =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, FreeAddMonoid.lift_eval_of, map_add]
      | _, _, .of_smul s m n =>
        (AddCon.ker_rel _).2 <| by rw [FreeAddMonoid.lift_eval_of, FreeAddMonoid.lift_eval_of, hf]
      | _, _, .add_comm x y =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, add_comm]

@[simp]
theorem liftAddHom_tmul (f : M →+ N →+ P)
    (hf : ∀ (r : R) (m : M) (n : N), f (r • m) n = f m (r • n)) (m : M) (n : N) :
    liftAddHom f hf (m ⊗ₜ n) = f m n :=
  rfl

variable (M) in
@[simp]
theorem zero_tmul (n : N) : (0 : M) ⊗ₜ[R] n = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero_left _

theorem add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) ⊗ₜ n = m₁ ⊗ₜ n + m₂ ⊗ₜ[R] n :=
  Eq.symm <| Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_add_left _ _ _

variable (N) in
@[simp]
theorem tmul_zero (m : M) : m ⊗ₜ[R] (0 : N) = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero_right _

theorem tmul_add (m : M) (n₁ n₂ : N) : m ⊗ₜ (n₁ + n₂) = m ⊗ₜ n₁ + m ⊗ₜ[R] n₂ :=
  Eq.symm <| Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_add_right _ _ _

instance uniqueLeft [Subsingleton M] : Unique (M ⊗[R] N) where
  default := 0
  uniq z := z.induction_on rfl (fun x y ↦ by rw [Subsingleton.elim x 0, zero_tmul]) <| by
    rintro _ _ rfl rfl; apply add_zero

instance uniqueRight [Subsingleton N] : Unique (M ⊗[R] N) where
  default := 0
  uniq z := z.induction_on rfl (fun x y ↦ by rw [Subsingleton.elim y 0, tmul_zero]) <| by
    rintro _ _ rfl rfl; apply add_zero

section

variable (R R' M N)

/-- A typeclass for `SMul` structures which can be moved across a tensor product.

This typeclass is generated automatically from an `IsScalarTower` instance, but exists so that
we can also add an instance for `AddCommGroup.toIntModule`, allowing `z •` to be moved even if
`R` does not support negation.

Note that `Module R' (M ⊗[R] N)` is available even without this typeclass on `R'`; it's only
needed if `TensorProduct.smul_tmul`, `TensorProduct.smul_tmul'`, or `TensorProduct.tmul_smul` is
used.
-/
class CompatibleSMul [DistribMulAction R' N] : Prop where
  smul_tmul : ∀ (r : R') (m : M) (n : N), (r • m) ⊗ₜ n = m ⊗ₜ[R] (r • n)

end

/-- Note that this provides the default `CompatibleSMul R R M N` instance through
`IsScalarTower.left`. -/
instance (priority := 100) CompatibleSMul.isScalarTower [SMul R' R] [IsScalarTower R' R M]
    [DistribMulAction R' N] [IsScalarTower R' R N] : CompatibleSMul R R' M N :=
  ⟨fun r m n => by
    conv_lhs => rw [← one_smul R m]
    conv_rhs => rw [← one_smul R n]
    rw [← smul_assoc, ← smul_assoc]
    exact Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_smul _ _ _⟩

/-- `smul` can be moved from one side of the product to the other . -/
theorem smul_tmul [DistribMulAction R' N] [CompatibleSMul R R' M N] (r : R') (m : M) (n : N) :
    (r • m) ⊗ₜ n = m ⊗ₜ[R] (r • n) :=
  CompatibleSMul.smul_tmul _ _ _

set_option backward.privateInPublic true in
@[instance_reducible]
private def addMonoidWithWrongNSMul : AddMonoid (M ⊗[R] N) :=
  { (addConGen (TensorProduct.Eqv R M N)).addMonoid with }

attribute [local instance] addMonoidWithWrongNSMul in
/-- Auxiliary function to defining scalar multiplication on tensor product. -/
def SMul.aux {R' : Type*} [SMul R' M] (r : R') : FreeAddMonoid (M × N) →+ M ⊗[R] N :=
  FreeAddMonoid.lift fun p : M × N => (r • p.1) ⊗ₜ p.2

theorem SMul.aux_of {R' : Type*} [SMul R' M] (r : R') (m : M) (n : N) :
    SMul.aux r (.of (m, n)) = (r • m) ⊗ₜ[R] n :=
  rfl

variable [SMulCommClass R R' M] [SMulCommClass R R'' M]

/-- Given two modules over a commutative semiring `R`, if one of the factors carries a
(distributive) action of a second type of scalars `R'`, which commutes with the action of `R`, then
the tensor product (over `R`) carries an action of `R'`.

This instance defines this `R'` action in the case that it is the left module which has the `R'`
action. Two natural ways in which this situation arises are:
* Extension of scalars
* A tensor product of a group representation with a module not carrying an action

Note that in the special case that `R = R'`, since `R` is commutative, we just get the usual scalar
action on a tensor product of two modules. This special case is important enough that, for
performance reasons, we define it explicitly below. -/
instance leftHasSMul : SMul R' (M ⊗[R] N) :=
  ⟨fun r =>
    (addConGen (TensorProduct.Eqv R M N)).lift (SMul.aux r : _ →+ M ⊗[R] N) <|
      AddCon.addConGen_le fun x y hxy =>
        match x, y, hxy with
        | _, _, .of_zero_left n =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_zero, SMul.aux_of, smul_zero, zero_tmul]
        | _, _, .of_zero_right m =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_zero, SMul.aux_of, tmul_zero]
        | _, _, .of_add_left m₁ m₂ n =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, SMul.aux_of, smul_add, add_tmul]
        | _, _, .of_add_right m n₁ n₂ =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, SMul.aux_of, tmul_add]
        | _, _, .of_smul s m n =>
          (AddCon.ker_rel _).2 <| by rw [SMul.aux_of, SMul.aux_of, ← smul_comm, smul_tmul]
        | _, _, .add_comm x y =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, add_comm]⟩

instance : SMul R (M ⊗[R] N) :=
  TensorProduct.leftHasSMul

protected theorem smul_zero (r : R') : r • (0 : M ⊗[R] N) = 0 :=
  map_zero _

protected theorem smul_add (r : R') (x y : M ⊗[R] N) : r • (x + y) = r • x + r • y :=
  map_add _ _ _

protected theorem zero_smul (x : M ⊗[R] N) : (0 : R'') • x = 0 :=
  have : ∀ (r : R'') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
    (fun m n => by rw [this, zero_smul, zero_tmul]) fun x y ihx ihy => by
    rw [TensorProduct.smul_add, ihx, ihy, add_zero]

protected theorem one_smul (x : M ⊗[R] N) : (1 : R') • x = x :=
  have : ∀ (r : R') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
    (fun m n => by rw [this, one_smul])
    fun x y ihx ihy => by rw [TensorProduct.smul_add, ihx, ihy]

protected theorem add_smul (r s : R'') (x : M ⊗[R] N) : (r + s) • x = r • x + s • x :=
  have : ∀ (r : R'') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by simp_rw [TensorProduct.smul_zero, add_zero])
    (fun m n => by simp_rw [this, add_smul, add_tmul]) fun x y ihx ihy => by
    simp_rw [TensorProduct.smul_add]
    rw [ihx, ihy, add_add_add_comm]

set_option backward.isDefEq.respectTransparency false in
instance addMonoid : AddMonoid (M ⊗[R] N) :=
  { TensorProduct.addZeroClass _ _ with
    toAddSemigroup := TensorProduct.addSemigroup _ _
    toZero := TensorProduct.zero _ _
    nsmul := fun n v => n • v
    nsmul_zero := by simp [TensorProduct.zero_smul]
    nsmul_succ := by simp only [TensorProduct.one_smul, TensorProduct.add_smul, add_comm,
      forall_const] }

instance addCommMonoid : AddCommMonoid (M ⊗[R] N) :=
  { TensorProduct.addCommSemigroup _ _ with
    toAddMonoid := TensorProduct.addMonoid }

variable (R)

theorem _root_.IsAddUnit.tmul_left {n : N} (hn : IsAddUnit n) (m : M) : IsAddUnit (m ⊗ₜ[R] n) := by
  rw [isAddUnit_iff_exists_neg] at hn ⊢
  have ⟨b, eq⟩ := hn
  exact ⟨m ⊗ₜ[R] b, by rw [← tmul_add, eq, tmul_zero]⟩

theorem _root_.IsAddUnit.tmul_right {m : M} (hm : IsAddUnit m) (n : N) : IsAddUnit (m ⊗ₜ[R] n) := by
  rw [isAddUnit_iff_exists_neg] at hm ⊢
  have ⟨b, eq⟩ := hm
  exact ⟨b ⊗ₜ[R] n, by rw [← add_tmul, eq, zero_tmul]⟩

variable {R}

instance leftDistribMulAction : DistribMulAction R' (M ⊗[R] N) :=
  have : ∀ (r : R') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  { smul_add := fun r x y => TensorProduct.smul_add r x y
    mul_smul := fun r s x =>
      x.induction_on (by simp_rw [TensorProduct.smul_zero])
        (fun m n => by simp_rw [this, mul_smul]) fun x y ihx ihy => by
        simp_rw [TensorProduct.smul_add]
        rw [ihx, ihy]
    one_smul := TensorProduct.one_smul
    smul_zero := TensorProduct.smul_zero }

instance : DistribMulAction R (M ⊗[R] N) :=
  TensorProduct.leftDistribMulAction

theorem smul_tmul' (r : R') (m : M) (n : N) : r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n :=
  rfl

@[simp]
theorem tmul_smul [DistribMulAction R' N] [CompatibleSMul R R' M N] (r : R') (x : M) (y : N) :
    x ⊗ₜ (r • y) = r • x ⊗ₜ[R] y :=
  (smul_tmul _ _ _).symm

theorem smul_tmul_smul (r s : R) (m : M) (n : N) : (r • m) ⊗ₜ[R] (s • n) = (r * s) • m ⊗ₜ[R] n := by
  simp_rw [smul_tmul, tmul_smul, mul_smul]

theorem tmul_eq_smul_one_tmul {S : Type*} [Semiring S] [Module R S] [SMulCommClass R S S]
    (s : S) (m : M) : s ⊗ₜ[R] m = s • (1 ⊗ₜ[R] m) := by
  nth_rw 1 [← mul_one s, ← smul_eq_mul, smul_tmul']

instance leftModule : Module R'' (M ⊗[R] N) :=
  { add_smul := TensorProduct.add_smul
    zero_smul := TensorProduct.zero_smul }

instance : Module R (M ⊗[R] N) :=
  TensorProduct.leftModule

instance [Module R''ᵐᵒᵖ M] [IsCentralScalar R'' M] : IsCentralScalar R'' (M ⊗[R] N) where
  op_smul_eq_smul r x :=
    x.induction_on (by rw [smul_zero, smul_zero])
      (fun x y => by rw [smul_tmul', smul_tmul', op_smul_eq_smul]) fun x y hx hy => by
      rw [smul_add, smul_add, hx, hy]

section

-- Like `R'`, `R'₂` provides a `DistribMulAction R'₂ (M ⊗[R] N)`
variable {R'₂ : Type*} [Monoid R'₂] [DistribMulAction R'₂ M]
variable [SMulCommClass R R'₂ M]

/-- `SMulCommClass R' R'₂ M` implies `SMulCommClass R' R'₂ (M ⊗[R] N)` -/
instance smulCommClass_left [SMulCommClass R' R'₂ M] : SMulCommClass R' R'₂ (M ⊗[R] N) where
  smul_comm r' r'₂ x :=
    TensorProduct.induction_on x (by simp_rw [TensorProduct.smul_zero])
      (fun m n => by simp_rw [smul_tmul', smul_comm]) fun x y ihx ihy => by
      simp_rw [TensorProduct.smul_add]; rw [ihx, ihy]

variable [SMul R'₂ R']

/-- `IsScalarTower R'₂ R' M` implies `IsScalarTower R'₂ R' (M ⊗[R] N)` -/
instance isScalarTower_left [IsScalarTower R'₂ R' M] : IsScalarTower R'₂ R' (M ⊗[R] N) :=
  ⟨fun s r x =>
    x.induction_on (by simp)
      (fun m n => by rw [smul_tmul', smul_tmul', smul_tmul', smul_assoc]) fun x y ihx ihy => by
      rw [smul_add, smul_add, smul_add, ihx, ihy]⟩

variable [DistribMulAction R'₂ N] [DistribMulAction R' N]
variable [CompatibleSMul R R'₂ M N] [CompatibleSMul R R' M N]

/-- `IsScalarTower R'₂ R' N` implies `IsScalarTower R'₂ R' (M ⊗[R] N)` -/
instance isScalarTower_right [IsScalarTower R'₂ R' N] : IsScalarTower R'₂ R' (M ⊗[R] N) :=
  ⟨fun s r x =>
    x.induction_on (by simp)
      (fun m n => by rw [← tmul_smul, ← tmul_smul, ← tmul_smul, smul_assoc]) fun x y ihx ihy => by
      rw [smul_add, smul_add, smul_add, ihx, ihy]⟩

end

/-- A short-cut instance for the common case, where the requirements for the `compatible_smul`
instances are sufficient. -/
instance isScalarTower [SMul R' R] [IsScalarTower R' R M] : IsScalarTower R' R (M ⊗[R] N) :=
  TensorProduct.isScalarTower_left

-- or right
variable (R M N) in
/-- The canonical bilinear map `M → N → M ⊗[R] N`. -/
def mk : M →ₗ[R] N →ₗ[R] M ⊗[R] N :=
  LinearMap.mk₂ R (· ⊗ₜ ·) add_tmul (fun c m n => by simp_rw [smul_tmul, tmul_smul])
    tmul_add tmul_smul

@[simp]
theorem mk_apply (m : M) (n : N) : mk R M N m n = m ⊗ₜ n :=
  rfl

theorem ite_tmul (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] :
    (if P then x₁ else 0) ⊗ₜ[R] x₂ = if P then x₁ ⊗ₜ x₂ else 0 := by split_ifs <;> simp

theorem tmul_ite (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] :
    (x₁ ⊗ₜ[R] if P then x₂ else 0) = if P then x₁ ⊗ₜ x₂ else 0 := by split_ifs <;> simp

lemma tmul_single {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] (i : ι) (x : N) (m : M i) (j : ι) :
    x ⊗ₜ[R] Pi.single i m j = (Pi.single i (x ⊗ₜ[R] m) : ∀ i, N ⊗[R] M i) j := by
  by_cases h : i = j <;> aesop

lemma single_tmul {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] (i : ι) (x : N) (m : M i) (j : ι) :
    Pi.single i m j ⊗ₜ[R] x = (Pi.single i (m ⊗ₜ[R] x) : ∀ i, M i ⊗[R] N) j := by
  by_cases h : i = j <;> aesop

section

theorem sum_tmul {α : Type*} (s : Finset α) (m : α → M) (n : N) :
    (∑ a ∈ s, m a) ⊗ₜ[R] n = ∑ a ∈ s, m a ⊗ₜ[R] n := by
  classical
    induction s using Finset.induction with
    | empty => simp
    | insert _ _ has ih => simp [Finset.sum_insert has, add_tmul, ih]

theorem tmul_sum (m : M) {α : Type*} (s : Finset α) (n : α → N) :
    (m ⊗ₜ[R] ∑ a ∈ s, n a) = ∑ a ∈ s, m ⊗ₜ[R] n a := by
  classical
    induction s using Finset.induction with
    | empty => simp
    | insert _ _ has ih => simp [Finset.sum_insert has, tmul_add, ih]

end

variable (R M N)

/-- The simple (aka pure) elements span the tensor product. -/
theorem span_tmul_eq_top : Submodule.span R { t : M ⊗[R] N | ∃ m n, m ⊗ₜ n = t } = ⊤ := by
  ext t; simp only [Submodule.mem_top, iff_true]
  refine t.induction_on ?_ ?_ ?_
  · exact Submodule.zero_mem _
  · intro m n
    apply Submodule.subset_span
    use m, n
  · intro t₁ t₂ ht₁ ht₂
    exact Submodule.add_mem _ ht₁ ht₂

@[simp]
theorem map₂_mk_top_top_eq_top : Submodule.map₂ (mk R M N) ⊤ ⊤ = ⊤ := by
  rw [← top_le_iff, ← span_tmul_eq_top, Submodule.map₂_eq_span_image2]
  exact Submodule.span_mono fun _ ⟨m, n, h⟩ => ⟨m, trivial, n, trivial, h⟩

theorem exists_eq_tmul_of_forall (x : TensorProduct R M N)
    (h : ∀ (m₁ m₂ : M) (n₁ n₂ : N), ∃ m n, m₁ ⊗ₜ n₁ + m₂ ⊗ₜ n₂ = m ⊗ₜ[R] n) :
    ∃ m n, x = m ⊗ₜ n := by
  induction x with
  | zero =>
    use 0, 0
    rw [TensorProduct.zero_tmul]
  | tmul m n => use m, n
  | add x y h₁ h₂ =>
    obtain ⟨m₁, n₁, rfl⟩ := h₁
    obtain ⟨m₂, n₂, rfl⟩ := h₂
    apply h

end Module

variable [Module R P] [Module R Q]

section UniversalProperty

variable {M N}
variable (f : M →ₗ[R] N →ₗ[R] P)
variable (f' : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂)

/-- Auxiliary function to constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def liftAux : M ⊗[R] N →+ P₂ :=
  liftAddHom (LinearMap.toAddMonoidHom'.comp <| f'.toAddMonoidHom)
    fun r m n => by dsimp; rw [LinearMap.map_smulₛₗ₂, map_smulₛₗ]

theorem liftAux_tmul (m n) : liftAux f' (m ⊗ₜ n) = f' m n :=
  rfl

variable {f f'}

@[simp]
theorem liftAux.smulₛₗ (r : R) (x) : liftAux f' (r • x) = σ₁₂ r • liftAux f' x :=
  TensorProduct.induction_on x (smul_zero _).symm
    (fun p q => by simp_rw [← tmul_smul, liftAux_tmul, (f' p).map_smulₛₗ])
    fun p q ih1 ih2 => by simp_rw [smul_add, (liftAux f').map_add, ih1, ih2, smul_add]

theorem liftAux.smul (r : R) (x) : liftAux f (r • x) = r • liftAux f x :=
  liftAux.smulₛₗ _ _

variable (f') in
/-- Constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P` with the property that
its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`.

This works for semilinear maps. -/
def lift : M ⊗[R] N →ₛₗ[σ₁₂] P₂ :=
  { liftAux f' with map_smul' := liftAux.smulₛₗ }

@[simp]
theorem lift.tmul (x y) : lift f' (x ⊗ₜ y) = f' x y :=
  rfl

@[simp]
theorem lift.tmul' (x y) : (lift f').1 (x ⊗ₜ y) = f' x y :=
  rfl

theorem ext' {g h : M ⊗[R] N →ₛₗ[σ₁₂] P₂} (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
  LinearMap.ext fun z =>
    TensorProduct.induction_on z (by simp_rw [map_zero]) H fun x y ihx ihy => by
      rw [g.map_add, h.map_add, ihx, ihy]

theorem lift.unique {g : M ⊗[R] N →ₛₗ[σ₁₂] P₂} (H : ∀ x y, g (x ⊗ₜ y) = f' x y) : g = lift f' :=
  ext' fun m n => by rw [H, lift.tmul]

theorem lift_mk : lift (mk R M N) = LinearMap.id :=
  Eq.symm <| lift.unique fun _ _ => rfl

theorem lift_compr₂ₛₗ [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (h : P₂ →ₛₗ[σ₂₃] P₃) :
    lift (f'.compr₂ₛₗ h) = h.comp (lift f') :=
  Eq.symm <| lift.unique fun _ _ => by simp

theorem lift_compr₂ (g : P →ₗ[R] Q) : lift (f.compr₂ g) = g.comp (lift f) :=
  Eq.symm <| lift.unique fun _ _ => by simp

theorem lift_mk_compr₂ₛₗ (g : M ⊗ N →ₛₗ[σ₁₂] P₂) : lift ((mk R M N).compr₂ₛₗ g) = g := by
  rw [lift_compr₂ₛₗ g, lift_mk, LinearMap.comp_id]

theorem lift_mk_compr₂ (f : M ⊗ N →ₗ[R] P) : lift ((mk R M N).compr₂ f) = f := by
  rw [lift_compr₂ f, lift_mk, LinearMap.comp_id]

/-- This used to be an `@[ext]` lemma, but it fails very slowly when the `ext` tactic tries to apply
it in some cases, notably when one wants to show equality of two linear maps. The `@[ext]`
attribute is now added locally where it is needed. Using this as the `@[ext]` lemma instead of
`TensorProduct.ext'` allows `ext` to apply lemmas specific to `M →ₗ _` and `N →ₗ _`.

See note [partially-applied ext lemmas]. -/
theorem ext {g h : M ⊗ N →ₛₗ[σ₁₂] P₂} (H : (mk R M N).compr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) :
    g = h := by
  rw [← lift_mk_compr₂ₛₗ g, H, lift_mk_compr₂ₛₗ]

attribute [local ext high] ext

variable (M N P₂ σ₁₂) in
/-- Linearly constructing a semilinear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def uncurry : (M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) →ₗ[R₂] M ⊗[R] N →ₛₗ[σ₁₂] P₂ where
  toFun := lift
  map_add' f g := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp]
theorem uncurry_apply (f : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) (m : M) (n : N) :
    uncurry σ₁₂ M N P₂ f (m ⊗ₜ n) = f m n := rfl

variable (M N P₂ σ₁₂)

/-- A linear equivalence constructing a semilinear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def lift.equiv : (M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) ≃ₗ[R₂] M ⊗[R] N →ₛₗ[σ₁₂] P₂ :=
  { uncurry σ₁₂ M N P₂ with
    invFun := fun f => (mk R M N).compr₂ₛₗ f }

@[simp]
theorem lift.equiv_apply (f : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) (m : M) (n : N) :
    lift.equiv σ₁₂ M N P₂ f (m ⊗ₜ n) = f m n :=
  uncurry_apply f m n

@[simp]
theorem lift.equiv_symm_apply (f : M ⊗[R] N →ₛₗ[σ₁₂] P₂) (m : M) (n : N) :
    (lift.equiv σ₁₂ M N P₂).symm f m n = f (m ⊗ₜ n) :=
  rfl

/-- Given a semilinear map `M ⊗ N → P`, compose it with the canonical bilinear map
`M → N → M ⊗ N` to form a bilinear map `M → N → P`. -/
def lcurry : (M ⊗[R] N →ₛₗ[σ₁₂] P₂) →ₗ[R₂] M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂ :=
  (lift.equiv σ₁₂ M N P₂).symm

variable {M N P₂ σ₁₂}

@[simp]
theorem lcurry_apply (f : M ⊗[R] N →ₛₗ[σ₁₂] P₂) (m : M) (n : N) :
    lcurry σ₁₂ M N P₂ f m n = f (m ⊗ₜ n) :=
  rfl

/-- Given a semilinear map `M ⊗ N → P`, compose it with the canonical bilinear map
`M → N → M ⊗ N` to form a bilinear map `M → N → P`. -/
def curry (f : M ⊗[R] N →ₛₗ[σ₁₂] P₂) : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂ :=
  lcurry σ₁₂ M N P₂ f

@[simp]
theorem curry_apply (f : M ⊗[R] N →ₛₗ[σ₁₂] P₂) (m : M) (n : N) : curry f m n = f (m ⊗ₜ n) :=
  rfl

theorem curry_injective :
    Function.Injective (curry : (M ⊗[R] N →ₛₗ[σ₁₂] P₂) → M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) :=
  fun _ _ H => ext H

theorem ext_threefold {g h : M ⊗[R] N ⊗[R] P →ₛₗ[σ₁₂] P₂}
    (H : ∀ x y z, g (x ⊗ₜ y ⊗ₜ z) = h (x ⊗ₜ y ⊗ₜ z)) : g = h := by
  ext x y z
  exact H x y z

theorem ext_threefold' {g h : M ⊗[R] (N ⊗[R] P) →ₛₗ[σ₁₂] P₂}
    (H : ∀ x y z, g (x ⊗ₜ (y ⊗ₜ z)) = h (x ⊗ₜ (y ⊗ₜ z))) : g = h := by
  ext x y z
  exact H x y z

-- We'll need this one for checking the pentagon identity!
theorem ext_fourfold {g h : M ⊗[R] N ⊗[R] P ⊗[R] Q →ₛₗ[σ₁₂] P₂}
    (H : ∀ w x y z, g (w ⊗ₜ x ⊗ₜ y ⊗ₜ z) = h (w ⊗ₜ x ⊗ₜ y ⊗ₜ z)) : g = h := by
  ext w x y z
  exact H w x y z

/-- Two semilinear maps `(M ⊗ N) ⊗ (P ⊗ Q) → P₂` which agree on all elements of the
form `(m ⊗ₜ n) ⊗ₜ (p ⊗ₜ q)` are equal. -/
theorem ext_fourfold' {φ ψ : M ⊗[R] N ⊗[R] (P ⊗[R] Q) →ₛₗ[σ₁₂] P₂}
    (H : ∀ w x y z, φ (w ⊗ₜ x ⊗ₜ (y ⊗ₜ z)) = ψ (w ⊗ₜ x ⊗ₜ (y ⊗ₜ z))) : φ = ψ := by
  ext m n p q
  exact H m n p q

/-- Two semilinear maps `M ⊗ (N ⊗ P) ⊗ Q → P₂` which agree on all elements of the
form `m ⊗ₜ (n ⊗ₜ p) ⊗ₜ q` are equal. -/
theorem ext_fourfold'' {φ ψ : M ⊗[R] (N ⊗[R] P) ⊗[R] Q →ₛₗ[σ₁₂] P₂}
    (H : ∀ w x y z, φ (w ⊗ₜ (x ⊗ₜ y) ⊗ₜ z) = ψ (w ⊗ₜ (x ⊗ₜ y) ⊗ₜ z)) : φ = ψ := by
  ext m n p q
  exact H m n p q

end UniversalProperty

variable {M N}
section

variable (R M N)

/-- The tensor product of modules is commutative, up to linear equivalence. -/
protected def comm : M ⊗[R] N ≃ₗ[R] N ⊗[R] M :=
  LinearEquiv.ofLinear (lift (mk R N M).flip) (lift (mk R M N).flip) (ext' fun _ _ => rfl)
    (ext' fun _ _ => rfl)

@[simp]
theorem comm_tmul (m : M) (n : N) : (TensorProduct.comm R M N) (m ⊗ₜ n) = n ⊗ₜ m :=
  rfl

@[simp]
lemma comm_symm : (TensorProduct.comm R M N).symm = TensorProduct.comm R N M := rfl

theorem comm_symm_tmul (m : M) (n : N) : (TensorProduct.comm R M N).symm (n ⊗ₜ m) = m ⊗ₜ n :=
  rfl

-- Why is the `toLinearMap` necessary ? And why is this slow ?
lemma lift_comp_comm_eq (f : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) :
    lift f ∘ₛₗ (TensorProduct.comm R N M).toLinearMap = lift f.flip :=
  ext rfl

attribute [local ext high] ext in
@[simp] lemma comm_trans_comm :
    TensorProduct.comm R N M ≪≫ₗ TensorProduct.comm R M N = .refl _ _ := by
  apply LinearEquiv.toLinearMap_injective; ext; rfl

lemma comm_comp_comm :
    (TensorProduct.comm R N M).toLinearMap ∘ₗ (TensorProduct.comm R M N).toLinearMap = .id := by
  simp

@[simp]
lemma comm_comp_comm_assoc (f : P →ₗ[R] M ⊗[R] N) :
    (TensorProduct.comm R N M).toLinearMap ∘ₗ (TensorProduct.comm R M N).toLinearMap ∘ₗ f = f := by
  rw [← LinearMap.comp_assoc, comm_comp_comm, LinearMap.id_comp]

end

section CompatibleSMul

variable (R A M N) [CommSemiring A] [Module A M] [Module A N] [SMulCommClass R A M]
  [CompatibleSMul R A M N]

/-- If M and N are both R- and A-modules and their actions on them commute,
and if the A-action on `M ⊗[R] N` can switch between the two factors, then there is a
canonical A-linear map from `M ⊗[A] N` to `M ⊗[R] N`. -/
def mapOfCompatibleSMul : M ⊗[A] N →ₗ[A] M ⊗[R] N :=
  lift
  { toFun := fun m ↦
    { __ := mk R M N m
      map_smul' := fun _ _ ↦ (smul_tmul _ _ _).symm }
    map_add' := fun _ _ ↦ LinearMap.ext <| by simp
    map_smul' := fun _ _ ↦ rfl }

@[simp] theorem mapOfCompatibleSMul_tmul (m n) : mapOfCompatibleSMul R A M N (m ⊗ₜ n) = m ⊗ₜ n :=
  rfl

theorem mapOfCompatibleSMul_surjective : Function.Surjective (mapOfCompatibleSMul R A M N) :=
  fun x ↦ x.induction_on (⟨0, map_zero _⟩) (fun m n ↦ ⟨_, mapOfCompatibleSMul_tmul ..⟩)
    fun _ _ ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x + y, by simpa using congr($hx + $hy)⟩

attribute [local instance] SMulCommClass.symm

/-- `mapOfCompatibleSMul R A M N` is also R-linear. -/
def mapOfCompatibleSMul' : M ⊗[A] N →ₗ[R] M ⊗[R] N where
  __ := mapOfCompatibleSMul R A M N
  map_smul' _ x := x.induction_on (map_zero _) (fun _ _ ↦ by simp [smul_tmul'])
    fun _ _ h h' ↦ by simpa using congr($h + $h')

/-- If the R- and A-actions on M and N satisfy `CompatibleSMul` both ways,
then `M ⊗[A] N` is canonically isomorphic to `M ⊗[R] N`. -/
def equivOfCompatibleSMul [CompatibleSMul A R M N] : M ⊗[A] N ≃ₗ[A] M ⊗[R] N where
  __ := mapOfCompatibleSMul R A M N
  invFun := mapOfCompatibleSMul A R M N
  left_inv x := x.induction_on (map_zero _) (fun _ _ ↦ rfl)
    fun _ _ h h' ↦ by simpa using congr($h + $h')
  right_inv x := x.induction_on (map_zero _) (fun _ _ ↦ rfl)
    fun _ _ h h' ↦ by simpa using congr($h + $h')

end CompatibleSMul

end TensorProduct

end Semiring

section Ring

variable {R : Type*} [CommSemiring R]
variable {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}
variable [AddCommGroup M] [AddCommMonoid N] [AddCommGroup P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]

namespace TensorProduct

open TensorProduct

open LinearMap

variable (R) in
/-- Auxiliary function to defining negation multiplication on tensor product. -/
def Neg.aux : M ⊗[R] N →ₗ[R] M ⊗[R] N :=
  lift <| (mk R M N).comp (-LinearMap.id)

instance neg : Neg (M ⊗[R] N) where
  neg := Neg.aux R

protected theorem neg_add_cancel (x : M ⊗[R] N) : -x + x = 0 :=
  x.induction_on
    (by rw [add_zero]; apply (Neg.aux R).map_zero)
    (fun x y => by convert (add_tmul (R := R) (-x) x y).symm; rw [neg_add_cancel, zero_tmul])
    fun x y hx hy => by
    suffices -x + x + (-y + y) = 0 by
      rw [← this]
      unfold Neg.neg neg
      simp only
      rw [map_add]
      abel
    rw [hx, hy, add_zero]

instance addCommGroup : AddCommGroup (M ⊗[R] N) :=
  { TensorProduct.addCommMonoid with
    neg_add_cancel := fun x => TensorProduct.neg_add_cancel x
    zsmul := (· • ·)
    zsmul_zero' := by simp
    zsmul_succ' := by simp [add_comm, TensorProduct.add_smul]
    zsmul_neg' := fun n x => by
      change (-n.succ : ℤ) • x = -(((n : ℤ) + 1) • x)
      rw [← zero_add (_ • x), ← TensorProduct.neg_add_cancel ((n.succ : ℤ) • x), add_assoc,
        ← add_smul, ← sub_eq_add_neg, sub_self, zero_smul, add_zero]
      rfl }

theorem neg_tmul (m : M) (n : N) : (-m) ⊗ₜ n = -m ⊗ₜ[R] n :=
  rfl

theorem tmul_neg (m : M) (p : P) : m ⊗ₜ (-p) = -m ⊗ₜ[R] p :=
  (mk R M P _).map_neg _

theorem tmul_sub (m : M) (p₁ p₂ : P) : m ⊗ₜ (p₁ - p₂) = m ⊗ₜ[R] p₁ - m ⊗ₜ[R] p₂ :=
  (mk R M P _).map_sub _ _

theorem sub_tmul (m₁ m₂ : M) (n : N) : (m₁ - m₂) ⊗ₜ n = m₁ ⊗ₜ[R] n - m₂ ⊗ₜ[R] n :=
  (mk R M N).map_sub₂ _ _ _

/-- While the tensor product will automatically inherit a ℤ-module structure from
`AddCommGroup.toIntModule`, that structure won't be compatible with lemmas like `tmul_smul` unless
we use a `ℤ-Module` instance provided by `TensorProduct.left_module`.

When `R` is a `Ring` we get the required `TensorProduct.compatible_smul` instance through
`IsScalarTower`, but when it is only a `Semiring` we need to build it from scratch.
The instance diamond in `compatible_smul` doesn't matter because it's in `Prop`.
-/
instance CompatibleSMul.int : CompatibleSMul R ℤ M P :=
  ⟨fun r m p =>
    Int.induction_on r (by simp) (fun r ih => by simpa [add_smul, tmul_add, add_tmul] using ih)
      fun r ih => by simpa [sub_smul, tmul_sub, sub_tmul] using ih⟩

instance CompatibleSMul.unit {S} [Monoid S] [DistribMulAction S M] [DistribMulAction S N]
    [CompatibleSMul R S M N] : CompatibleSMul R Sˣ M N :=
  ⟨fun s m n => CompatibleSMul.smul_tmul (s : S) m n⟩

end TensorProduct

end Ring
