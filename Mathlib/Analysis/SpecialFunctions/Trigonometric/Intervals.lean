import Mathlib

set_option autoImplicit true

/-!
# Examples of building interval propagators.
-/

/--
A class for types in which we can do interval arithmetic,
by virtue of order comparisons with `ℚ` (later `Dyadic`).
-/
class IntervalArithmetic (α : Type) [LE α] where
  upperBound : α → ℚ → Prop
  lowerBound : ℚ → α → Prop
  trans_upperBound : ∀ x y z, x ≤ y → upperBound y z → upperBound x z := by grind
  upperBound_trans : ∀ x y z, upperBound x y → y ≤ z → upperBound x z := by grind
  trans_lowerBound : ∀ x y z, x ≤ y → lowerBound y z → lowerBound x z := by grind
  lowerBound_trans : ∀ x y z, lowerBound x y → y ≤ z → lowerBound x z := by grind

infix:50 " ≤ℚ " => IntervalArithmetic.upperBound
infix:50 " ℚ≤ " => IntervalArithmetic.lowerBound

instance : IntervalArithmetic Nat where
  upperBound x y := (x : Rat) ≤ y
  lowerBound x y := x ≤ (y : Rat)
  trans_upperBound x y z h₁ h₂ := by qify at h₁; grind
  lowerBound_trans x y z h₁ h₂ := by qify at h₂; grind

@[simp, grind =]
theorem Nat.IntervalArithmetic.upperBound (x : Nat) (y : Rat) : x ≤ℚ y ↔ (x : Rat) ≤ y := Iff.rfl
@[simp, grind =]
theorem Nat.IntervalArithmetic.lowerBound (x : Rat) (y : Nat) : x ℚ≤ y ↔ x ≤ (y : Nat) := Iff.rfl

instance : IntervalArithmetic Int where
  upperBound x y := (x : Rat) ≤ y
  lowerBound x y := x ≤ (y : Rat)
  trans_upperBound x y z h₁ h₂ := by qify at h₁; grind
  lowerBound_trans x y z h₁ h₂ := by qify at h₂; grind

@[simp, grind =]
theorem Int.IntervalArithmetic.upperBound (x : Int) (y : Rat) : x ≤ℚ y ↔ (x : Rat) ≤ y := Iff.rfl
@[simp, grind =]
theorem Int.IntervalArithmetic.lowerBound (x : Rat) (y : Int) : x ℚ≤ y ↔ x ≤ (y : Int) := Iff.rfl

-- This instance will live in Mathlib
instance : IntervalArithmetic ℝ where
  upperBound x y := x ≤ (y : ℝ)
  lowerBound y x := (y : ℝ) ≤ x
  upperBound_trans x y z h₁ h₂ := by rify at h₂; grind
  trans_lowerBound x y z h₁ h₂ := by rify at h₁; grind

@[simp, grind =]
theorem Real.IntervalArithmetic.upperBound (x : ℝ) (y : Rat) : x ≤ℚ y ↔ x ≤ (y : ℝ) := Iff.rfl
@[simp, grind =]
theorem Real.IntervalArithmetic.lowerBound (x : Rat) (y : ℝ) : x ℚ≤ y ↔ (x : ℝ) ≤ y := Iff.rfl

/--
A machine for propagating intervals through a function.
(The interface here will certainly change.)

The propagator is only required to propagate subintervals of the declared `Set.Icc a b`.

* `forward q x y h` must produce a pair of rationals `(r, s)` such that for `z : ℝ`
  if `z ∈ Set.Icc x y` then `f x ∈ Set.Icc r s`

The parameter `q` is a "quality" parameter (smaller is better),
which is used to control the effort expended in producing a tight interval.
No guarantees are required regarding the dependence on `q`,
but we suggest that where possible the additional error introduced should be bounded by `q`.
-/
structure IntervalPropagator
    {α β : Type} [LE α] [LE β] [IntervalArithmetic α] [IntervalArithmetic β]
    (f : α → β) (a b : ℚ) where
  forward (q : ℚ) (x : ℚ) (y : ℚ) (h : Set.Icc x y ⊆ Set.Icc a b) : ℚ × ℚ
  mem (q : ℚ) (x : ℚ) (y : ℚ) (h : Set.Icc x y ⊆ Set.Icc a b) (z : α) (m : x ℚ≤ z ∧ z ≤ℚ y) :
    let (r, s) := forward q x y h
    r ℚ≤ f z ∧ f z ≤ℚ s

/-!
Notes:
* There'll be an internal version of this that uses `Dyadic` rather than `ℚ`,
  but we can automatically build one from the other.
* The machinery that uses this will not know anything about `ℝ`, which lives in Mathlib.
  Instead, we will have a typeclass for "has order comparisons with `Dyadic`",
  which Lean will provide for built in numeric types and Mathlib will provide for `ℝ`.
* There will also be fancier versions that
  * allow for multiple arguments
  * can maintain state for subsequent calls at higher quality
  * can give suggestions about how to best split the input interval
-/

/-!
We'll also have a user level gadget that says:
if you have an interval that doesn't lie inside `Set.Icc (-1) 1`
that you're trying to propagate through `sin`,
add the identity `sin x = 3 * sin (x / 3) - 4 * (sin (x / 3)) ^ 3` instead.
This has the effect of shrinking the interval by a factor of 3,
at the expense of having to push the resulting estimate through the `3 * y - 4 * y^3` function.
Recursing, we can shrink into the interval `Set.Icc (-1) 1`.
-/

/-!
We now give an example of a forward propagator for `sin` using Taylor polynomials.
-/

namespace Real.sin

open Nat

/--
The `n`-th derivative of `sin` at `0` as a rational number.

We use this to build rational approximations to `sin`.
-/
def iteratedDerivAtZero : ℕ → ℚ
| 0 => 0
| 1 => 1
| n + 2 => - iteratedDerivAtZero n

/-- The `n`-th Taylor polynomial of `sin` at `0`, as a function `ℚ → ℚ`. -/
def ratApprox (n : ℕ) (x : ℚ) : ℚ :=
  ∑ i ∈ Finset.range (n + 1), (iteratedDerivAtZero i * x ^ i) / i !

/--
The error bound for the `n`-th Taylor polynomial of `sin` at `0`.
-/
def ratErrorBound (n : ℕ) (x : ℚ) : ℚ :=
  |x| ^ (n + 1) / (n + 1)!

theorem iteratedDerivAtZero_eq (n : ℕ) :
    iteratedDerivAtZero n = iteratedDeriv n sin 0 :=
  match n with | 0 | 1 | n + 2 => by simp [iteratedDerivAtZero, iteratedDerivAtZero_eq]

theorem ratApprox_coe_eq {x : ℚ} {n : ℕ} (h : 0 < x) :
    (ratApprox n x : ℝ) = taylorWithinEval sin n (Set.Icc 0 ↑x) 0 ↑x := by
  have : (0 : ℝ) ∈ Set.Icc 0 (x : ℝ) := by simp; grind
  simp_all [taylorWithinEval, taylorWithin, taylorCoeffWithin, ratApprox, iteratedDerivAtZero_eq]
  grind

theorem ratApprox_bound_aux (n : ℕ) {x : ℚ} (h : 0 < x) :
    |sin x - ratApprox n x| ≤ ratErrorBound n x := by
  have h' : 0 < (x : ℝ) := by rify at h; exact h
  have w := taylor_mean_remainder_lagrange (f := sin) (n := n) h' ?_ ?_
  · obtain ⟨x', m, w⟩ := w
    rw [ratApprox_coe_eq h, w]
    simp? [abs_div, ratErrorBound] says
      simp only [sub_zero, abs_div, abs_mul, abs_pow, abs_cast, ratErrorBound, Rat.cast_div,
        Rat.cast_pow, Rat.cast_abs, Rat.cast_natCast, ge_iff_le]
    gcongr
    rw [iteratedDerivWithin_sin_Icc _ h' (by grind)]
    have t₁ := abs_iteratedDeriv_sin_le_one (n + 1) x'
    have t₂ : 0 ≤ |(x : ℝ)| ^ (n + 1) := by positivity
    simpa using mul_le_mul_of_nonneg_right t₁ t₂
  · fun_prop
  · apply DifferentiableOn.congr (f := iteratedDeriv n Real.sin)
    · exact Differentiable.differentiableOn (differentiable_iteratedDeriv_sin n)
    · intro x' hx'
      simp_all only [Rat.cast_pos, Set.mem_Ioo]
      rw [iteratedDerivWithin_sin_Icc] <;> grind

@[local simp]
theorem ratApprox_zero {n : ℕ} :
    ratApprox n 0 = 0 := by
  simp [ratApprox, Finset.sum_range_succ', iteratedDerivAtZero]

private theorem iteratedDerivAtZero_mul_neg_one_pow {n : ℕ} :
    iteratedDerivAtZero n * (-1) ^ n = - iteratedDerivAtZero n :=
  match n with
  | 0 => by simp [iteratedDerivAtZero]
  | 1 => by simp [iteratedDerivAtZero]
  | n + 2 => by simp [iteratedDerivAtZero, pow_add, iteratedDerivAtZero_mul_neg_one_pow]

private theorem ratApprox_neg {n : ℕ} {x : ℚ} :
    ratApprox n (-x) = -ratApprox n x := by
  simp [ratApprox, neg_pow x, ← mul_assoc, iteratedDerivAtZero_mul_neg_one_pow, neg_div]

private theorem ratErrorBound_nonneg {n : ℕ} {x : ℚ} :
    0 ≤ ratErrorBound n x := by
  simp [ratErrorBound]
  positivity

private theorem ratErrorBound_neg {n : ℕ} {x : ℚ} :
    ratErrorBound n (-x) = ratErrorBound n x := by
  simp [ratErrorBound]

theorem ratApprox_bound (n : ℕ) (x : ℚ) :
    |sin x - ratApprox n x| ≤ ratErrorBound n x := by
  obtain neg | rfl | pos := lt_trichotomy x 0
  · rw [← neg_neg x]
    rw [Rat.cast_neg, sin_neg, Rat.cast_neg, ratApprox_neg, sub_eq_add_neg, ← neg_add, abs_neg,
      Rat.cast_neg, ← sub_eq_add_neg, ratErrorBound_neg, ← Rat.cast_neg]
    exact ratApprox_bound_aux n (by grind)
  · simpa using ratErrorBound_nonneg
  · exact ratApprox_bound_aux n pos

/--
A lower bound on `sin x` for `x : ℚ` using the `n`-th Taylor polynomial.
-/
def lowerBound (n : ℕ) (x : ℚ) : ℚ :=
  ratApprox n x - ratErrorBound n x

/--
An upper bound on `sin x` for `x : ℚ` using the `n`-th Taylor polynomial.
-/
def upperBound (n : ℕ) (x : ℚ) : ℚ :=
  ratApprox n x + ratErrorBound n x

/--
The interval `[lowerBound n x, upperBound n y]` containing `sin x` for `x : ℝ` contained in `[x, y]`
using the `n`-th Taylor polynomial. This is only valid when `sin` is monotone on `[x, y]`.
-/
def interval (n : ℕ) (x y : ℚ) : ℚ × ℚ :=
  (lowerBound n x, upperBound n y)

example : lowerBound 2 (-1/2) = -25/48 := by decide +kernel
example : upperBound 3 (1/3) = 637/1944 := by decide +kernel

theorem mem_interval (n : ℕ) {x y : ℚ} (wx : -1 ≤ x) (wy : y ≤ 1) {z : ℝ} (h : x ≤ z ∧ z ≤ y) :
    lowerBound n x ≤ sin z ∧ sin z ≤ upperBound n y := by
  have m : MonotoneOn sin (Set.Icc x y) := by
    apply strictMonoOn_sin.monotoneOn.mono
    refine (Set.Icc_subset_Icc_iff ?_).mpr ?_
    · grind
    · have := Real.pi_gt_three
      rify at wx wy
      constructor <;> linarith
  have mx := @m x (by grind) z (by grind) (by grind)
  have my := @m z (by grind) y (by grind) (by grind)
  have rx := ratApprox_bound n x
  have ry := ratApprox_bound n y
  unfold lowerBound
  unfold upperBound
  grind [abs_le, Rat.cast_sub, Rat.cast_add]

/--
An interval propagator for `sin` on the interval `Set.Icc (-1) 1`.

If we use the n-th Taylor polynomial,
the introduced error is bounded by `1 / (n + 1)! ≤ 1 / 2^n`.
So if we take `n = (q⁻¹).ceil.toNat.log2`, the error will be bounded by `q`.
(But there is no need to formalize this.)
One could do better (i.e. get away with a smaller `n`) by bounding the factorial more tightly,
or using the input interval, which may be closer to zero.
-/
def propagator : IntervalPropagator Real.sin (-1) 1 where
  forward q x y h := Real.sin.interval (q⁻¹).ceil.toNat.log2 x y
  mem q x y h z m :=
    have h := (Set.Icc_subset_Icc_iff (by rify; grind)).mp h
    Real.sin.mem_interval (q⁻¹).ceil.toNat.log2 h.1 h.2 m

end Real.sin


/-!
We can build forward propagators for functions which have rational approximations and a computable
modulus of continuity, but I haven't implemented this yet.

Suppose we have a function $f : {\mathbb R} \to {\mathbb R}$, together with
* a rational approximation $\tilde f : {\mathbb Q} \times {\mathbb Q_{>0}} \to \mathbb Q$ satisfying
  $$|\tilde f(x, \epsilon) - f(x)| < \epsilon$$
* and a (computable) modulus of uniform continuity
  $\mu : {\mathbb Q_{>0}} \to {\mathbb Q_{>0}} \cup \{\infty\}$ satisfying
  $$|x - y| < \mu(\epsilon) \rightarrow |f(x) - f(y)| < \epsilon$$
  for all $x, y ∈ {\mathbb R}$.

Then we can construct a forward propagator for $f$ with quality $\epsilon \in {\mathbb Q}_{>0}$
which takes an input interval $[a, b]$ and produces an output interval by:
* subdividing into $a = a_0 < a_1 < \cdots < a_k = b$ so that $|a_{i+1} - a_i| < 2\mu(\epsilon)$
* let $c = \operatorname{min} \{\tilde{f}(a_i, \epsilon)\}$,
  and $d = \operatorname{max} \{\tilde{f}(a_i, \epsilon)\}$
* returning the interval $[c-2\epsilon, d+2\epsilon]$
* and the proof that if $x \in [a, b]$, then $|x-a_i|< \mu(\epsilon)$ for some $i$,
  so $|f(x)-f(a_i)| < \epsilon$ and hence $|f(x) - \tilde{f}(a_i, \epsilon)| < 2\epsilon$
  and thus $f(x) \in [c-2\epsilon, d+2\epsilon]$

The modulus of continuity may be allowed to depend on the input interval $[a,b]$.

(As an example of a forward propagator maintaining state,
when run on a smaller interval we could refine the previous subdivision
and reuse previously computed values of $\tilde{f}$.)
-/

-- We probably want to be able to specify the domain is an open interval.
noncomputable def Real.inv.propagator : IntervalPropagator (α := ℝ) (·⁻¹) (1/2) 2 where
  forward q x y h := (y⁻¹, x⁻¹)
  mem q x y h z m := by
    rw [Set.Icc_subset_Icc_iff] at h <;> simp at * <;> rify at *
    · constructor <;> apply inv_anti₀ <;> linarith
    linarith

-- This works everywhere: we need WithBot and WithTop to describe the valid interval.
noncomputable def Real.neg.propagator : IntervalPropagator (α := ℝ) (- ·) (-1) 1 where
  forward q x y h := (-y, -x)
  mem q x y h z m := by
    simp at *
    constructor <;> linarith

-- This is not what things will really look like:
-- we'll have variable arity arguments.
structure IntervalPropagator₀
    {α : Type} [LE α] [IntervalArithmetic α] (f : α) where
  forward (q : ℚ) : ℚ × ℚ
  mem (q : ℚ) :
    let (r, s) := forward q
    r ℚ≤ f ∧ f ≤ℚ s

-- TODO: an example of a 0-ary propagator, e.g. approximating `π`.

-- This is not what things will really look like:
-- we'll have variable arity arguments.
structure IntervalPropagator₂
    {α β γ : Type} [LE α] [LE β] [LE γ]
    [IntervalArithmetic α] [IntervalArithmetic β] [IntervalArithmetic γ]
    (f : α → β → γ) (a₁ b₁ a₂ b₂ : ℚ) where
  forward (q : ℚ) (x₁ y₁ x₂ y₂ : ℚ)
    (h₁ : Set.Icc x₁ y₁ ⊆ Set.Icc a₁ b₁) (h₂ : Set.Icc x₂ y₂ ⊆ Set.Icc a₂ b₂) : ℚ × ℚ
  mem (q : ℚ) (x₁ y₁ x₂ y₂ : ℚ)
    (h₁ : Set.Icc x₁ y₁ ⊆ Set.Icc a₁ b₁) (h₂ : Set.Icc x₂ y₂ ⊆ Set.Icc a₂ b₂)
    (z : α × β) (m₁ : x₁ ℚ≤ z.1 ∧ z.1 ≤ℚ y₁) (m₂ : x₂ ℚ≤ z.2 ∧ z.2 ≤ℚ y₂) :
    let (r, s) := forward q x₁ y₁ x₂ y₂ h₁ h₂
    r ℚ≤ f z.1 z.2 ∧ f z.1 z.2 ≤ℚ s

def Real.add.propagator : IntervalPropagator₂ (· + · : ℝ → ℝ → ℝ) (-1) 1 (-1) 1 where
  forward q x₁ y₁ x₂ y₂ h₁ h₂ := (x₁ + x₂, y₁ + y₂)
  mem q x₁ y₁ x₂ y₂ h₁ h₂ z m₁ m₂ := by
    simp at *
    grind

def Real.mul.propagator : IntervalPropagator₂ (· * · : ℝ → ℝ → ℝ) (-1) 1 (-1) 1 where
  forward q x₁ y₁ x₂ y₂ h₁ h₂ :=
    -- It might be nice to use the more uniform
    -- (min (min (x₁ * x₂) (x₁ * y₂)) (min (y₁ * x₂) (y₁ * y₂)),
    --   max (max (x₁ * x₂) (x₁ * y₂)) (max (y₁ * x₂) (y₁ * y₂)))
    -- but I couldn't immediately get the proofs through.
    if 0 ≤ x₁ then
      if 0 ≤ x₂ then (x₁ * x₂, y₁ * y₂)
      else if y₂ ≤ 0 then (y₁ * x₂, x₁ * y₂)
      else (y₁ * x₂, y₁ * y₂)
    else if y₁ ≤ 0 then
      if 0 ≤ x₂ then (x₁ * y₂, y₁ * x₂)
      else if y₂ ≤ 0 then (y₁ * y₂, x₁ * x₂)
      else (x₁ * y₂, x₁ * x₂)
    else
      if 0 ≤ x₂ then (x₁ * y₂, y₁ * y₂)
      else if y₂ ≤ 0 then (y₁ * x₂, x₁ * x₂)
      else (min (x₁ * y₂) (y₁ * x₂), max (x₁ * x₂) (y₁ * y₂))
  mem q x₁ y₁ x₂ y₂ h₁ h₂ z m₁ m₂ := by
    simp at *
    rify at *
    repeat' split
    iterate 8
      constructor <;>
      · simp
        nlinarith
    · simp only [min_def, max_def]
      split_ifs with h₁ h₂ <;>
      · constructor <;> (rify at *; by_cases 0 ≤ z.1 <;> nlinarith)


-- Speculative material about arbitrary arity propagators.

abbrev TypeVector (n : Nat) : Type 1 := Vector Type n

class TypeVector.LE (α : TypeVector n) : Type where
  le : ∀ (i : Nat) (h : i < n), _root_.LE α[i]

attribute [instance] TypeVector.LE.le

class TypeVector.IntervalArithmetic (α : TypeVector n) [TypeVector.LE α] : Type where
  intervalArithmetic : ∀ (i : Nat) (h : i < n), _root_.IntervalArithmetic α[i]

attribute [instance] TypeVector.IntervalArithmetic.intervalArithmetic

instance TypeVector.LE_nil : TypeVector.LE #v[] where
  le i h := by simp at h
instance TypeVector.LE_cons [_root_.LE α] [I : TypeVector.LE (Vector.mk (List.toArray αs) rfl)] :
    TypeVector.LE (Vector.mk (List.toArray (α :: αs)) rfl) where
  le i h :=
    match i with
    | 0 => by
      assumption
    | i + 1 => by
      apply @TypeVector.LE.le _ _ I i
      grind

instance TypeVector.IntervalArithmetic_nil : TypeVector.IntervalArithmetic #v[] where
  intervalArithmetic i h := by simp at h
instance TypeVector.IntervalArithmetic_cons [_root_.LE α] [_root_.IntervalArithmetic α]
    [I : TypeVector.LE (Vector.mk (List.toArray αs) rfl)]
    [I' : TypeVector.IntervalArithmetic (Vector.mk (List.toArray αs) rfl)] :
    TypeVector.IntervalArithmetic (Vector.mk (List.toArray (α :: αs)) rfl) where
  intervalArithmetic i h :=
    match i with
    | 0 => by
      assumption
    | i + 1 => by
      apply @TypeVector.IntervalArithmetic.intervalArithmetic _ _ _ I' i

example : TypeVector.LE #v[ℝ, ℝ, ℝ] := inferInstance
example : TypeVector.IntervalArithmetic #v[ℝ, ℝ, ℝ] := inferInstance

def functionType (args : TypeVector n) (dom : Type) : Type :=
  args.foldr (fun α β => α → β) dom

noncomputable example : functionType #v[ℝ] ℝ := Real.sin
example : functionType #v[ℤ, ℕ] ℤ := Int.pow

def point (types : TypeVector n) : Type :=
  Π (i : Nat) (h : i < n), types[i]

def eval {args : TypeVector n} {dom : Type}
    (f : functionType args dom) (z : point args) : dom :=
  sorry

def subbox (x y : (i : Nat) → i < n → ℚ × ℚ) : Prop :=
    ∀ i h, (y i h).1 ≤ (x i h).1 ∧ (x i h).2 ≤ (y i h).2

def membox {types : TypeVector n} [TypeVector.LE types] [TypeVector.IntervalArithmetic types]
    (z : point types) (box : (i : Nat) → i < n → ℚ × ℚ) : Prop :=
  ∀ (i : Nat) (h : i < n), ((box i h).1 ℚ≤ z i h) ∧ (z i h ≤ℚ (box i h).2)

structure IntervalPropagator'
    {n : Nat}
    (args : TypeVector n) [TypeVector.LE args] [TypeVector.IntervalArithmetic args]
    (dom : Type) [LE dom] [IntervalArithmetic dom]
    (f : functionType args dom) (validBox : (i : Nat) → i < n → ℚ × ℚ) where
  forward (q : ℚ) (box : (i : Nat) → i < n → ℚ × ℚ) (h : subbox box validBox) : ℚ × ℚ
  mem (q : ℚ) (box : (i : Nat) → i < n → ℚ × ℚ) (h : subbox box validBox) (z : point args)
    (m : membox z box) :
    let (r, s) := forward q box h
    (r ℚ≤ eval f z) ∧ (eval f z ≤ℚ s)
