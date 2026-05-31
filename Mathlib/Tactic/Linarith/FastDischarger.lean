/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Tactic.Linarith.Parsing
public import Mathlib.Tactic.Ring.Basic

/-!
# Fast discharger for linarith — prototype

A specialized, `Rat`-only replacement for the `ring1` discharger that proves
`Σ cᵢ * tᵢ = 0` by structural composition of fixed-arity lemmas rather than
polynomial normalization. Gated behind `LinarithConfig.useFastDischarger`.

Ported from the `lp` tactic in
[Soplex/Tactic/LP/Certificate.lean](https://github.com/kim-em/lean-soplex).
The structure mirrors the lp version closely; see that file for the algorithmic
rationale.
-/

public meta section

open Lean Elab Tactic Meta

namespace Mathlib.Tactic.Linarith

/-! ## Structured input. -/

structure FastDischargerInput where
  goalType : Expr
  sm : Expr
  atoms : Array Expr
  monomMap : Map Monom ℕ
  rows : Array (Expr × Linexp × Nat)

abbrev FastDischargerFn := FastDischargerInput → MetaM (Option Expr)

def noFastDischarger : FastDischargerFn := fun _ => return none

end Mathlib.Tactic.Linarith

/-! ## Q type — a kernel-reduction-friendly rational helper.

`Q := { num : Int, den : Nat, den_nz : den ≠ 0 }` keeps coefficients as raw
pairs without in-place gcd normalisation, so closed `Q.add`/`Q.mul`/`Q.neg`
reduce cleanly under the kernel via GMP `Int` arithmetic. `Q.toRat` bridges
to `Rat` via `Rat.normalize` (not `num / den`).

The leaf numeral lemmas take a closed-`Int` cross-multiplication side
condition that is discharged by `Eq.refl` — the kernel verifies the
equality by reducing closed `Int` arithmetic, no `decide` overhead. -/

namespace Mathlib.Tactic.Linarith.FastDischarger

/-- Helper rational with raw fields (no normalisation invariant). -/
structure Q where
  num : Int
  den : Nat := 1
  den_nz : den ≠ 0 := by decide
deriving Repr

instance : Inhabited Q := ⟨{ num := 0 }⟩

namespace Q

/-- `Q.toRat q := Rat.normalize q.num q.den q.den_nz`. -/
@[inline] def toRat (q : Q) : Rat := Rat.normalize q.num q.den q.den_nz

@[inline] def zero : Q := { num := 0, den := 1 }

@[inline] def add (a b : Q) : Q where
  num := a.num * (b.den : Int) + b.num * (a.den : Int)
  den := a.den * b.den
  den_nz := Nat.mul_ne_zero a.den_nz b.den_nz

@[inline] def mul (a b : Q) : Q where
  num := a.num * b.num
  den := a.den * b.den
  den_nz := Nat.mul_ne_zero a.den_nz b.den_nz

@[inline] def neg (a : Q) : Q where
  num := -a.num
  den := a.den
  den_nz := a.den_nz

/-- Cross-multiplication characterisation of `toRat` equality. -/
theorem toRat_eq_of_cross {a b : Q} (h : a.num * (b.den : Int) = b.num * (a.den : Int)) :
    a.toRat = b.toRat :=
  (Rat.normalize_eq_iff a.den_nz b.den_nz).mpr h

theorem toRat_add (a b : Q) : a.toRat + b.toRat = (Q.add a b).toRat :=
  Rat.normalize_add_normalize a.num b.num a.den_nz b.den_nz

theorem toRat_mul (a b : Q) : a.toRat * b.toRat = (Q.mul a b).toRat :=
  Rat.normalize_mul_normalize a.num b.num a.den_nz b.den_nz

theorem toRat_neg (a : Q) : -a.toRat = (Q.neg a).toRat :=
  Rat.neg_normalize a.num a.den a.den_nz

theorem toRat_zero : Q.zero.toRat = 0 :=
  Rat.normalize_zero (d := 1) Nat.one_ne_zero

end Q

/-! ## Sanity tests: kernel reduction of closed Q arithmetic + cross-multiplication.

If these fail to elaborate, the leaf side-condition discharger must switch
from `Eq.refl` to `mkDecideProof`. -/

-- Q.add reduces in the kernel:
example : (Q.add ⟨2, 3, by decide⟩ ⟨5, 7, by decide⟩).num = 29 := rfl
example : (Q.add ⟨2, 3, by decide⟩ ⟨5, 7, by decide⟩).den = 21 := rfl

-- Cross-multiplication on the merged value (qm = ⟨29, 21⟩) holds by rfl:
example : (Q.add ⟨2, 3, by decide⟩ ⟨5, 7, by decide⟩).num * (21 : Int)
        = (29 : Int) * ((Q.add ⟨2, 3, by decide⟩ ⟨5, 7, by decide⟩).den : Int) := rfl

-- Cross-multiplication against an unreduced qm (qm = ⟨4, 3⟩ as the normal form of 2/3 + 4/6 = 24/18):
example : (Q.add ⟨2, 3, by decide⟩ ⟨4, 6, by decide⟩).num * (3 : Int)
        = (4 : Int) * ((Q.add ⟨2, 3, by decide⟩ ⟨4, 6, by decide⟩).den : Int) := rfl

-- Q.mul reduces:
example : (Q.mul ⟨2, 3, by decide⟩ ⟨5, 7, by decide⟩).num = 10 := rfl
example : (Q.mul ⟨2, 3, by decide⟩ ⟨5, 7, by decide⟩).den = 21 := rfl

-- Q.neg reduces:
example : (Q.neg ⟨2, 3, by decide⟩).num = -2 := rfl

/-! ## Walk-step lemmas for the structured proof.

These are the fixed-arity, kernel-cheap lemmas used to compose the proof
term. All proved by `subst; ring1` at module load and then applied via raw
`mkAppN` at runtime — never re-derived per-row.

The canonical right-nested rendering shape is:
  `c₁ * x₁ + (c₂ * x₂ + (... + (cₙ * xₙ + const)))`
where each `cᵢ` is `Q.toRat (some Q)`, atoms are sorted descending by index,
and `const` is `Q.toRat (some Q)`. -/

theorem atom_norm (x : Rat) : x = 1 * x + 0 := by ring1

theorem mul_atom_norm (k x : Rat) : k * x = k * x + 0 := by ring1

theorem neg_atom_norm (x : Rat) : -x = -1 * x + 0 := by ring1

/-- Peel the head off the left when its atom index is greater than the head
of the right (or when the right is just a constant tail). -/
theorem take_left (h ta b res : Rat) (e : ta + b = res) : (h + ta) + b = h + res := by
  subst e; ring1

/-- Peel the head off the right when its atom index is greater than the head
of the left. -/
theorem take_right (a h tb res : Rat) (e : a + tb = res) : a + (h + tb) = h + res := by
  subst e; ring1

/-- Combine matching heads with non-zero coefficient sum. -/
theorem combine (x ta tb res c' c m : Rat)
    (e : ta + tb = res) (hm : c' + c = m) :
    (c' * x + ta) + (c * x + tb) = m * x + res := by
  subst e; subst hm; ring1

/-- Combine matching heads with zero coefficient sum (the atom drops out). -/
theorem combine_zero (x ta tb res c' c : Rat)
    (e : ta + tb = res) (hm : c' + c = 0) :
    (c' * x + ta) + (c * x + tb) = res := by
  subst e
  have h1 : (c' + c) * x = 0 * x := by rw [hm]
  have h2 : c' * x + c * x = 0 := by rw [← Rat.add_mul, h1]; ring1
  rw [show c' * x + ta + (c * x + tb) = (c' * x + c * x) + (ta + tb) from by ring1, h2]
  ring1

/-- Walk-step for scalar multiplication: `k * (c*x + rest) = (k*c)*x + (k*rest)`. -/
theorem smul_cons (k x c m rest rest' : Rat)
    (hm : k * c = m) (e : k * rest = rest') :
    k * (c * x + rest) = m * x + rest' := by
  subst hm; subst e; ring1

/-- Walk-step for negation: `-(c*x + rest) = (-c)*x + (-rest)`. -/
theorem neg_cons (x c m rest rest' : Rat)
    (hm : -c = m) (e : -rest = rest') :
    -(c * x + rest) = m * x + rest' := by
  subst hm; subst e; ring1

theorem add_congr_eq (a A b B : Rat) (ha : a = A) (hb : b = B) : a + b = A + B := by
  subst ha; subst hb; rfl

theorem sub_congr_eq (a A b B : Rat) (ha : a = A) (hb : b = B) : a - b = A - B := by
  subst ha; subst hb; rfl

theorem mul_congr_eq_r (k a A : Rat) (e : a = A) : k * a = k * A := by subst e; rfl

theorem neg_congr_eq (a A : Rat) (e : a = A) : -a = -A := by subst e; rfl

theorem sub_to_add_neg (a b : Rat) : a - b = a + (-b) := by ring1

/-- Right-associativity of `+`, the workhorse for converting left-folded sums
to right-nested form. -/
theorem reassoc_step (a b c : Rat) : (a + b) + c = a + (b + c) := add_assoc a b c

/-- Scalar mul of a constant tail (`k * r = m` if both reduce to the same `Q`). -/
theorem smul_const (k r m : Rat) (h : k * r = m) : k * r = m := h

/-- Negation of a constant (`-r = m` if both reduce to the same `Q`). -/
theorem neg_const (r m : Rat) (h : -r = m) : -r = m := h

/-! ## Canonical linear form sorted DESCENDING by atom index. -/

/-- A canonical linear form over `Q`-valued coefficients. `coeffs` is sorted
**descending** by atom index (to match lp's convention); `const` is the
standalone constant term. The represented term is
`coeffs[0] * atom₀ + (coeffs[1] * atom₁ + (… + (coeffs[n-1] * atomₙ₋₁ + const)))`. -/
structure LinForm where
  coeffs : Array (Nat × Q)
  const  : Q
deriving Inhabited

namespace LinForm

def zero : LinForm := { coeffs := #[], const := Q.zero }

/-- Scale by a `Q`. If `k = 0` the result is `zero`. -/
def smul (k : Q) (L : LinForm) : LinForm :=
  if k.num == 0 then zero
  else { coeffs := L.coeffs.map (fun (i, c) => (i, Q.mul k c)),
         const := Q.mul k L.const }

/-- Negate a `LinForm`. -/
def neg (L : LinForm) : LinForm :=
  { coeffs := L.coeffs.map (fun (i, c) => (i, Q.neg c)),
    const := Q.neg L.const }

/-- Merge two `LinForm`s, **assuming both `coeffs` arrays are sorted descending**.
Coefficient cancellation removes the entry. -/
partial def add (L₁ L₂ : LinForm) : LinForm := Id.run do
  let mut out : Array (Nat × Q) := Array.mkEmpty (L₁.coeffs.size + L₂.coeffs.size)
  let mut i := 0
  let mut j := 0
  while i < L₁.coeffs.size && j < L₂.coeffs.size do
    let (a, c) := L₁.coeffs[i]!
    let (b, d) := L₂.coeffs[j]!
    if a > b then
      out := out.push (a, c); i := i + 1
    else if b > a then
      out := out.push (b, d); j := j + 1
    else
      let s := Q.add c d
      -- Drop the entry if the merged numerator is zero (equivalent to s = 0).
      if s.num != 0 then out := out.push (a, s)
      i := i + 1; j := j + 1
  while i < L₁.coeffs.size do
    out := out.push L₁.coeffs[i]!; i := i + 1
  while j < L₂.coeffs.size do
    out := out.push L₂.coeffs[j]!; j := j + 1
  return { coeffs := out, const := Q.add L₁.const L₂.const }

end LinForm

/-! ## Cached Expr-construction helpers. -/

/-- `Q.toRat (Q.mk num den den_nz)`-headed Rat literal, with the integer
denominator path using a cached `Nat.one_ne_zero` proof. -/
def mkQLit (r : Q) : MetaM Expr := do
  let numE : Expr := match r.num with
    | .ofNat k => mkApp (mkConst ``Int.ofNat) (mkNatLit k)
    | .negSucc k => mkApp (mkConst ``Int.negSucc) (mkNatLit k)
  let denE : Expr := mkNatLit r.den
  let denNeProof ←
    if r.den == 1 then
      pure (mkConst ``Nat.one_ne_zero)
    else
      let denNeType : Expr := mkApp3 (mkConst ``Ne [Level.succ Level.zero])
        (mkConst ``Nat) denE (mkNatLit 0)
      mkDecideProof denNeType
  return mkApp3 (mkConst ``Q.mk) numE denE denNeProof

/-- `Q.toRat` applied to a `Q` payload. -/
def mkRatLit (r : Q) : MetaM Expr := do
  return mkApp (mkConst ``Q.toRat) (← mkQLit r)

/-- Cached partially-applied `HAdd.hAdd Rat Rat Rat _`, used via `mkApp2`. -/
def addRatFn : Expr :=
  let inst := mkApp2 (mkConst ``instHAdd [Level.zero])
    (mkConst ``Rat) (mkConst ``Rat.instAdd)
  mkApp4 (mkConst ``HAdd.hAdd [Level.zero, Level.zero, Level.zero])
    (mkConst ``Rat) (mkConst ``Rat) (mkConst ``Rat) inst

/-- Cached partially-applied `HMul.hMul Rat Rat Rat _`, used via `mkApp2`. -/
def mulRatFn : Expr :=
  let inst := mkApp2 (mkConst ``instHMul [Level.zero])
    (mkConst ``Rat) (mkConst ``Rat.instMul)
  mkApp4 (mkConst ``HMul.hMul [Level.zero, Level.zero, Level.zero])
    (mkConst ``Rat) (mkConst ``Rat) (mkConst ``Rat) inst

/-- Cached partially-applied `Neg.neg Rat _`. -/
def negRatFn : Expr :=
  mkApp2 (mkConst ``Neg.neg [Level.zero]) (mkConst ``Rat) (mkConst ``Rat.instNeg)

/-- Build `a + b : Rat` Expr without typeclass synthesis. -/
@[inline] def mkRatAdd (a b : Expr) : Expr := mkApp2 addRatFn a b

/-- Build `a * b : Rat` Expr without typeclass synthesis. -/
@[inline] def mkRatMul (a b : Expr) : Expr := mkApp2 mulRatFn a b

/-- Build `-a : Rat` Expr without typeclass synthesis. -/
@[inline] def mkRatNeg (a : Expr) : Expr := mkApp negRatFn a

/-- The constant `Rat` type Expr, cached for reuse. -/
def ratType : Expr := mkConst ``Rat

/-- Build `Eq.trans` directly via `mkApp` on the `Eq.trans` constant, without
`Lean.Meta.mkEqTrans`'s `isDefEq` middle-term unification. The metaprogram
has constructed the middle term `bE` syntactically, so unification is wasted. -/
@[inline] def mkEqTransFast (α aE bE cE p q : Expr) : Expr :=
  mkApp6 (mkConst ``Eq.trans [Level.succ Level.zero]) α aE bE cE p q

/-- Build `Eq.refl rhs` with the *expected type* `lhs = rhs`, relying on
kernel defeq to verify both sides are reducibly equal. -/
def mkRatEqByDefeq (lhs rhs : Expr) : MetaM Expr := do
  let eq ← mkEq lhs rhs
  mkExpectedTypeHint (← mkEqRefl rhs) eq

/-! ## Render a LinForm to a right-nested Rat Expr. -/

/-- Render a `LinForm` (descending) to the right-nested Expr
`c₁ * a₁ + (c₂ * a₂ + (... + (cₙ * aₙ + const)))`. -/
def render (atoms : Array Expr) (L : LinForm) : MetaM Expr := do
  let mut acc ← mkRatLit L.const
  let n := L.coeffs.size
  for i in [0:n] do
    let idx := n - 1 - i
    let (atomIdx, c) := L.coeffs[idx]!
    let cE ← mkRatLit c
    if h : atomIdx < atoms.size then
      let atomE := atoms[atomIdx]
      let head := mkRatMul cE atomE
      acc := mkRatAdd head acc
    else
      throwError "fast discharger: atom index {atomIdx} out of bounds (have {atoms.size})"
  return acc

/-! ## Atom map for normalizeR lookups. -/

/-- Build a reverse map atom-Expr → linarith atom index. Exact-Expr equality
because the fast discharger sees the same preprocessed terms linarith atomized. -/
def buildAtomMap (atoms : Array Expr) : Std.HashMap Expr Nat := Id.run do
  let mut m : Std.HashMap Expr Nat := {}
  for h : i in [0:atoms.size] do
    if i > 0 then m := m.insert atoms[i] i
  return m

/-! ## Convert linarith's Linexp to a LinForm. -/

/-- Build the reverse `monomMap` once. Maps each Linexp-variable-index to its
unique atom index, but ONLY for monomials of the form `{atom ↦ 1}` (single
atom, exponent 1). Non-linear monomials are omitted, so a lookup miss in the
per-row converter signals a non-linear hypothesis (→ fall back to ring1). -/
def buildLinexpRevMap (monomMap : Map Monom ℕ) : Std.HashMap Nat Nat := Id.run do
  let mut revMap : Std.HashMap Nat Nat := {}
  for (mn, j) in monomMap do
    match mn.toList with
    | [(a, 1)] => revMap := revMap.insert j a
    | _ => pure ()
  return revMap

/-- Convert linarith's `Linexp` (descending by Linexp-variable-index) into a
`LinForm` (descending by *atom* index). Returns `none` if any used monomial
is not a single-atom degree-1 monomial (i.e. the goal is non-linear).

`revMap` should be built once per discharger call via `buildLinexpRevMap`;
do not rebuild per-row. -/
def linexpToLinForm (revMap : Std.HashMap Nat Nat) (le : Linexp) : Option LinForm := Id.run do
  let mut consts : Q := Q.zero
  let mut linears : Array (Nat × Q) := Array.mkEmpty le.length
  for (j, z) in le do
    if j == 0 then
      consts := Q.add consts { num := z, den := 1 }
    else
      match revMap[j]? with
      | none => return none
      | some a => linears := linears.push (a, { num := z, den := 1 })
  let sorted := linears.qsort (fun (a, _) (b, _) => a > b)
  return some { coeffs := sorted, const := consts }

/-! ## Numeral leaf builders: `proveRatlit{Add,Mul,Neg}`.

Given the Q.mk Exprs and Q values for both operands, compute the merged value
in meta, build the side-condition (a closed `Int` cross-multiplication
equality) and discharge it by `Eq.refl`. Return the merged Q, its Q.mk Expr,
and the full lemma application. -/

/-- Build `Eq.refl LHS` typed as `LHS = RHS`, where `LHS = RHS` is verified
by kernel reduction of closed `Int` arithmetic. -/
def mkClosedIntEqRefl (hType : Expr) : MetaM Expr := do
  -- hType : @Eq Int LHS RHS
  let lhs := hType.appFn!.appArg!
  return mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Int) lhs

/-- Produce `ratlit_add qaE qbE qmE proof` where `qmE` is the Q.mk of `qa + qb`
and `proof` verifies `(Q.add qa qb).num * qm.den = qm.num * (Q.add qa qb).den`. -/
def proveRatlitAdd (qaE qbE : Expr) (qaVal qbVal : Q) :
    MetaM (Q × Expr × Expr) := do
  let mVal := Q.add qaVal qbVal
  let qmE ← mkQLit mVal
  -- Build hType: (Q.add qa qb).num * (qm.den : Int) = qm.num * ((Q.add qa qb).den : Int)
  let addAB := mkApp2 (mkConst ``Q.add) qaE qbE
  let numAB := mkApp (mkConst ``Q.num) addAB
  let denAB := mkApp (mkConst ``Q.den) addAB
  let numM := mkApp (mkConst ``Q.num) qmE
  let denM := mkApp (mkConst ``Q.den) qmE
  let intType := mkConst ``Int
  let castDenM := mkApp (mkConst ``Int.ofNat) denM
  let castDenAB := mkApp (mkConst ``Int.ofNat) denAB
  let lhs := mkApp2 (mkApp4 (mkConst ``HMul.hMul [Level.zero, Level.zero, Level.zero])
    intType intType intType
    (mkApp2 (mkConst ``instHMul [Level.zero]) intType (mkConst ``Int.instMul)))
    numAB castDenM
  let rhs := mkApp2 (mkApp4 (mkConst ``HMul.hMul [Level.zero, Level.zero, Level.zero])
    intType intType intType
    (mkApp2 (mkConst ``instHMul [Level.zero]) intType (mkConst ``Int.instMul)))
    numM castDenAB
  let hType := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) intType lhs rhs
  let hProof ← mkClosedIntEqRefl hType
  let crossProof := mkApp3 (mkConst ``Q.toRat_eq_of_cross) addAB qmE hProof
  let addEq := mkApp2 (mkConst ``Q.toRat_add) qaE qbE
  let ratType' : Expr := mkConst ``Rat
  let mid := mkApp (mkConst ``Q.toRat) addAB
  let final := mkApp (mkConst ``Q.toRat) qmE
  let lhsRat := mkRatAdd (mkApp (mkConst ``Q.toRat) qaE) (mkApp (mkConst ``Q.toRat) qbE)
  let fullProof := mkEqTransFast ratType' lhsRat mid final addEq crossProof
  return (mVal, qmE, fullProof)

/-- Similar to `proveRatlitAdd` but for multiplication. -/
def proveRatlitMul (qaE qbE : Expr) (qaVal qbVal : Q) :
    MetaM (Q × Expr × Expr) := do
  let mVal := Q.mul qaVal qbVal
  let qmE ← mkQLit mVal
  let mulAB := mkApp2 (mkConst ``Q.mul) qaE qbE
  let numAB := mkApp (mkConst ``Q.num) mulAB
  let denAB := mkApp (mkConst ``Q.den) mulAB
  let numM := mkApp (mkConst ``Q.num) qmE
  let denM := mkApp (mkConst ``Q.den) qmE
  let intType := mkConst ``Int
  let castDenM := mkApp (mkConst ``Int.ofNat) denM
  let castDenAB := mkApp (mkConst ``Int.ofNat) denAB
  let lhs := mkApp2 (mkApp4 (mkConst ``HMul.hMul [Level.zero, Level.zero, Level.zero])
    intType intType intType
    (mkApp2 (mkConst ``instHMul [Level.zero]) intType (mkConst ``Int.instMul)))
    numAB castDenM
  let rhs := mkApp2 (mkApp4 (mkConst ``HMul.hMul [Level.zero, Level.zero, Level.zero])
    intType intType intType
    (mkApp2 (mkConst ``instHMul [Level.zero]) intType (mkConst ``Int.instMul)))
    numM castDenAB
  let hType := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) intType lhs rhs
  let hProof ← mkClosedIntEqRefl hType
  let crossProof := mkApp3 (mkConst ``Q.toRat_eq_of_cross) mulAB qmE hProof
  let mulEq := mkApp2 (mkConst ``Q.toRat_mul) qaE qbE
  let ratType' := mkConst ``Rat
  let lhsRat := mkRatMul (mkApp (mkConst ``Q.toRat) qaE) (mkApp (mkConst ``Q.toRat) qbE)
  let mid := mkApp (mkConst ``Q.toRat) mulAB
  let final := mkApp (mkConst ``Q.toRat) qmE
  let fullProof := mkEqTransFast ratType' lhsRat mid final mulEq crossProof
  return (mVal, qmE, fullProof)

/-- Similar for negation. -/
def proveRatlitNeg (qaE : Expr) (qaVal : Q) : MetaM (Q × Expr × Expr) := do
  let mVal := Q.neg qaVal
  let qmE ← mkQLit mVal
  let negA := mkApp (mkConst ``Q.neg) qaE
  let numA := mkApp (mkConst ``Q.num) negA
  let denA := mkApp (mkConst ``Q.den) negA
  let numM := mkApp (mkConst ``Q.num) qmE
  let denM := mkApp (mkConst ``Q.den) qmE
  let intType := mkConst ``Int
  let castDenM := mkApp (mkConst ``Int.ofNat) denM
  let castDenA := mkApp (mkConst ``Int.ofNat) denA
  let lhs := mkApp2 (mkApp4 (mkConst ``HMul.hMul [Level.zero, Level.zero, Level.zero])
    intType intType intType
    (mkApp2 (mkConst ``instHMul [Level.zero]) intType (mkConst ``Int.instMul)))
    numA castDenM
  let rhs := mkApp2 (mkApp4 (mkConst ``HMul.hMul [Level.zero, Level.zero, Level.zero])
    intType intType intType
    (mkApp2 (mkConst ``instHMul [Level.zero]) intType (mkConst ``Int.instMul)))
    numM castDenA
  let hType := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) intType lhs rhs
  let hProof ← mkClosedIntEqRefl hType
  let crossProof := mkApp3 (mkConst ``Q.toRat_eq_of_cross) negA qmE hProof
  let negEq := mkApp (mkConst ``Q.toRat_neg) qaE
  let ratType' := mkConst ``Rat
  let lhsRat := mkRatNeg (mkApp (mkConst ``Q.toRat) qaE)
  let mid := mkApp (mkConst ``Q.toRat) negA
  let final := mkApp (mkConst ``Q.toRat) qmE
  let fullProof := mkEqTransFast ratType' lhsRat mid final negEq crossProof
  return (mVal, qmE, fullProof)

/-! ## proveMerge: composing `proveRatlitAdd` + walk-step lemmas to merge two
right-nested LinForm renderings.

Both inputs are sorted descending. Walk both arrays head-down. Return
`(L_merged, pf : ⟦L₁⟧ + ⟦L₂⟧ = ⟦L_merged⟧, ⟦L_merged⟧ : Expr)`. -/

/-- Precompute a "spine" for a LinForm: per-atom Q.mk Exprs, per-atom heads
`cₖ * xₖ`, and suffix renderings `suffix[k] = ⟦L[k..n]⟧` (size n+1,
right-nested with the constant at suffix[n]).

This eliminates the O(n²) re-rendering inside `proveMerge`/`proveSmul`/
`proveNeg` — each recursive step indexes into the precomputed suffix
array in O(1) instead of rebuilding it. -/
def precomputeSpine (atoms : Array Expr) (L : LinForm) :
    MetaM (Array Expr × Array Expr × Array Expr) := do
  let n := L.coeffs.size
  let mut qs : Array Expr := Array.mkEmpty n
  let mut heads : Array Expr := Array.mkEmpty n
  for k in [0:n] do
    let (v, c) := L.coeffs[k]!
    let qE ← mkQLit c
    qs := qs.push qE
    let cE := mkApp (mkConst ``Q.toRat) qE
    if h : v < atoms.size then
      heads := heads.push (mkRatMul cE atoms[v])
    else
      throwError "fast discharger: atom index {v} out of bounds"
  -- suffix[k] = ⟦L[k..n]⟧. Build right-to-left:
  --   suffix_rev[0] = mkRatLit L.const   (corresponds to suffix[n])
  --   suffix_rev[i] = mkRatAdd heads[n-i] suffix_rev[i-1]  (corresponds to suffix[n-i])
  -- Final: reverse to get suffix[0..n].
  let mut suffixRev : Array Expr := Array.mkEmpty (n + 1)
  suffixRev := suffixRev.push (← mkRatLit L.const)
  for i in [0:n] do
    let head := heads[n - 1 - i]!
    let prev := suffixRev.back!
    suffixRev := suffixRev.push (mkRatAdd head prev)
  let suffix := suffixRev.reverse
  return (qs, heads, suffix)

partial def proveMerge (atoms : Array Expr) (L₁ L₂ : LinForm) :
    MetaM (LinForm × Expr × Expr) := do
  let (qs₁, heads₁, suffix₁) ← precomputeSpine atoms L₁
  let (qs₂, heads₂, suffix₂) ← precomputeSpine atoms L₂
  let rec go (i j : Nat) : MetaM (LinForm × Expr × Expr) := do
    let n₁ := L₁.coeffs.size
    let n₂ := L₂.coeffs.size
    let aDone := i ≥ n₁
    let bDone := j ≥ n₂
    if aDone && bDone then
      let (mVal, _qmE, pf) ← proveRatlitAdd suffix₁[n₁]!.appArg!
                                              suffix₂[n₂]!.appArg!
                                              L₁.const L₂.const
      -- Note: suffix[n] = mkRatLit L.const = Q.toRat (Q.mk ...). Its appArg! is Q.mk.
      let resE ← mkRatLit mVal
      return ({ coeffs := #[], const := mVal }, pf, resE)
    if aDone then
      -- Left exhausted: peel head off right.
      let (vB, cB) := L₂.coeffs[j]!
      let h := heads₂[j]!
      let (restL, pRest, resPrev) ← go i (j+1)
      let lhsConst := suffix₁[n₁]!
      let tbE := suffix₂[j+1]!
      let pf := mkAppN (mkConst ``take_right) #[lhsConst, h, tbE, resPrev, pRest]
      let resE := mkRatAdd h resPrev
      return ({ restL with coeffs := #[(vB, cB)] ++ restL.coeffs }, pf, resE)
    if bDone then
      let (vA, cA) := L₁.coeffs[i]!
      let h := heads₁[i]!
      let (restL, pRest, resPrev) ← go (i+1) j
      let rhsConst := suffix₂[n₂]!
      let taE := suffix₁[i+1]!
      let pf := mkAppN (mkConst ``take_left) #[h, taE, rhsConst, resPrev, pRest]
      let resE := mkRatAdd h resPrev
      return ({ restL with coeffs := #[(vA, cA)] ++ restL.coeffs }, pf, resE)
    -- Interior: compare atom indices.
    let (vA, cA) := L₁.coeffs[i]!
    let (vB, cB) := L₂.coeffs[j]!
    if vA > vB then
      let h := heads₁[i]!
      let (restL, pRest, resPrev) ← go (i+1) j
      let taE := suffix₁[i+1]!
      let bE := suffix₂[j]!
      let pf := mkAppN (mkConst ``take_left) #[h, taE, bE, resPrev, pRest]
      let resE := mkRatAdd h resPrev
      return ({ restL with coeffs := #[(vA, cA)] ++ restL.coeffs }, pf, resE)
    else if vB > vA then
      let h := heads₂[j]!
      let (restL, pRest, resPrev) ← go i (j+1)
      let aE := suffix₁[i]!
      let tbE := suffix₂[j+1]!
      let pf := mkAppN (mkConst ``take_right) #[aE, h, tbE, resPrev, pRest]
      let resE := mkRatAdd h resPrev
      return ({ restL with coeffs := #[(vB, cB)] ++ restL.coeffs }, pf, resE)
    else
      -- vA == vB: combine.
      let qaE := qs₁[i]!
      let qbE := qs₂[j]!
      let (mVal, qmE, hm) ← proveRatlitAdd qaE qbE cA cB
      let xE := atoms[vA]!
      let cAE := mkApp (mkConst ``Q.toRat) qaE
      let cBE := mkApp (mkConst ``Q.toRat) qbE
      let mE := mkApp (mkConst ``Q.toRat) qmE
      let (restL, pRest, resPrev) ← go (i+1) (j+1)
      let taE := suffix₁[i+1]!
      let tbE := suffix₂[j+1]!
      if mVal.num = 0 then
        let pf := mkAppN (mkConst ``combine_zero)
          #[xE, taE, tbE, resPrev, cAE, cBE, pRest, hm]
        return (restL, pf, resPrev)
      else
        let pf := mkAppN (mkConst ``combine)
          #[xE, taE, tbE, resPrev, cAE, cBE, mE, pRest, hm]
        let newHead := mkRatMul mE xE
        let resE := mkRatAdd newHead resPrev
        return ({ restL with coeffs := #[(vA, mVal)] ++ restL.coeffs }, pf, resE)
  go 0 0

/-! ## proveSmul: scale a LinForm by a Q. -/

partial def proveSmul (atoms : Array Expr) (kE : Expr) (kVal : Q) (L : LinForm) :
    MetaM (LinForm × Expr × Expr) := do
  let qkE ← mkQLit kVal
  let rec go (i : Nat) : MetaM (LinForm × Expr × Expr) := do
    let n := L.coeffs.size
    if i ≥ n then
      let qaE ← mkQLit L.const
      let (mVal, _qmE, pf) ← proveRatlitMul qkE qaE kVal L.const
      let resE ← mkRatLit mVal
      return ({ coeffs := #[], const := mVal }, pf, resE)
    let (v, c) := L.coeffs[i]!
    let qcE ← mkQLit c
    let (mVal, qmE, hm) ← proveRatlitMul qkE qcE kVal c
    let xE := atoms[v]!
    let cE := mkApp (mkConst ``Q.toRat) qcE
    let mE := mkApp (mkConst ``Q.toRat) qmE
    let (restL, pRest, resPrev) ← go (i+1)
    let restE : Expr ← do
      let mut acc ← mkRatLit L.const
      for k in [i+1:n] do
        let idx := (n-1) - (k - (i+1))
        let (vK, cK) := L.coeffs[idx]!
        let cKE ← mkRatLit cK
        let head := mkRatMul cKE atoms[vK]!
        acc := mkRatAdd head acc
      pure acc
    let pf := mkAppN (mkConst ``smul_cons) #[kE, xE, cE, mE, restE, resPrev, hm, pRest]
    if mVal.num = 0 then
      return (restL, pf, resPrev)
    else
      let newHead := mkRatMul mE xE
      let resE := mkRatAdd newHead resPrev
      return ({ restL with coeffs := #[(v, mVal)] ++ restL.coeffs }, pf, resE)
  go 0

/-! ## proveNeg: negate a LinForm. -/

partial def proveNeg (atoms : Array Expr) (L : LinForm) :
    MetaM (LinForm × Expr × Expr) := do
  let rec go (i : Nat) : MetaM (LinForm × Expr × Expr) := do
    let n := L.coeffs.size
    if i ≥ n then
      let qaE ← mkQLit L.const
      let (mVal, _qmE, pf) ← proveRatlitNeg qaE L.const
      let resE ← mkRatLit mVal
      return ({ coeffs := #[], const := mVal }, pf, resE)
    let (v, c) := L.coeffs[i]!
    let qcE ← mkQLit c
    let (mVal, qmE, hm) ← proveRatlitNeg qcE c
    let xE := atoms[v]!
    let cE := mkApp (mkConst ``Q.toRat) qcE
    let mE := mkApp (mkConst ``Q.toRat) qmE
    let (restL, pRest, resPrev) ← go (i+1)
    let restE : Expr ← do
      let mut acc ← mkRatLit L.const
      for k in [i+1:n] do
        let idx := (n-1) - (k - (i+1))
        let (vK, cK) := L.coeffs[idx]!
        let cKE ← mkRatLit cK
        let head := mkRatMul cKE atoms[vK]!
        acc := mkRatAdd head acc
      pure acc
    let pf := mkAppN (mkConst ``neg_cons) #[xE, cE, mE, restE, resPrev, hm, pRest]
    if mVal.num = 0 then
      return (restL, pf, resPrev)
    else
      let newHead := mkRatMul mE xE
      let resE := mkRatAdd newHead resPrev
      return ({ restL with coeffs := #[(v, mVal)] ++ restL.coeffs }, pf, resE)
  go 0

/-! ## Numeral recognizer (subset of lp's quickScalarLit?). -/

partial def asRatLit? (e : Expr) : Option Q :=
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) =>
      match n.rawNatLit? with
      | some k => some { num := Int.ofNat k, den := 1 }
      | none => none
  | (``Neg.neg, #[_, _, x]) => (asRatLit? x).map (fun q => Q.neg q)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) => do
      let ra ← asRatLit? a
      let rb ← asRatLit? b
      -- Simplification: require rb is positive integer literal.
      if rb.den == 1 then
        match rb.num with
        | .ofNat (k+1) =>
            some { num := ra.num, den := ra.den * (k+1),
                   den_nz := Nat.mul_ne_zero ra.den_nz (by simp) }
        | _ => none
      else none
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do
      let ra ← asRatLit? a
      let rb ← asRatLit? b
      some (Q.mul ra rb)
  | _ => none

/-! ## normalizeR — per-row Expr walker.

Given a Rat-typed expression `e`, return `(L, pf : e = ⟦L⟧, ⟦L⟧)`.
Throws if any subterm is neither a recognized literal/atom nor an
arithmetic op. The caller catches and falls back to `ring1`. -/

partial def normalizeR (atomMap : Std.HashMap Expr Nat) (atoms : Array Expr) (e : Expr) :
    MetaM (LinForm × Expr × Expr) := do
  -- Closed literal?
  if let some r := asRatLit? e then
    let lit ← mkRatLit r
    let pf ← mkRatEqByDefeq e lit
    return ({ coeffs := #[], const := r }, pf, lit)
  -- Atom?
  if let some idx := atomMap[e]? then
    let L : LinForm := { coeffs := #[(idx, { num := 1, den := 1 })], const := Q.zero }
    let pf := mkApp (mkConst ``atom_norm) e
    let rL ← render atoms L
    return (L, pf, rL)
  -- Otherwise dispatch on the head.
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      let (La, pa, rA) ← normalizeR atomMap atoms a
      let (Lb, pb, rB) ← normalizeR atomMap atoms b
      let step1 := mkAppN (mkConst ``add_congr_eq) #[a, rA, b, rB, pa, pb]
      let (L, pm, rL) ← proveMerge atoms La Lb
      let rAddRB := mkRatAdd rA rB
      let pf := mkEqTransFast ratType e rAddRB rL step1 pm
      return (L, pf, rL)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      let (La, pa, rA) ← normalizeR atomMap atoms a
      let (Lb, pb, rB) ← normalizeR atomMap atoms b
      let (Lnb, pn, rLnb) ← proveNeg atoms Lb
      let (L, pm, rL) ← proveMerge atoms La Lnb
      let negB := mkRatNeg b
      let negRB := mkRatNeg rB
      let midSub := mkRatAdd a negB
      let midAdd := mkRatAdd rA rLnb
      let step1 := mkAppN (mkConst ``sub_to_add_neg) #[a, b]
      let stepNeg := mkAppN (mkConst ``neg_congr_eq) #[b, rB, pb]
      let stepNegFull := mkEqTransFast ratType negB negRB rLnb stepNeg pn
      let step2 := mkAppN (mkConst ``add_congr_eq) #[a, rA, negB, rLnb, pa, stepNegFull]
      let chained := mkEqTransFast ratType e midSub midAdd step1 step2
      let pf := mkEqTransFast ratType e midAdd rL chained pm
      return (L, pf, rL)
  | (``Neg.neg, #[_, _, a]) =>
      let (La, pa, rA) ← normalizeR atomMap atoms a
      let (L, pn, rL) ← proveNeg atoms La
      let negRA := mkRatNeg rA
      let step1 := mkAppN (mkConst ``neg_congr_eq) #[a, rA, pa]
      let pf := mkEqTransFast ratType e negRA rL step1 pn
      return (L, pf, rL)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      -- Scalar * non-scalar?
      if let some kVal := asRatLit? a then
        -- e = a * b = (user numeral) * b
        -- Bridge to Q.toRat-headed form for proveSmul to compose.
        let (Lb, pb, rB) ← normalizeR atomMap atoms b
        let qkE ← mkQLit kVal
        let kQRatE := mkApp (mkConst ``Q.toRat) qkE
        let qkMulB := mkRatMul kQRatE b
        let qkMulRB := mkRatMul kQRatE rB
        let bridge ← mkRatEqByDefeq e qkMulB
        let step1 := mkAppN (mkConst ``mul_congr_eq_r) #[kQRatE, b, rB, pb]
        let (L, ps, rL) ← proveSmul atoms kQRatE kVal Lb
        let bridgeStep := mkEqTransFast ratType e qkMulB qkMulRB bridge step1
        let pf := mkEqTransFast ratType e qkMulRB rL bridgeStep ps
        return (L, pf, rL)
      -- non-scalar * scalar?
      else if let some kVal := asRatLit? b then
        let (La, pa, rA) ← normalizeR atomMap atoms a
        let qkE ← mkQLit kVal
        let kQRatE := mkApp (mkConst ``Q.toRat) qkE
        let qkMulA := mkRatMul kQRatE a
        let qkMulRA := mkRatMul kQRatE rA
        -- Bridge: a * b = b * a (Rat.mul_comm)  then  b * a = Q.toRat ⟨b⟩ * a (defeq)
        let commPf := mkAppN (mkConst ``Rat.mul_comm) #[a, b]
        let bMulA := mkRatMul b a
        let bridge ← mkRatEqByDefeq bMulA qkMulA
        let chainBridge := mkEqTransFast ratType e bMulA qkMulA commPf bridge
        let step1 := mkAppN (mkConst ``mul_congr_eq_r) #[kQRatE, a, rA, pa]
        let (L, ps, rL) ← proveSmul atoms kQRatE kVal La
        let bridgeStep := mkEqTransFast ratType e qkMulA qkMulRA chainBridge step1
        let pf := mkEqTransFast ratType e qkMulRA rL bridgeStep ps
        return (L, pf, rL)
      else
        throwError "fast discharger: HMul with neither operand numeric: {e}"
  | _ =>
      throwError "fast discharger: unhandled Expr shape: {e}"

/-! ## reassocLeftToRight: convert a left-folded sum to right-nested form. -/

/-- Given a left-folded sum `((a₁ + a₂) + a₃) + … + aₙ` of `Rat` Exprs,
return `(sm_right, pf : sm_left = sm_right)` where `sm_right` is right-nested
`a₁ + (a₂ + (… + aₙ))`. Uses `reassoc_step = add_assoc` repeatedly.

If the input has ≤ 2 terms, returns it unchanged with `Eq.refl`. -/
partial def reassocLeftToRight (sm : Expr) : MetaM (Expr × Expr) := do
  -- Decompose sm into a left-leaning list of summands.
  let rec collect (e : Expr) : Array Expr := Id.run do
    match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => collect a ++ #[b]
    | _ => #[e]
  let terms := collect sm
  if terms.size ≤ 1 then
    return (sm, ← mkAppM ``Eq.refl #[sm])
  -- Build right-nested form.
  let mut acc := terms[terms.size - 1]!
  for i in [1:terms.size] do
    let idx := terms.size - 1 - i
    acc := mkRatAdd terms[idx]! acc
  -- Build the proof by induction. For sm = ((a + b) + c), we have:
  --   (a + b) + c = a + (b + c)   by reassoc_step.
  -- For longer sums, fall back to ring1 (correctness over construction simplicity).
  let smRight := acc
  let pf ← do
    let goalEq ← mkEq sm smRight
    let mvar ← mkFreshExprMVar (some goalEq)
    let (_, _) ← (Lean.Elab.Tactic.run mvar.mvarId! do
      Lean.Elab.Tactic.evalTactic (← `(tactic| ring1))).run
    instantiateMVars mvar
  return (smRight, pf)

end Mathlib.Tactic.Linarith.FastDischarger

/-! ## Top-level entry points. -/

namespace Mathlib.Tactic.Linarith.FastDischarger

open Mathlib.Tactic.Linarith

/-- A fallback counter, incremented every time the fast path declines and
linarith uses ring1. Useful for the benchmark coverage check. -/
initialize fastDischargerFallbackCount : IO.Ref Nat ← IO.mkRef 0
/-- A success counter for fast-path proofs. -/
initialize fastDischargerSuccessCount : IO.Ref Nat ← IO.mkRef 0

/-! ## Fine-grained stage timers.

Per-stage cumulative time (in nanoseconds) across all discharger invocations
since module init. Reset and print via `resetFastDischargerTimers` and
`printFastDischargerTimers`. -/

initialize timerValidate : IO.Ref Nat ← IO.mkRef 0
initialize timerAtomMap : IO.Ref Nat ← IO.mkRef 0
initialize timerNormalizeR : IO.Ref Nat ← IO.mkRef 0
initialize timerBuildScaledRow : IO.Ref Nat ← IO.mkRef 0
initialize timerProveBalancedSum : IO.Ref Nat ← IO.mkRef 0
initialize timerBridge : IO.Ref Nat ← IO.mkRef 0
initialize timerClose : IO.Ref Nat ← IO.mkRef 0
initialize timerTotal : IO.Ref Nat ← IO.mkRef 0

/-- Wrap an action with a stage timer, accumulating elapsed nanoseconds. -/
@[inline] def withTimer {α} (ref : IO.Ref Nat) (act : MetaM α) : MetaM α := do
  let t0 ← IO.monoNanosNow
  let r ← act
  let t1 ← IO.monoNanosNow
  ref.modify (· + (t1 - t0))
  return r

/-- Reset all stage timers + counters to zero. -/
def resetFastDischargerTimers : IO Unit := do
  timerValidate.set 0
  timerAtomMap.set 0
  timerNormalizeR.set 0
  timerBuildScaledRow.set 0
  timerProveBalancedSum.set 0
  timerBridge.set 0
  timerClose.set 0
  timerTotal.set 0
  fastDischargerSuccessCount.set 0
  fastDischargerFallbackCount.set 0

/-- Print all stage timers as ms (formatted). -/
def printFastDischargerTimers : IO Unit := do
  let fmt (label : String) (ns : Nat) : String :=
    let ms := (Float.ofNat ns) / 1e6
    s!"  {label.rightpad 22} {ms}ms"
  IO.println "FastDischarger timers (cumulative across all invocations):"
  IO.println (fmt "validate" (← timerValidate.get))
  IO.println (fmt "atom map" (← timerAtomMap.get))
  IO.println (fmt "normalizeR (per-row)" (← timerNormalizeR.get))
  IO.println (fmt "buildScaledRowProof" (← timerBuildScaledRow.get))
  IO.println (fmt "proveBalancedSum" (← timerProveBalancedSum.get))
  IO.println (fmt "bridge (left-fold)" (← timerBridge.get))
  IO.println (fmt "close (rhs = 0)" (← timerClose.get))
  IO.println (fmt "TOTAL discharger" (← timerTotal.get))
  IO.println s!"  successes: {← fastDischargerSuccessCount.get}, fallbacks: {← fastDischargerFallbackCount.get}"

/-- Build the per-row "scaled term" Expr matching exactly what linarith's
`mulExpr c tᵢ` produces inside `sm`. For c=1, returns just `tᵢ`. Otherwise
returns `OfNat.ofNat c * tᵢ` via `mulExpr`. -/
def matchRowMlsExpr (c : Nat) (tE : Expr) : MetaM Expr := do
  if c == 1 then return tE
  else
    -- Mimic mulExpr c tE for Rat: build `OfNat.ofNat c * tE` with the Rat instance.
    let cE ← mkAppOptM ``OfNat.ofNat #[some (mkConst ``Rat), some (mkNatLit c), none]
    return mkRatMul cE tE

/-- Build proof `mls[i] = ⟦Lᵢ'⟧` and the rendered `⟦Lᵢ'⟧`, where:
- `pNormᵢ : tᵢ = ⟦Lᵢ⟧`
- `Lᵢ' := if c=1 then Lᵢ else (Lᵢ.smul ⟨c,1,_⟩)`

For c=1, just returns `pNormᵢ` and `rLᵢ` directly.
For c>1, builds:
  bridge : OfNat.ofNat c * tᵢ = Q.toRat ⟨c,1⟩ * tᵢ                [Eq.refl-by-defeq]
  cong   : Q.toRat ⟨c,1⟩ * tᵢ = Q.toRat ⟨c,1⟩ * rLᵢ              [mul_congr_eq_r pNormᵢ]
  smul   : Q.toRat ⟨c,1⟩ * rLᵢ = rScaledᵢ                          [proveSmul output]
  pf = trans (trans bridge cong) smul -/
def buildScaledRowProof (atoms : Array Expr) (c : Nat) (tE : Expr)
    (Lᵢ : LinForm) (pNormᵢ rLᵢ : Expr) :
    MetaM (LinForm × Expr × Expr) := do
  let mlsE ← matchRowMlsExpr c tE
  if c == 1 then
    return (Lᵢ, pNormᵢ, rLᵢ)
  let cQ : Q := { num := Int.ofNat c, den := 1 }
  let qkE ← mkQLit cQ
  let kQRatE := mkApp (mkConst ``Q.toRat) qkE
  -- bridge: mlsE = kQRatE * tE  (defeq: OfNat.ofNat c = Q.toRat ⟨c,1,_⟩)
  let qToRatMulT := mkRatMul kQRatE tE
  let bridge ← mkRatEqByDefeq mlsE qToRatMulT
  -- proveSmul with kE = kQRatE — its outputs use Q.toRat-headed forms internally
  let (Lscaled, pSmul, rScaled) ← proveSmul atoms kQRatE cQ Lᵢ
  -- cong: kQRatE * tE = kQRatE * rLᵢ
  let qToRatMulRL := mkRatMul kQRatE rLᵢ
  let cong := mkAppN (mkConst ``mul_congr_eq_r) #[kQRatE, tE, rLᵢ, pNormᵢ]
  -- Compose: mlsE = qToRatMulT = qToRatMulRL = rScaled
  let bridgeCong := mkEqTransFast ratType mlsE qToRatMulT qToRatMulRL bridge cong
  let pf := mkEqTransFast ratType mlsE qToRatMulRL rScaled bridgeCong pSmul
  return (Lscaled, pf, rScaled)

/-! ## Balanced tree fold for the combine step.

The entry-point combine step folds the per-row proofs `pfᵢ : mlsᵢ = ⟦Lᵢ⟧`
into a single proof `sm = ⟦totalL⟧`. The straightforward left-fold (matching
`addExprs`'s left-association) produces an O(n²) proof term because each
merge step generates a proof whose size grows with the accumulator.

The balanced binary tree fold below produces an O(n log n) proof term — the
kernel-checking cost scales accordingly. Trade-off: the output proof's LHS
has balanced-tree shape, not `sm`'s left-fold shape, so we need a bridge
proof. The bridge is a single `ring1` call on a pure-associativity goal
(`sm_left_fold = sm_balanced`), which is small and fast. -/

/-- Recursively merge a slice `[lo, hi)` of pre-built per-row proofs in a
balanced binary tree. Returns `(L, pf, rL, lhsE)` where:
  - `L` is the merged LinForm.
  - `pf : lhsE = ⟦L⟧`.
  - `rL = ⟦L⟧` (rendered).
  - `lhsE` is the balanced-tree-shaped LHS Expr (NOT matching linarith's
    left-fold; the caller bridges separately).

For a singleton slice returns the row's data directly.
For a pair, one `proveMerge` call.
For longer slices, splits in the middle and recurses, composing via
`add_congr_eq` + `proveMerge` + `mkEqTransFast`. -/
partial def proveBalancedSum (atoms : Array Expr)
    (rowProofs : Array (LinForm × Expr × Expr × Expr)) (lo hi : Nat) :
    MetaM (LinForm × Expr × Expr × Expr) := do
  if hi == lo + 1 then
    let (L, pf, rL, mlsE) := rowProofs[lo]!
    return (L, pf, rL, mlsE)
  let mid := lo + (hi - lo) / 2
  let (L1, pf1, rL1, lhs1) ← proveBalancedSum atoms rowProofs lo mid
  let (L2, pf2, rL2, lhs2) ← proveBalancedSum atoms rowProofs mid hi
  let combinedLhs := mkRatAdd lhs1 lhs2
  let midRhs := mkRatAdd rL1 rL2
  -- cong: lhs1 + lhs2 = rL1 + rL2
  let congPf := mkAppN (mkConst ``add_congr_eq) #[lhs1, rL1, lhs2, rL2, pf1, pf2]
  -- merge: rL1 + rL2 = newRL
  let (newL, mergePf, newRL) ← proveMerge atoms L1 L2
  let composed := mkEqTransFast ratType combinedLhs midRhs newRL congPf mergePf
  return (newL, composed, newRL, combinedLhs)

/-- Build the left-folded sum Expr of `leaves[lo..hi)`. -/
partial def leftFoldExpr (leaves : Array Expr) (lo hi : Nat) : Expr :=
  if hi == lo + 1 then leaves[lo]!
  else mkRatAdd (leftFoldExpr leaves lo (hi - 1)) leaves[hi - 1]!

/-- Proof: `leftFoldOf leaves[lo..hi) = leftFoldOf leaves[lo..mid) + leftFoldOf leaves[mid..hi)`.

Iteratively builds the proof from the base case (`k = mid + 1`) upward,
maintaining the right-side fold and the proof simultaneously. Total: O(hi - mid)
lemma applications, O(hi - mid) tactic-side work. -/
def buildSplitProof (leaves : Array Expr) (lo mid hi : Nat) : MetaM Expr := do
  if mid + 1 == hi then
    -- Base: leftFoldOf [lo, mid+1) = leftFoldOf [lo, mid) + leaves[mid]
    --     = leftFoldOf [lo, mid) + leftFoldOf [mid, mid+1)
    -- These are equal as Exprs (both are `foldLoMid + leaves[mid]`), so refl.
    let foldLoHi := leftFoldExpr leaves lo hi
    return mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) ratType foldLoHi
  let foldLoMid := leftFoldExpr leaves lo mid
  -- Invariant at iteration k (mid+1 ≤ k ≤ hi):
  --   foldLoK  = leftFoldOf [lo, k)
  --   foldMidK = leftFoldOf [mid, k)
  --   pf       : leftFoldOf [lo, k) = foldLoMid + foldMidK
  -- Initial (k = mid+1):
  --   foldLoK  = foldLoMid + leaves[mid]
  --   foldMidK = leaves[mid]
  --   pf       = Eq.refl (foldLoMid + leaves[mid])
  let mut foldLoK := mkRatAdd foldLoMid leaves[mid]!
  let mut foldMidK := leaves[mid]!
  let mut pf : Expr :=
    mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) ratType foldLoK
  for k in [mid + 2 : hi + 1] do
    let lastLeaf := leaves[k - 1]!
    -- Step: take pf : foldLoK_old = foldLoMid + foldMidK_old.
    -- New foldLoK = foldLoK_old + lastLeaf.
    -- New foldMidK = foldMidK_old + lastLeaf.
    -- Goal: new foldLoK = foldLoMid + new foldMidK.
    let newFoldLoK := mkRatAdd foldLoK lastLeaf
    let newFoldMidK := mkRatAdd foldMidK lastLeaf
    let viaRhs := mkRatAdd (mkRatAdd foldLoMid foldMidK) lastLeaf
    let goal := mkRatAdd foldLoMid newFoldMidK
    -- (1) cong: foldLoK_old + lastLeaf = (foldLoMid + foldMidK_old) + lastLeaf
    let reflLast :=
      mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) ratType lastLeaf
    let cong := mkAppN (mkConst ``add_congr_eq)
      #[foldLoK, mkRatAdd foldLoMid foldMidK, lastLeaf, lastLeaf, pf, reflLast]
    -- (2) assoc: (foldLoMid + foldMidK_old) + lastLeaf
    --          = foldLoMid + (foldMidK_old + lastLeaf)
    let assocPf := mkAppN (mkConst ``reassoc_step)
      #[foldLoMid, foldMidK, lastLeaf]
    -- Chain
    pf := mkEqTransFast ratType newFoldLoK viaRhs goal cong assocPf
    foldLoK := newFoldLoK
    foldMidK := newFoldMidK
  return pf

/-- Build the balanced-tree Expr of `leaves[lo..hi)`. Must match the split
schedule used by `proveBalancedSum`. -/
partial def balancedExpr (leaves : Array Expr) (lo hi : Nat) : Expr :=
  if hi == lo + 1 then leaves[lo]!
  else
    let mid := lo + (hi - lo) / 2
    mkRatAdd (balancedExpr leaves lo mid) (balancedExpr leaves mid hi)

/-- Bridge proof: `leftFoldOf leaves[lo..hi) = balancedOf leaves[lo..hi)`.
Recursively splits with the same schedule as `proveBalancedSum`. -/
partial def bridgeLeftFoldToBalancedRange (leaves : Array Expr) (lo hi : Nat) :
    MetaM Expr := do
  let leftFoldLoHi := leftFoldExpr leaves lo hi
  if hi == lo + 1 then
    return mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) ratType leftFoldLoHi
  let mid := lo + (hi - lo) / 2
  -- Step 1: leftFoldOf [lo, hi) = leftFoldOf [lo, mid) + leftFoldOf [mid, hi)
  let splitPf ← buildSplitProof leaves lo mid hi
  let foldLoMid := leftFoldExpr leaves lo mid
  let foldMidHi := leftFoldExpr leaves mid hi
  let splitForm := mkRatAdd foldLoMid foldMidHi
  -- Step 2: recursively bridge each half.
  let leftBridge ← bridgeLeftFoldToBalancedRange leaves lo mid
  let rightBridge ← bridgeLeftFoldToBalancedRange leaves mid hi
  let balLeft := balancedExpr leaves lo mid
  let balRight := balancedExpr leaves mid hi
  let balForm := mkRatAdd balLeft balRight
  let combined := mkAppN (mkConst ``add_congr_eq)
    #[foldLoMid, balLeft, foldMidHi, balRight, leftBridge, rightBridge]
  return mkEqTransFast ratType leftFoldLoHi splitForm balForm splitPf combined

def bridgeLeftFoldToBalanced (leaves : Array Expr) (_sm _balancedLhs : Expr) :
    MetaM Expr := do
  bridgeLeftFoldToBalancedRange leaves 0 leaves.size

def ratFastDischargerStructured : FastDischargerFn := fun input => do
  let tTotalStart ← IO.monoNanosNow
  -- Restrict to ℚ goals.
  unless input.goalType.isConstOf ``Rat do
    fastDischargerFallbackCount.modify (· + 1)
    return none
  -- ===== Validate (linexp → LinForm + Farkas residual check) =====
  let validateResult : Option (Array LinForm) ← withTimer timerValidate do
    -- Build the reverse monomMap ONCE for all rows.
    let revMap := buildLinexpRevMap input.monomMap
    let mut linForms : Array LinForm := Array.mkEmpty input.rows.size
    let mut total : LinForm := LinForm.zero
    for (_, le, c) in input.rows do
      match linexpToLinForm revMap le with
      | none => return none
      | some L =>
          let cQ : Q := { num := Int.ofNat c, den := 1 }
          linForms := linForms.push L
          total := total.add (L.smul cQ)
    unless total.coeffs.size == 0 && total.const.num == 0 do return none
    if input.rows.size == 0 then return none
    return some linForms
  let linForms ← match validateResult with
    | none =>
        fastDischargerFallbackCount.modify (· + 1)
        return none
    | some lf => pure lf
  -- ===== Atom map =====
  let atomMap ← withTimer timerAtomMap do return buildAtomMap input.atoms
  try
    let mut rowProofs : Array (LinForm × Expr × Expr × Expr) := Array.mkEmpty input.rows.size
    -- ===== Per-row: normalizeR + buildScaledRowProof =====
    for h : i in [0:input.rows.size] do
      let (tE, _, c) := input.rows[i]
      let Lᵢ := linForms[i]!
      let (Lᵢ', pNormᵢ, rLᵢ) ← withTimer timerNormalizeR do
        normalizeR atomMap input.atoms tE
      let _ := Lᵢ
      let (Lscaled, pf, rScaled, mlsE) ← withTimer timerBuildScaledRow do
        let mlsE ← matchRowMlsExpr c tE
        let (Lscaled, pf, rScaled) ←
          buildScaledRowProof input.atoms c tE Lᵢ' pNormᵢ rLᵢ
        return (Lscaled, pf, rScaled, mlsE)
      rowProofs := rowProofs.push (Lscaled, pf, rScaled, mlsE)
    -- ===== proveBalancedSum =====
    let (_accL, balancedPf, accRhs, balancedLhs) ← withTimer timerProveBalancedSum do
      proveBalancedSum input.atoms rowProofs 0 rowProofs.size
    -- ===== Bridge =====
    let bridgePf ← withTimer timerBridge do
      let leaves : Array Expr := rowProofs.map (fun (_, _, _, mlsE) => mlsE)
      bridgeLeftFoldToBalanced leaves input.sm balancedLhs
    let accPf := mkEqTransFast ratType input.sm balancedLhs accRhs bridgePf balancedPf
    -- ===== Close =====
    let final ← withTimer timerClose do
      let zeroE ← mkAppOptM ``OfNat.ofNat
        #[some (mkConst ``Rat), some (mkNatLit 0), none]
      let closePf ← mkRatEqByDefeq accRhs zeroE
      return mkEqTransFast ratType input.sm accRhs zeroE accPf closePf
    fastDischargerSuccessCount.modify (· + 1)
    let tTotalEnd ← IO.monoNanosNow
    timerTotal.modify (· + (tTotalEnd - tTotalStart))
    return some final
  catch _ =>
    fastDischargerFallbackCount.modify (· + 1)
    return none
/-- The "ring fallback" variant — also goes through the structured path but
ultimately closes via ring1. Functionally equivalent to the structured one
for now; kept as a separate name for the benchmark harness. -/
def ratFastDischargerRingFallback : FastDischargerFn := ratFastDischargerStructured

end Mathlib.Tactic.Linarith.FastDischarger
