import Mathlib.Util.Notation3
import Mathlib.Data.Nat.Basic

set_option linter.style.setOption false
set_option pp.unicode.fun true
set_option autoImplicit true

namespace Test

-- set_option trace.notation3 true

def Filter (α : Type) : Type := (α → Prop) → Prop
def Filter.atTop [Preorder α] : Filter α := fun _ => True
def Filter.eventually (p : α → Prop) (f : Filter α) := f p

notation3 "∀ᶠ " (...) " in " f ", " r:(scoped p => Filter.eventually p f) => r

/-- info: ∀ᶠ (x : ℕ) (y : ℕ) in Filter.atTop, x < y : Prop -/
#guard_msgs in #check ∀ᶠ (x : Nat) (y) in Filter.atTop, x < y
/-- info: ∀ᶠ (x : ℕ) in Filter.atTop, x < 3 : Prop -/
#guard_msgs in #check ∀ᶠ x in Filter.atTop, x < 3

/-!
Test that `pp.tagAppFns` causes tokens to be tagged with head constant.
-/

open Lean in
def findWithTag (tag : Nat) (f : Format) : List Format :=
  match f with
  | .nil => []
  | .line => []
  | .align _ => []
  | .text _ => []
  | .nest _ f' => findWithTag tag f'
  | .append f' f'' => findWithTag tag f' ++ findWithTag tag f''
  | .group f' _ => findWithTag tag f'
  | .tag t f' => (if t = tag then [f'] else []) ++ findWithTag tag f'

open Lean Elab Term in
def testTagAppFns (n : Name) : TermElabM Unit := do
  let stx ← `(∀ᶠ x in Filter.atTop, x < 3)
  let e ← elabTermAndSynthesize stx none
  let f ← Meta.ppExprWithInfos e
  -- Find tags for the constant `n`
  let tags : Array Nat := f.infos.fold (init := #[]) fun tags tag info =>
    match info with
    | .ofTermInfo info | .ofDelabTermInfo info =>
      if info.expr.isConstOf n then
        tags.push tag
      else
        tags
    | _ => tags
  let fmts := tags.map (findWithTag · f.fmt)
  unless fmts.all (!·.isEmpty) do throwError "missing tag"
  let fmts := fmts.toList.flatten
  logInfo m!"{repr <| fmts.map (·.pretty.trim)}"

section
/-- info: [] -/
#guard_msgs in #eval testTagAppFns ``Filter.eventually
set_option pp.tagAppFns true
/-- info: ["∀ᶠ", "in", ","] -/
#guard_msgs in #eval testTagAppFns ``Filter.eventually
end


-- Testing lambda expressions:
notation3 "∀ᶠ' " f ", " p => Filter.eventually (fun x => (p : _ → _) x) f
/-- info: ∀ᶠ' Filter.atTop, fun x ↦ x < 3 : Prop -/
#guard_msgs in #check ∀ᶠ' Filter.atTop, fun x => x < 3

def foobar (p : α → Prop) (f : Prop) := ∀ x, p x = f

notation3 "∀ᶠᶠ " (...) " in " f ": "
  r1:(scoped p => Filter.eventually p f) ", " r2:(scoped p => foobar p r1) => r2

/-- info: ∀ᶠᶠ (x : ℕ) (y : ℕ) in Filter.atTop: x < y, x = y : Prop -/
#guard_msgs in #check ∀ᶠᶠ (x : Nat) (y) in Filter.atTop: x < y, x = y
/-- info: ∀ᶠᶠ (x : ℕ) in Filter.atTop: x < 3, x = 1 : Prop -/
#guard_msgs in #check ∀ᶠᶠ x in Filter.atTop: x < 3, x = 1
/-- info: ∀ᶠᶠ (x : ℕ) in Filter.atTop: x < 3, x = 1 : Prop -/
#guard_msgs in #check foobar (fun x ↦ Eq x 1) (Filter.atTop.eventually fun x ↦ LT.lt x 3)
/-- info: foobar (fun y ↦ y = 1) (∀ᶠ (x : ℕ) in Filter.atTop, x < 3) : Prop -/
#guard_msgs in #check foobar (fun y ↦ Eq y 1) (Filter.atTop.eventually fun x ↦ LT.lt x 3)

notation3 "∃' " (...) ", " r:(scoped p => Exists p) => r
/-- info: ∃' (a : ℕ) (_ : a < 3), a < 3 : Prop -/
#guard_msgs in #check ∃' a < 3, a < 3
/-- info: ∃' (x : ℕ) (_ : x < 3), True : Prop -/
#guard_msgs in #check ∃' _ < 3, True
/-- info: ∃' (x : ℕ) (_ : x < 1) (x_1 : ℕ) (_ : x_1 < 2), x = 0 : Prop -/
#guard_msgs in #check ∃' (x < 1) (_ < 2), x = 0

def func (x : α) : α := x
notation3 "func! " (...) ", " r:(scoped p => func p) => r
/-- info: (func! (x : ℕ → ℕ), x) fun x ↦ x * 2 : ℕ → ℕ -/
#guard_msgs in #check (func! (x : Nat → Nat), x) (· * 2)

structure MyUnit where
notation3 "~{" (x"; "* => foldl (a b => (a, b)) MyUnit) "}~" => x
/-- info: ~{1; true; ~{2}~}~ : ((Type × ℕ) × Bool) × Type × ℕ -/
#guard_msgs in #check ~{1; true; ~{2}~}~
/-- info: ~{}~ : Type -/
#guard_msgs in #check ~{}~

structure MyUnit' where
instance : OfNat MyUnit' (nat_lit 0) := ⟨{}⟩
notation3 "MyUnit'0" => (0 : MyUnit')
/-- info: MyUnit'0 : MyUnit' -/
#guard_msgs in #check (0 : MyUnit')
/-- info: 0 : ℕ -/
#guard_msgs in #check 0

notation3 "%[" (x", "* => foldr (a b => a :: b) []) "]" => x
/-- info: %[1, 2, 3] : List ℕ -/
#guard_msgs in #check %[1, 2, 3]

def foo (a : Nat) (f : Nat → Nat) := a + f a
def bar (a b : Nat) := a * b
notation3 "*[" x "] " (...) ", " v:(scoped c => bar x (foo x c)) => v
/-- info: *[1] (x : ℕ) (y : ℕ), x + y : ℕ -/
#guard_msgs in #check *[1] (x) (y), x + y
/-- info: bar 1 : ℕ → ℕ -/
#guard_msgs in #check bar 1

-- Checking that the `<|` macro is expanded when making matcher
def foo' (a : Nat) (f : Nat → Nat) := a + f a
def bar' (a b : Nat) := a * b
notation3 "*'[" x "] " (...) ", " v:(scoped c => bar' x <| foo' x c) => v
/-- info: *'[1] (x : ℕ) (y : ℕ), x + y : ℕ -/
#guard_msgs in #check *'[1] (x) (y), x + y
/-- info: bar' 1 : ℕ → ℕ -/
#guard_msgs in #check bar' 1

-- Need to give type ascription to `p` so that `p x` elaborates when making matcher
notation3 "MyPi " (...) ", " r:(scoped p => (x : _) → (p : _ → _) x) => r
/-- info: MyPi (x : ℕ) (y : ℕ), x < y : Prop -/
#guard_msgs in #check MyPi (x : Nat) (y : Nat), x < y

-- The notation parses fine, but the delaborator never succeeds, which is expected
def myId (x : α) := x
notation3 "BAD " c "; " (x", "* => foldl (a b => b) c) " DAB" => myId x
/-- info: myId 3 : ℕ -/
#guard_msgs in #check BAD 1; 2, 3 DAB

section
variable (x : Nat)
local notation3 "y" => x + 1
/-- info: y : ℕ -/
#guard_msgs in #check y
/-- info: y : ℕ -/
#guard_msgs in #check x + 1
end

section
variable (α : Type u) [Add α]
local notation3 x " +α " y => (x + y : α)
variable (x y : α)
/-- info: x +α y : α -/
#guard_msgs in #check x +α y
/-- info: x +α y : α -/
#guard_msgs in #check x + y
/-- info: 1 + 2 : ℕ -/
#guard_msgs in #check 1 + 2
end

def idStr : String → String := id

/--
error: Application type mismatch: In the application
  idStr Nat.zero
the argument
  Nat.zero
has type
  ℕ : Type
but is expected to have type
  String : Type
---
warning: Was not able to generate a pretty printer for this notation. If you do not expect it to be pretty printable, then you can use `notation3 (prettyPrint := false)`. If the notation expansion refers to section variables, be sure to do `local notation3`. Otherwise, you might be able to adjust the notation expansion to make it matchable; pretty printing relies on deriving an expression matcher from the expansion. (Use `set_option trace.notation3 true` to get some debug information.)
-/
#guard_msgs in
notation3 "error" => idStr Nat.zero

section
/--
warning: Was not able to generate a pretty printer for this notation. If you do not expect it to be
pretty printable, then you can use `notation3 (prettyPrint := false)`. If the notation expansion
refers to section variables, be sure to do `local notation3`. Otherwise, you might be able to adjust
the notation expansion to make it matchable; pretty printing relies on deriving an expression
matcher from the expansion. (Use `set_option trace.notation3 true` to get some debug information.)
-/
#guard_msgs (warning, drop error) in local notation3 "#" n => Fin.mk n (by decide)
end

section
set_option linter.unusedTactic false
local notation3 (prettyPrint := false) "#" n => Fin.mk n (by decide)

example : Fin 5 := #1

/--
error: tactic 'decide' proved that the proposition
  6 < 5
is false
-/
#guard_msgs in example : Fin 5 := #6

end

section test_scoped

scoped[MyNotation] notation3 "π" => (3 : Nat)

/-- error: unknown identifier 'π' -/
#guard_msgs in #check π

open scoped MyNotation

/-- info: π : ℕ -/
#guard_msgs in #check π

end test_scoped

/-!
Verifying that delaborator does not match the exact `Inhabited` instance.
Instead, it matches that it's an application of `Inhabited.default` whose first argument is `Nat`.
-/
/--
trace: [notation3] syntax declaration has name Test.termδNat
---
trace: [notation3] Generating matcher for pattern default
[notation3] Matcher creation succeeded; assembling delaborator
[notation3] matcher:
      matchApp✝ (matchApp✝ (matchExpr✝ (Expr.isConstOf✝ · `Inhabited.default)) (matchExpr✝ (Expr.isConstOf✝ · `Nat)))
          pure✝ >=>
        pure✝
[notation3] Creating delaborator for key Mathlib.Notation3.DelabKey.app (some `Inhabited.default) 2
---
trace: [notation3] Defined delaborator Test.termδNat.«delab_app.Inhabited.default»
-/
#guard_msgs in
set_option trace.notation3 true in
notation3 "δNat" => (default : Nat)

/-- info: δNat : ℕ -/
#guard_msgs in #check (default : Nat)
/-- info: δNat : ℕ -/
#guard_msgs in #check @default Nat (Inhabited.mk 5)


notation3 "(" "ignorez " "SVP" ")" => Sort _
notation3 "Objet " "mathématique " "supérieur" => Type _
notation3 "Énoncé" => Prop
notation3 "Objet " "mathématique" => Type
/-- info: 1 = 1 : Énoncé -/
#guard_msgs in #check 1 = 1
/-- info: Énoncé : Objet mathématique -/
#guard_msgs in #check Prop
/-- info: Nat : Objet mathématique -/
#guard_msgs in #check Nat
/-- info: Objet mathématique : Objet mathématique supérieur -/
#guard_msgs in #check Type
/-- info: PSum.{u, v} (α : (ignorez SVP)) (β : (ignorez SVP)) : (ignorez SVP) -/
#guard_msgs in #check PSum

end Test
