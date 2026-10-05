/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Util.AtLocation
public meta import Mathlib.Util.AtomM
public import Mathlib.Tactic.TryThis
public import Mathlib.Tactic.Hint
public meta import Lean.Elab.Tactic.Config
public meta import Lean.Elab.Tactic.Conv.Simp
public meta import Mathlib.Tactic.Conv
public meta import Lean.Meta.Sym.Simp.Main
public meta import Lean.Meta.Sym.Canon
public meta import Lean.Meta.Sym.Arith.Norm
public meta import Lean.Meta.Sym.Arith.Module

/-!
# The `bench_new_abel` tactic

Evaluate expressions in the language of additive, commutative monoids and groups.

-/

public section

-- TODO: assert_not_exists NonUnitalNonAssociativeSemiring
assert_not_exists IsOrderedMonoid TopologicalSpace PseudoMetricSpace

namespace Mathlib.Tactic.AbelBenchCurrent

meta section

open Lean Elab Meta Tactic

/--
`bench_new_abel` solves equations in the language of *additive*, commutative monoids and groups.

`bench_new_abel` and its variants work as both tactics and conv tactics.

* `bench_new_abel1` fails if the target is not an equality that is provable by the axioms of
  commutative monoids/groups.
* `bench_new_abel_nf` rewrites all group expressions into a normal form.
  * `bench_new_abel_nf at h` rewrites in a hypothesis.
  * `bench_new_abel_nf (config := cfg)` allows for additional configuration:
    * `red`: the reducibility setting (overridden by `!`).
    * `zetaDelta`: if true, local `let` variables can be unfolded (overridden by `!`).
* `bench_new_abel!`, `bench_new_abel1!`, `bench_new_abel_nf!` use default transparency to identify atoms
  and unfold local `let` variables.

Examples:
```
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by bench_new_abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by bench_new_abel
```
-/
syntax (name := bench_new_abel) "bench_new_abel" "!"? : tactic

/-- Configuration for `bench_new_abel_nf`. -/
structure AbelNF.Config where
  /-- Unfold local let variables. -/
  zetaDelta := false
  /-- Transparency used to identify atoms. -/
  red := TransparencyMode.reducible

/-- Elaborate `bench_new_abel_nf` configuration. -/
declare_config_elab elabAbelNFConfig AbelNF.Config

/-- Normalize scalar arithmetic and additive expressions inside atoms. -/
private def simpAtom (cfg : AbelNF.Config) (s : IO.Ref AtomM.State) (e : Expr) :
    Sym.Simp.SimpM Sym.Simp.Result := do
  if !e.hasFVar && !e.hasMVar then
    let type ← inferType e
    if type.isConstOf ``Nat || type.isConstOf ``Int then
      return ← Sym.Arith.normalize? e (fun _ => pure .rfl)
  let e' ← Sym.shareCommon (← Sym.canon e)
  -- Revisit only the children: an unsupported operation is also an atom.
  let methods ← Sym.Simp.getMethods
  let methods := { methods with pre := fun x => do
      if Sym.isSameExpr x e' then pure .rfl else methods.pre x }
  let r ← withReader (fun (_ : Sym.Simp.MethodsRef) => methods.toMethodsRef) <| Sym.Simp.simp e'
  let (_, atom') ← AtomM.addAtom (r.getResultExpr e') { red := cfg.red } s
  let atom' ← Sym.shareCommon atom'
  match r with
  | .rfl done cd =>
    if e == atom' then return .rfl done cd
    return .step atom' (← mkEqRefl atom') (done := true) (contextDependent := cd)
  | .step _ proof _ cd => return .step atom' proof (done := true) (contextDependent := cd)

private def methods (cfg : AbelNF.Config) (s : IO.Ref AtomM.State) : Sym.Simp.Methods :=
  { pre := fun e => Sym.Arith.normalizeAdd? e (simpAtom cfg s)
    post := fun e => do
      let_expr Eq _ a b := e | return .rfl
      unless ← withTransparency .default <| isDefEq a b do return .rfl
      return .step (← Sym.getTrueExpr) (← mkAppM ``eq_self #[a]) (done := true) }

/-- Normalize maximal additive expressions and recurse into their atoms. -/
private def normalize (cfg : AbelNF.Config) (s : IO.Ref AtomM.State) (e : Expr) :
    MetaM Simp.Result :=
    withConfig ({ · with zetaDelta := cfg.zetaDelta }) <| withNewMCtxDepth do
  let r ← Sym.SymM.run do
    withReader (fun (ctx : Sym.Context) =>
        { ctx with config := { ctx.config with enforceUnfoldReducible := false } }) do
      Sym.Simp.SimpM.run' (Sym.Simp.simp (← Sym.shareCommon (← Sym.canon e))) (methods cfg s)
  match r with
  | .rfl .. => return { expr := e }
  | .step e' proof .. =>
    if ← withTransparency .default <| isDefEq e e' then return { expr := e }
    return { expr := e', proof? := proof }

@[tactic_alt bench_new_abel]
elab (name := bench_new_abel1) "bench_new_abel1" tk:"!"? : tactic => withMainContext do
  let type ← instantiateMVars (← getMainTarget)
  unless (← whnfR type).isAppOfArity ``Eq 3 do
    throwError "`bench_new_abel1` requires an equality goal"
  let cfg : AbelNF.Config :=
    if tk.isSome then { red := .default, zetaDelta := true } else { zetaDelta := true }
  let r ← normalize cfg (← IO.mkRef {}) type
  unless r.expr.isTrue do throwError "`bench_new_abel1` found that the two sides were not equal"
  let proof ← mkOfEqTrue (← r.getProof)
  let proof ← Lean.Meta.mkAuxTheorem type proof (zetaDelta := true) (kind? := `_abel)
  closeMainGoal `bench_new_abel1 proof

@[tactic_alt bench_new_abel]
macro (name := bench_new_abel1!) "bench_new_abel1!" : tactic => `(tactic| bench_new_abel1 !)

open Parser.Tactic

@[tactic_alt bench_new_abel]
elab (name := abelNF) "bench_new_abel_nf" tk:"!"? cfg:optConfig loc:(location)? : tactic => do
  let mut cfg ← elabAbelNFConfig cfg
  if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  transformAtLocation (fun e => normalize cfg s e) "bench_new_abel_nf" loc (ifUnchanged := .error) false

@[tactic_alt bench_new_abel]
macro "bench_new_abel_nf!" cfg:optConfig loc:(location)? : tactic =>
  `(tactic| bench_new_abel_nf ! $cfg:optConfig $(loc)?)

@[inherit_doc bench_new_abel]
syntax (name := abelNFConv) "bench_new_abel_nf" "!"? optConfig : conv

/-- Elaborator for the `bench_new_abel_nf` tactic. -/
@[tactic abelNFConv]
def elabAbelNFConv : Tactic := fun stx ↦ match stx with
  | `(conv| bench_new_abel_nf $[!%$tk]? $cfg:optConfig) => withMainContext do
    let mut cfg ← elabAbelNFConfig cfg
    if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
    Conv.applySimpResult (← normalize cfg (← IO.mkRef {}) (← instantiateMVars (← Conv.getLhs)))
  | _ => Elab.throwUnsupportedSyntax

@[inherit_doc bench_new_abel]
macro "bench_new_abel_nf!" cfg:optConfig : conv => `(conv| bench_new_abel_nf ! $cfg:optConfig)

macro_rules
  | `(tactic| bench_new_abel !) => `(tactic| first | bench_new_abel1! | try_this bench_new_abel_nf!)
  | `(tactic| bench_new_abel) => `(tactic| first | bench_new_abel1 | try_this bench_new_abel_nf)

@[tactic_alt bench_new_abel]
macro "bench_new_abel!" : tactic => `(tactic| bench_new_abel !)

@[inherit_doc bench_new_abel]
macro (name := abelConv) "bench_new_abel" : conv =>
  `(conv| first | discharge => bench_new_abel1 | try_this bench_new_abel_nf)

@[inherit_doc abelConv] macro "bench_new_abel!" : conv =>
  `(conv| first | discharge => bench_new_abel1! | try_this bench_new_abel_nf!)

end

end Mathlib.Tactic.AbelBenchCurrent

/-!
We register `bench_new_abel` with the `hint` tactic.
-/

register_hint 950 bench_new_abel
