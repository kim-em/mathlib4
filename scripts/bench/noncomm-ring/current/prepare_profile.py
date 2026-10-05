from pathlib import Path
import subprocess
util='''module
public import Lean.Elab.Tactic
public section
namespace JacobiProfileUtil
initialize counters : IO.Ref (Array (String × Nat × Nat)) ← IO.mkRef #[]
@[noinline] def timed {m : Type → Type} [Monad m] [MonadLiftT Lean.MetaM m]
    (label : String) (action : m α) : m α := do
  let start ← (show Lean.MetaM Nat from IO.monoNanosNow)
  let result ← action
  let elapsed := (← (show Lean.MetaM Nat from IO.monoNanosNow)) - start
  let _ ← (show Lean.MetaM Unit from counters.modify fun entries =>
    match entries.findIdx? (·.1 == label) with
    | some i => entries.modify i fun (s, n, t) => (s, n + 1, t + elapsed)
    | none => entries.push (label, 1, elapsed))
  return result
@[noinline] def timedPure {m : Type → Type} [Monad m] [MonadLiftT Lean.MetaM m]
    (label : String) (action : Unit → α) : m α := do
  let start ← (show Lean.MetaM Nat from IO.monoNanosNow)
  let result := action ()
  let elapsed := (← (show Lean.MetaM Nat from IO.monoNanosNow)) - start
  let _ ← (show Lean.MetaM Unit from counters.modify fun entries =>
    match entries.findIdx? (·.1 == label) with
    | some i => entries.modify i fun (s, n, t) => (s, n + 1, t + elapsed)
    | none => entries.push (label, 1, elapsed))
  return result
end JacobiProfileUtil
'''
Path('JacobiProfileUtil.lean').write_text(util)
core=Path('/home/kim/worktrees/lean4/lean4-sym-module')
for name,source in [('Legacy',subprocess.check_output(['git','show','d81678a:src/Lean/Meta/Sym/Arith/Module.lean'],cwd=core,text=True)),('Current',(core/'src/Lean/Meta/Sym/Arith/Module.lean').read_text())]:
 s=source.replace('public section','public import JacobiProfileUtil\npublic section')
 s=s.replace('namespace Lean.Meta.Sym.Arith','namespace Lean.Meta.Sym.Arith.JacobiProfile'+name+'\nopen JacobiProfileUtil')
 s=s.replace('end Lean.Meta.Sym.Arith','end Lean.Meta.Sym.Arith.JacobiProfile'+name)
 s=s.replace('private def moduleVar (e : Expr) : ModuleM Grind.Linarith.Expr := do','private def moduleVar (e : Expr) : ModuleM Grind.Linarith.Expr := timed "atom lookup" do')
 if name=='Current':
  s=s.replace('private def matchesFn (e fn : Expr) (arity : Nat) : ModuleM Bool := do','private def matchesFn (e fn : Expr) (arity : Nat) : ModuleM Bool := timed "operation matching" do')
 else:
  s=s.replace('withReducibleAndInstances <| isDefEq (e.getBoundedAppFn arity) fn','timed "operation matching" <| withReducibleAndInstances <| isDefEq (e.getBoundedAppFn arity) fn')
  s=s.replace('  let ctx := { ctx with\n','  let ctx ← timed "context canonicalization" do\n    return { ctx with\n',1)
 s=s.replace('private def ModuleContext.canon (ctx : ModuleContext) : SymM ModuleContext := do','private def ModuleContext.canon (ctx : ModuleContext) : SymM ModuleContext := timed "context canonicalization" do')
 s=s.replace('private def getModule? (type : Expr) : SymM (Option (ModuleContext × Expr × Level × Bool)) := do','private def getModule? (type : Expr) : SymM (Option (ModuleContext × Expr × Level × Bool)) := timed "module context" do')
 s=s.replace('(ctx : ModuleContext) (vars : Array Expr) (lhs rhs : Grind.Linarith.Expr) : MetaM Expr := do','(ctx : ModuleContext) (vars : Array Expr) (lhs rhs : Grind.Linarith.Expr) : MetaM Expr := timed "certificate construction" do')
 s=s.replace('let e ← shareCommon e','let e ← timed "input sharing" <| shareCommon e')
 s=s.replace('← ((do return (← reifyModule lhs, ← reifyModule rhs)', '← timed "reification" <| ((do return (← reifyModule lhs, ← reifyModule rhs)')
 s=s.replace('← (((do return (← reifyModule lhs\', ← reifyModule rhs\')', '← timed "reification" <| (((do return (← reifyModule lhs\', ← reifyModule rhs\')')
 s=s.replace('let equal := if integers then lhs.norm == rhs.norm else lhs.toPolyN == rhs.toPolyN','let equal ← timedPure "polynomial normalization" fun () => if integers then lhs.norm == rhs.norm else lhs.toPolyN == rhs.toPolyN')
 s=s.replace('let equal := if integers then lhsRe.norm == rhsRe.norm else lhsRe.toPolyN == rhsRe.toPolyN','let equal ← timedPure "polynomial normalization" fun () => if integers then lhsRe.norm == rhsRe.norm else lhsRe.toPolyN == rhsRe.toPolyN')
 s=s.replace('← visitModuleAtoms integers simpAtom lhs','← timed "atom callback traversal" <| visitModuleAtoms integers simpAtom lhs')
 s=s.replace('← visitModuleAtoms integers simpAtom rhs','← timed "atom callback traversal" <| visitModuleAtoms integers simpAtom rhs')
 s=s.replace('← shareCommon (rl.getResultExpr lhs)','← timed "callback output sharing" <| shareCommon (rl.getResultExpr lhs)')
 s=s.replace('← shareCommon (rr.getResultExpr rhs)','← timed "callback output sharing" <| shareCommon (rr.getResultExpr rhs)')
 Path('JacobiModule'+name+'Profile.lean').write_text(s)
