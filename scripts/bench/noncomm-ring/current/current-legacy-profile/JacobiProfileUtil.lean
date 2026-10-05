module
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
