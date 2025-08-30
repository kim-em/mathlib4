/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Elab.Tactic.Basic

set_option autoImplicit true

namespace Lean.Core.CoreM

/--
Given a monadic value in `CoreM`, creates a task that runs it in the current state,
returning
* a cancellation hook and
* a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : CoreM α) : CoreM (BaseIO Unit × Task (CoreM α)) := do
  let task ← (t.toIO (← read) (← get)).asTask
  return (IO.cancel task, task.map (prio := .max) fun
  | .ok (a, s) => do set s; pure a
  | .error e => throwError m!"Task failed:\n{e}")

/--
Given a monadic value in `CoreM`, creates a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask' (t : CoreM α) : CoreM (Task (CoreM α)) := (·.2) <$> asTask t

end Lean.Core.CoreM

namespace Lean.Meta.MetaM

/--
Given a monadic value in `MetaM`, creates a task that runs it in the current state,
returning
* a cancellation hook and
* a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : MetaM α) : MetaM (BaseIO Unit × Task (MetaM α)) := do
  let (cancel, task) ← (t.run (← read) (← get)).asTask
  return (cancel, task.map (prio := .max)
    fun c : CoreM (α × Meta.State) => do let (a, s) ← c; set s; pure a)

/--
Given a monadic value in `MetaM`, creates a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask' (t : MetaM α) : MetaM (Task (MetaM α)) := (·.2) <$> asTask t

end Lean.Meta.MetaM

namespace Lean.Elab.Term.TermElabM

/--
Given a monadic value in `TermElabM`, creates a task that runs it in the current state,
returning
* a cancellation hook and
* a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : TermElabM α) : TermElabM (BaseIO Unit × Task (TermElabM α)) := do
  let (cancel, task) ← (t.run (← read) (← get)).asTask
  return (cancel, task.map (prio := .max)
    fun c : MetaM (α × Term.State) => do let (a, s) ← c; set s; pure a)

/--
Given a monadic value in `TermElabM`, creates a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask' (t : TermElabM α) : TermElabM (Task (TermElabM α)) := (·.2) <$> asTask t

end Lean.Elab.Term.TermElabM

namespace Lean.Elab.Tactic.TacticM

/--
Given a monadic value in `TacticM`, creates a task that runs it in the current state,
returning
* a cancellation hook and
* a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask (t : TacticM α) : TacticM (BaseIO Unit × Task (TacticM α)) := do
  let (cancel, task) ← (t (← read) |>.run (← get)).asTask
  return (cancel, task.map (prio := .max)
    fun c : TermElabM (α × Tactic.State) => do let (a, s) ← c; set s; pure a)

/--
Given a monadic value in `TacticM`, creates a task that runs it in the current state,
returning a monadic value with the cached result (and subsequent state as it was after running).
-/
def asTask' (t : TacticM α) : TacticM (Task (TacticM α)) := (·.2) <$> asTask t

end Lean.Elab.Tactic.TacticM
