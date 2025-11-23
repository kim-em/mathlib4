/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Lean.Task.Basic
import Init.Data.Iterators
import Batteries.Lean.System.IO

/-!
# Iterator-based parallelization for Lean's tactic monads.

This file provides iterator-based versions of the parallel execution utilities,
using the new Iterator framework instead of MLList.

The main functions are:
- `IO.iterTasks` - Creates an iterator over tasks that yields results in completion order
- `CoreM.runIteratively`, `MetaM.runIteratively`, etc. - Run monadic computations in parallel,
  returning an iterator that yields results as they complete

Unlike the MLList-based `runGreedily`, these functions:
- Use the modern Iterator framework from Lean 4
- Integrate with standard iterator combinators (map, filter, etc.)
- Support iterator consumers like `.forEach`, etc.

Note: These iterators do not have `Finite` instances, as we cannot prove termination
from the available information about `IO.waitAny'`. In practice, they will terminate
if all tasks eventually complete. For consumers that require `Finite` (like `.toList`),
you'll need to use `.allowNontermination.toList`.

## Example usage

```lean
-- Run multiple MetaM computations in parallel, process results as they complete
let jobs : List (MetaM Result) := [job1, job2, job3]
let iter ← MetaM.runIteratively jobs
for result in iter do
  processResult result
```

## Implementation notes

The iterator uses `IO.waitAny'` internally to wait for task completion in order.
Like the MLList-based version, tasks must call `IO.checkCanceled` for cooperative cancellation.

For cancellation support, use the Task-level API directly:
```lean
let (cancels, tasks) ← jobs.mapM asTask
let iter := IO.iterTasks tasks
-- Use iter...
-- Cancel remaining tasks:
cancels.forM id
```
-/

set_option autoImplicit true

namespace Std.Iterators

/--
Internal state for an iterator over tasks.
Maintains the list of tasks that haven't completed yet.
-/
structure TaskIterator (α : Type w) where
  tasks : List (Task α)

end Std.Iterators

namespace IO

open Std.Iterators

/--
Creates an iterator over a list of tasks that yields results in completion order.

Uses `IO.waitAny'` to wait for the next task to complete (whichever finishes first),
then yields that result and continues with the remaining tasks.

The iterator will terminate once all tasks have completed, but we don't provide a `Finite`
instance since we cannot prove termination from the available information.
In practice, if all tasks eventually complete, the iterator will be finite.

## Example
```lean
let tasks : List (Task Nat) ← [
  IO.asTask (pure 1),
  IO.asTask (pure 2),
  IO.asTask (pure 3)
]
let iter := IO.iterTasks tasks
for result in iter do
  IO.println s!"Got result: {result}"
```
-/
def iterTasks {α : Type} (tasks : List (Task α)) : IterM (α := TaskIterator α) BaseIO α :=
  Std.Iterators.toIterM { tasks } BaseIO α

instance {α : Type} : Iterator (TaskIterator α) BaseIO α where
  IsPlausibleStep it
    | .yield it' out => True
    | .skip _ => False
    | .done => it.internalState.tasks = []
  step it := do
    match h : it.internalState.tasks with
    | [] =>
        pure <| .deflate ⟨.done, rfl⟩
    | task :: rest =>
        have hlen : 0 < (task :: rest).length := by simp
        let (result, remaining) ← IO.waitAny' (task :: rest) hlen
        pure <| .deflate ⟨
          .yield (Std.Iterators.toIterM { tasks := remaining } BaseIO α) result,
          trivial⟩

/--
Iterator-based version of `IO.runGreedily`.

Given a list of IO computations, executes them all in parallel as tasks,
and returns an iterator that yields values in completion order.

Unlike `runGreedily`, this doesn't provide a cancellation hook.
For cancellation, create the tasks explicitly and cancel them after using the iterator.

Note: Task errors will cause panics when the task result is accessed.
For proper error handling, use the Task-based API directly.
-/
def runIteratively {α : Type} [Inhabited α] (jobs : List (IO α)) : BaseIO (IterM (α := TaskIterator α) BaseIO α) := do
  let tasks ← jobs.mapM fun job => do
    let task ← IO.asTask job
    -- Convert Task (Except Error α) to Task α by forcing the Except
    -- Errors will panic when the task is accessed
    return task.map (prio := .max) fun
      | .ok a => a
      | .error e => panic! s!"Task failed: {e}"
  return iterTasks tasks

end IO

namespace Lean.Core.CoreM

open Std.Iterators

/--
Iterator-based version of `CoreM.runGreedily`.

Runs a list of CoreM computations in parallel and returns an iterator
that yields results in completion order.

The iterator runs in CoreM, and as it yields each result, it updates the CoreM state
to reflect the state when that particular task completed. This means the state is
threaded through the iteration in task completion order.

The iterator will terminate after all jobs complete (assuming they all do complete).
-/
def runIteratively {α : Type} (jobs : List (CoreM α)) :=
  jobs.mapM asTask' >>= fun tasks =>
  let baseIter := IO.iterTasks tasks
  -- mapM lifts to CoreM and executes each action to thread state
  pure (baseIter.mapM id)

end Lean.Core.CoreM

namespace Lean.Meta.MetaM

open Std.Iterators

/--
Iterator-based version of `MetaM.runGreedily`.

Runs a list of MetaM computations in parallel and returns an iterator
that yields results in completion order.

The iterator runs in MetaM, and as it yields each result, it updates the MetaM state
to reflect the state when that particular task completed. This means the state is
threaded through the iteration in task completion order.

The iterator will terminate after all jobs complete (assuming they all do complete).
-/
def runIteratively {α : Type} (jobs : List (MetaM α)) :=
  jobs.mapM asTask' >>= fun tasks =>
  let baseIter := IO.iterTasks tasks
  -- mapM lifts to MetaM and executes each action to thread state
  pure (baseIter.mapM id)

end Lean.Meta.MetaM

namespace Lean.Elab.Term.TermElabM

open Std.Iterators

/--
Iterator-based version of `TermElabM.runGreedily`.

Runs a list of TermElabM computations in parallel and returns an iterator
that yields results in completion order.

The iterator runs in TermElabM, and as it yields each result, it updates the TermElabM state
to reflect the state when that particular task completed. This means the state is
threaded through the iteration in task completion order.

The iterator will terminate after all jobs complete (assuming they all do complete).
-/
def runIteratively {α : Type} (jobs : List (TermElabM α)) :=
  jobs.mapM asTask' >>= fun tasks =>
  let baseIter := IO.iterTasks tasks
  -- mapM lifts to TermElabM and executes each action to thread state
  pure (baseIter.mapM id)

end Lean.Elab.Term.TermElabM

namespace Lean.Elab.Tactic.TacticM

open Std.Iterators

/--
Iterator-based version of `TacticM.runGreedily`.

Runs a list of TacticM computations in parallel and returns an iterator
that yields results in completion order.

The iterator runs in TacticM, and as it yields each result, it updates the TacticM state
to reflect the state when that particular task completed. This means the state is
threaded through the iteration in task completion order.

The iterator will terminate after all jobs complete (assuming they all do complete).
-/
def runIteratively {α : Type} (jobs : List (TacticM α)) :=
  jobs.mapM asTask' >>= fun tasks =>
  let baseIter := IO.iterTasks tasks
  -- mapM lifts to TacticM and executes each action to thread state
  pure (baseIter.mapM id)

end Lean.Elab.Tactic.TacticM
