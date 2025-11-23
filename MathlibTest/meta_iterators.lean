/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Lean.Task.Iterators

/-!
# Tests for Iterator-based parallel execution

Tests for `Mathlib.Lean.Task.Iterators`, verifying:
- Tasks complete in parallel and results are returned in completion order
- State is properly threaded through CoreM/MetaM/TacticM iterations
- Cancellation hooks work with cooperative cancellation via `CancelToken`
-/

open Std.Iterators

/-- Create a test environment with the given imports. -/
def mkCoreState (imports : Array Lean.Import) (loadExts : Bool := false) :
    IO (Lean.Core.Context × Lean.Core.State) := do
  let env ← Lean.importModules imports {} 0 (loadExts := loadExts)
  return (
    { fileName := "<test>", fileMap := default },
    { env := env }
  )

/-- Run a TacticM test with a fresh True goal. -/
def runTacticTest {α : Type} (test : Lean.Elab.Tactic.TacticM α) : IO α := do
  let (coreCtx, coreState) ← mkCoreState #[{module := `Init}] (loadExts := true)
  let (result, _) ← (do
    let goal ← Lean.Meta.mkFreshExprMVar (Lean.mkConst ``True)
    (((test { elaborator := .anonymous }).run' { goals := [goal.mvarId!] }) {}).run' {}).run' |>.toIO coreCtx coreState
  return result

/-- Create a tactic task: sleep, run tactic, return name. -/
def mkTacticTask (sleepMs : Nat) (tacticStx : Lean.Syntax) (name : String) :
    Lean.Elab.Tactic.TacticM String := do
  IO.sleep sleepMs.toUInt32
  Lean.Elab.Tactic.evalTactic tacticStx
  return name

/-- Test that IO.iterTasks returns results in completion order. -/
def testCompletionOrder : IO Unit := do
  let iter ← IO.runParallel' [
    IO.sleep 300 *> pure 1,
    IO.sleep 50 *> pure 2,
    IO.sleep 150 *> pure 3
  ]

  let results ← iter.take 3 |>.allowNontermination.toList
  -- Extract successful results
  IO.println s!"{results.filterMap (·.toOption)}"

/-- info: [2, 3, 1] -/
#guard_msgs in
#eval! testCompletionOrder

/-- Test that state is properly threaded through CoreM iteration. -/
def testStateThreading : IO Unit := do
  let (ctx, state) ← mkCoreState #[]

  let testCore : Lean.CoreM (List Nat × List Nat × List String) := do
    -- Tasks that log messages with different delays
    let iter ← Lean.Core.CoreM.runParallel' [
      do Lean.logInfo "Task 1"; IO.sleep 300; return 1,
      do Lean.logInfo "Task 2"; IO.sleep  50; return 2,
      do Lean.logInfo "Task 3"; IO.sleep 150; return 3
    ]

    -- Map to capture state after each task and collect results
    let results ← (iter.mapM fun result => do
      match result with
      | .ok value =>
        let messages ← Lean.Core.getMessageLog
        let msgs := messages.toList
        let count := msgs.length
        -- Get the message text
        let msgText ← msgs.headD default |>.data.toString
        return (value, count, msgText)
      | .error _ =>
        return (0, 0, "error")).take 3 |>.allowNontermination.toList

    return (results.map (·.1), results.map (·.2.1), results.map (·.2.2))

  let ((values, counts, msgTexts), _) ← testCore.toIO ctx state

  IO.println s!"Values: {values}"
  IO.println s!"Message counts: {counts}"
  IO.println s!"Message texts: {msgTexts}"

/--
info: Values: [2, 3, 1]
Message counts: [1, 1, 1]
Message texts: [Task 2, Task 3, Task 1]
-/
#guard_msgs in
#eval! testStateThreading

/-- Test that TacticM state is properly threaded through iterations. -/
def testTacticMStateThreading : IO Unit := do
  let tacticTest : Lean.Elab.Tactic.TacticM (List String × List Nat) := do
    let tasks := [
      mkTacticTask 300 (← `(tactic| sorry)) "sorry",
      mkTacticTask 50 (← `(tactic| exact True.intro)) "exact",
      mkTacticTask 150 (← `(tactic| skip)) "skip"
    ]
    let (_, iter) ← Lean.Elab.Tactic.TacticM.runParallel tasks
    let results ← (iter.mapM fun result =>
      match result with
      | .ok tacticName => return (tacticName, (← Lean.Elab.Tactic.getGoals).length)
      | .error _ => return ("error", 999)).take 3 |>.allowNontermination.toList
    return results.unzip

  let (tacticNames, goalCounts) ← runTacticTest tacticTest

  IO.println s!"Tactic names: {tacticNames}"
  IO.println s!"Goal counts: {goalCounts}"

/--
info: Tactic names: [exact, skip, sorry]
Goal counts: [0, 1, 0]
-/
#guard_msgs in
#eval! testTacticMStateThreading

/-- Test that cancellation hooks work properly with cooperative cancellation. -/
def testCancellation : IO Unit := do
  let tacticTest : Lean.Elab.Tactic.TacticM (List String × Nat) := do
    let tasks := [
      mkTacticTask 300  (← `(tactic| sorry)) "sorry",
      mkTacticTask 50   (← `(tactic| exact True.intro)) "exact",
      mkTacticTask 150  (← `(tactic| skip)) "skip",
      mkTacticTask 1000 (← `(tactic| sorry)) "sorry-slow"
    ]
    let (cancel, iter) ← Lean.Elab.Tactic.TacticM.runParallel tasks

    -- Cancel after 500ms (task4 will still be sleeping)
    IO.sleep 500
    cancel

    -- Consume the iterator and partition into successes and failures
    let results ← iter.take 4 |>.allowNontermination.toList
    let successNames := results.filterMap fun r => match r with | .ok n => some n | .error _ => none
    let failedCount := results.countP fun r => match r with | .error _ => true | _ => false
    return (successNames, failedCount)

  let (successNames, failedCount) ← runTacticTest tacticTest

  -- Sort for deterministic output (timing can vary)
  IO.println s!"Succeeded: {successNames.mergeSort (· < ·)}"
  IO.println s!"Failed: {failedCount}"

/--
info: Succeeded: [exact, skip, sorry]
Failed: 1
-/
#guard_msgs in
#eval! testCancellation
