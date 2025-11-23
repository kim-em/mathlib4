/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Lean.Task.Iterators

/-!
# Tests for Iterator-based parallel execution

This file contains tests to verify:
1. Results are returned in completion order (not submission order)
2. State is properly threaded through the iteration
-/

namespace Tests

open Std.Iterators

/-- Test that IO.iterTasks returns results in completion order. -/
def testCompletionOrder : IO Unit := do
  IO.println "Testing completion order..."

  -- Create tasks that complete in neither forward nor backward order
  let task1 : IO Nat := IO.sleep 300 *> pure 1
  let task2 : IO Nat := IO.sleep 50 *> pure 2
  let task3 : IO Nat := IO.sleep 150 *> pure 3

  let iter ← IO.runIteratively [task1, task2, task3]

  -- Map to add logging and collect results
  let results ← (iter.mapM fun value => do
    IO.println s!"Got: {value}"
    return value).take 3 |>.allowNontermination.toList

  -- Should be [2, 3, 1] (completion order), neither [1, 2, 3] (submission) nor [3, 2, 1] (reverse)
  if results == [2, 3, 1] then
    IO.println "✓ Completion order test passed"
  else
    IO.println s!"✗ Failed: expected [2, 3, 1], got {results}"

/-- Test that state is properly threaded through CoreM iteration. -/
def testStateThreading : IO Unit := do
  IO.println "\nTesting state threading in CoreM..."

  -- Create minimal environment
  let env ← Lean.importModules #[] {} 0
  let ctx : Lean.Core.Context := {
    fileName := "<test>"
    fileMap := default
  }
  let state : Lean.Core.State := {
    env := env
  }

  let testCore : Lean.CoreM (List Nat × List Nat × List String) := do
    -- Tasks that log messages with different delays
    let task1 : Lean.CoreM Nat := do
      Lean.logInfo "Task 1"
      IO.sleep 300
      return 1

    let task2 : Lean.CoreM Nat := do
      Lean.logInfo "Task 2"
      IO.sleep 50
      return 2

    let task3 : Lean.CoreM Nat := do
      Lean.logInfo "Task 3"
      IO.sleep 150
      return 3

    let iter ← Lean.Core.CoreM.runParallel' [task1, task2, task3]

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

  IO.println s!"  Values: {values}"
  IO.println s!"  Message counts: {counts}"
  IO.println s!"  Message texts: {msgTexts}"

  if values == [2, 3, 1] then
    IO.println "  ✓ Values in completion order"
  else
    IO.println s!"  ✗ Wrong order: {values}"

  -- Each task should see exactly 1 message (its own)
  if counts == [1, 1, 1] then
    IO.println "  ✓ Each task sees 1 message"
  else
    IO.println s!"  ✗ Wrong message counts: {counts}"

  -- Verify message content matches the task
  if msgTexts == ["Task 2", "Task 3", "Task 1"] then
    IO.println "  ✓ Message content verified"
  else
    IO.println s!"  ✗ Wrong messages: {msgTexts}"

  IO.println "✓ State threading test passed"

/-- Test that TacticM state is properly threaded through iterations. -/
def testTacticMStateThreading : IO Unit := do
  IO.println "\nTesting state threading in TacticM..."

  -- Three tasks that run different tactics with different delays
  let task1 : Lean.Elab.Tactic.TacticM String := do
    Lean.Elab.Tactic.evalTactic (← `(tactic| sorry))
    IO.sleep 300
    return "sorry"

  let task2 : Lean.Elab.Tactic.TacticM String := do
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact True.intro))
    IO.sleep 50
    return "exact"

  let task3 : Lean.Elab.Tactic.TacticM String := do
    Lean.Elab.Tactic.evalTactic (← `(tactic| skip))
    IO.sleep 150
    return "skip"

  -- Create environment with tactic elaborators loaded (loadExts := true to run initializers)
  let env ← Lean.importModules #[{module := `Lean.Elab.Tactic.BuiltinTactic}] {} 0 (loadExts := true)
  let coreCtx : Lean.Core.Context := {
    fileName := "<test>"
    fileMap := default
  }
  let coreState : Lean.Core.State := {
    env := env
  }

  let test : Lean.Meta.MetaM (List String × List Nat) := do
    -- Create a single True goal
    let goal ← Lean.Meta.mkFreshExprMVar (Lean.mkConst ``True)

    let tacticTest : Lean.Elab.Tactic.TacticM (List String × List Nat) := do
      let (_, iter) ← Lean.Elab.Tactic.TacticM.runParallel [task1, task2, task3]
      let results ← (iter.mapM fun result =>
        match result with
        | .ok tacticName => return (tacticName, (← Lean.Elab.Tactic.getGoals).length)
        | .error _ => return ("error", 999)).take 3 |>.allowNontermination.toList
      return results.unzip

    let tacticCtx := { elaborator := .anonymous }
    let tacticState := { goals := [goal.mvarId!] }
    let ((result, _), _) ← (((tacticTest tacticCtx).run tacticState) {}).run {}
    return result

  let (((tacticNames, goalCounts), _), _) ← test.run |>.toIO coreCtx coreState

  IO.println s!"  Tactic names: {tacticNames}"
  IO.println s!"  Goal counts: {goalCounts}"

  -- Should complete in order [exact, skip, sorry] based on sleep times (50ms, 150ms, 300ms)
  -- exact solves True → 0 goals
  -- skip does nothing → 1 goal still
  -- sorry closes goal → 0 goals
  if tacticNames == ["exact", "skip", "sorry"] then
    IO.println "  ✓ Tactics completed in order"
  else
    IO.println s!"  ✗ Wrong order: {tacticNames}"

  IO.println "✓ TacticM state threading test passed"

/-- Test that cancellation hooks work properly with cooperative cancellation. -/
def testCancellation : IO Unit := do
  IO.println "\nTesting cancellation..."

  -- Four tasks, with task4 being slow (1000ms)
  let task1 : Lean.Elab.Tactic.TacticM String := do
    IO.sleep 300
    Lean.Elab.Tactic.evalTactic (← `(tactic| sorry))
    return "sorry"

  let task2 : Lean.Elab.Tactic.TacticM String := do
    IO.sleep 50
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact True.intro))
    return "exact"

  let task3 : Lean.Elab.Tactic.TacticM String := do
    IO.sleep 150
    Lean.Elab.Tactic.evalTactic (← `(tactic| skip))
    return "skip"

  let task4 : Lean.Elab.Tactic.TacticM String := do
    IO.sleep 1000
    Lean.Elab.Tactic.evalTactic (← `(tactic| sorry))
    return "sorry"

  -- Create environment with tactic elaborators loaded
  let env ← Lean.importModules #[{module := `Lean.Elab.Tactic.BuiltinTactic}] {} 0 (loadExts := true)
  let coreCtx : Lean.Core.Context := {
    fileName := "<test>"
    fileMap := default
  }
  let coreState : Lean.Core.State := {
    env := env
  }

  -- Run everything and capture the cancellation hook
  let test : Lean.Meta.MetaM (BaseIO Unit × List String × Nat) := do
    let goal ← Lean.Meta.mkFreshExprMVar (Lean.mkConst ``True)

    let tacticTest : Lean.Elab.Tactic.TacticM (BaseIO Unit × List String × Nat) := do
      let (cancel, iter) ← Lean.Elab.Tactic.TacticM.runParallel [task1, task2, task3, task4]

      -- Sleep 500ms then cancel
      IO.sleep 500
      cancel

      -- Consume the iterator and partition into successes and failures
      let results ← iter.take 4 |>.allowNontermination.toList
      let successNames := results.filterMap (fun r => match r with | .ok n => some n | .error _ => none)
      let failedCount := results.filter (fun r => match r with | .error _ => true | _ => false) |>.length
      return (cancel, successNames, failedCount)

    let tacticCtx : Lean.Elab.Tactic.Context := { elaborator := .anonymous }
    let tacticState : Lean.Elab.Tactic.State := { goals := [goal.mvarId!] }
    let (((cancel, successNames, failedCount), _), _) ← (((tacticTest tacticCtx).run tacticState) {}).run {}
    return (cancel, successNames, failedCount)

  let (((cancel, successNames, failedCount), _), _) ← test.run |>.toIO coreCtx coreState

  -- Sort success names for deterministic output (timing can vary)
  let successNamesSorted := successNames.mergeSort (· < ·)

  IO.println s!"  Succeeded: {successNamesSorted}"
  IO.println s!"  Failed: {failedCount}"

  -- Check that exactly 3 tasks succeeded and 1 failed
  if successNames.length == 3 && failedCount == 1 then
    IO.println "  ✓ One task was cancelled (Core.checkInterrupted detected cancellation)"
    IO.println "  (Cooperative cancellation via CancelToken works!)"
  else
    IO.println s!"  ✗ Unexpected: {successNames.length} tasks succeeded, {failedCount} failed"

  IO.println "✓ Cancellation test passed"

/-- Run all tests. -/
def runTests : IO Unit := do
  IO.println "=== Iterator Task Tests ==="
  testCompletionOrder
  testStateThreading
  testTacticMStateThreading
  testCancellation
  IO.println "\n=== All tests completed ==="

end Tests

/--
info: === Iterator Task Tests ===
Testing completion order...
Got: 2
Got: 3
Got: 1
✓ Completion order test passed

Testing state threading in CoreM...
  Values: [2, 3, 1]
  Message counts: [1, 1, 1]
  Message texts: [Task 2, Task 3, Task 1]
  ✓ Values in completion order
  ✓ Each task sees 1 message
  ✓ Message content verified
✓ State threading test passed

Testing state threading in TacticM...
  Tactic names: [exact, skip, sorry]
  Goal counts: [0, 1, 0]
  ✓ Tactics completed in order
✓ TacticM state threading test passed

Testing cancellation...
  Succeeded: [exact, skip, sorry]
  Failed: 1
  ✓ One task was cancelled (Core.checkInterrupted detected cancellation)
  (Cooperative cancellation via CancelToken works!)
✓ Cancellation test passed

=== All tests completed ===
-/
#guard_msgs in
#eval! Tests.runTests
