module
public import JacobiHarness
public meta section
open Lean Meta Elab Tactic
set_option maxHeartbeats 0
set_option maxRecDepth 4096
elab "jacobi_kernel_paired" : tactic => do
  let saved ← saveState
  let a ← `(tactic| jacobi_old_noncomm_ring)
  let b ← `(tactic| jacobi_current_noncomm_ring)
  let trial (tac : TSyntax `tactic) := do
    saved.restore
    let g ← getMainGoal
    let target ← g.getType
    evalTactic tac
    unless (← getUnsolvedGoals).isEmpty do throwError "unexpected residual goals"
    g.withContext do
      let proof ← instantiateMVars (mkMVar g)
      let start ← IO.monoNanosNow
      let _ ← Lean.Meta.mkAuxTheorem target proof (zetaDelta := true) (kind? := `_jacobi_check)
      return (← IO.monoNanosNow) - start
  let mut rows := #[]
  for pair in [:4] do
    let arms := if pair % 2 == 0 then #["A", "B"] else #["B", "A"]
    for arm in arms do
      let tac := if arm == "A" then a else b
      for _ in [:3] do let _ ← trial tac
      let mut kernelNs := 0
      let start ← IO.monoNanosNow
      for _ in [:50] do kernelNs := kernelNs + (← trial tac)
      let elapsed := (← IO.monoNanosNow) - start
      rows := rows.push (pair+1, arm, elapsed, kernelNs)
  saved.restore
  for (pair, arm, ns, kernelNs) in rows do
    logInfo m!"JACOBI_KERNEL {pair} {arm} 50 {ns} {kernelNs}"
  evalTactic b
