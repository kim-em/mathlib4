module
public import JacobiCurrentNoncommRing
public import JacobiOldNoncommRing
public meta import Lean.Elab.Tactic
public meta section
open Lean Meta Elab Tactic
set_option maxHeartbeats 0
set_option maxRecDepth 4096
elab "jacobi_paired" : tactic => do
  let saved ← saveState
  let a ← `(tactic| jacobi_old_noncomm_ring)
  let b ← `(tactic| jacobi_current_noncomm_ring)
  let trial (tac : TSyntax `tactic) := do
    saved.restore
    evalTactic tac
    unless (← getUnsolvedGoals).isEmpty do throwError "unexpected residual goals"
  let mut rows := #[]
  for pair in [:4] do
    let arms := if pair % 2 == 0 then #["A", "B"] else #["B", "A"]
    for arm in arms do
      let tac := if arm == "A" then a else b
      for _ in [:3] do trial tac
      let start ← IO.monoNanosNow
      for _ in [:50] do trial tac
      let elapsed := (← IO.monoNanosNow) - start
      rows := rows.push (pair+1, arm, elapsed)
  saved.restore
  for (pair, arm, ns) in rows do logInfo m!"JACOBI_BENCH {pair} {arm} 50 {ns}"
  evalTactic b
