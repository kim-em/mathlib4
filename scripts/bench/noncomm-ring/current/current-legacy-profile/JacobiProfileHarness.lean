module
public import JacobiHarness
public import JacobiProfileUtil
public meta import JacobiModuleLegacyProfile
public meta import JacobiModuleCurrentProfile
public meta section
open Lean Meta Elab Tactic Sym JacobiProfileUtil
set_option maxHeartbeats 0
set_option maxRecDepth 4096
elab "jacobi_profile_phase " label:str tac:tactic : tactic => timed label.getString <| evalTactic tac
elab "jacobi_profile_module " arm:str : tactic => liftMetaTactic1 fun g => SymM.run do
  let target ← instantiateMVars (← g.getType)
  let proof? ← if arm.getString == "legacy" then
    Arith.JacobiProfileLegacy.proveAddEq? target
  else Arith.JacobiProfileCurrent.proveAddEq? target
  let some proof := proof? | throwError "profile backend did not close target"
  timed "proof assignment" <| g.assign proof
  return none
elab "jacobi_profile_paired" : tactic => do
  let saved ← saveState
  let frontend ← `(tactic|
    jacobi_profile_phase "frontend" (first
      | simp only [add_mul, mul_add, sub_eq_add_neg, mul_assoc, pow_one, pow_zero, pow_succ,
          one_mul, mul_one, zero_mul, mul_zero,
          Mathlib.Tactic.JacobiCurrentNoncommRing.nat_lit_mul_eq_nsmul,
          Mathlib.Tactic.JacobiCurrentNoncommRing.mul_nat_lit_eq_nsmul,
          mul_smul_comm, smul_mul_assoc, neg_mul, mul_neg]
      | fail "simp failed"))
  let old ← `(tactic| $frontend <;> jacobi_profile_phase "backend" (first | jacobi_old_abel1 | jacobi_old_abel_nf))
  let legacy ← `(tactic| $frontend <;> jacobi_profile_phase "backend" (jacobi_profile_module "legacy") <;> try rfl)
  let current ← `(tactic| $frontend <;> jacobi_profile_phase "backend" (jacobi_profile_module "current") <;> try rfl)
  let mut rows := #[]
  for pair in [:4] do
    for comparison in #["abel", "legacy"] do
      let arms := if pair % 2 == 0 then #["A", "B"] else #["B", "A"]
      for arm in arms do
        let tac := if arm == "B" then current else if comparison == "abel" then old else legacy
        for _ in [:3] do
          saved.restore
          evalTactic tac
        counters.set #[]
        for _ in [:50] do
          timed "goal restoration" saved.restore
          timed "total without restoration" <| evalTactic tac
          unless (← getUnsolvedGoals).isEmpty do throwError "unexpected residual goals"
        rows := rows.push (comparison, pair+1, arm, ← counters.get)
  saved.restore
  for (comparison, pair, arm, entries) in rows do
    for (stage, count, ns) in entries do
      logInfo m!"JACOBI_PROFILE {comparison} {pair} {arm} {stage} {count} {ns}"
  evalTactic (← `(tactic| jacobi_current_noncomm_ring))
