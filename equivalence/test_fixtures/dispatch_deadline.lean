import Equivalence.Solver

/-! Verify dispatch cancellation during either check-sat or model retrieval,
then check that the next query can still run. -/
open Lean Equivalence

run_elab do
  let modelBlock := (← IO.getEnv "UPLC_TEST_Z3_DEFAULT_MODE") == some "block-model"
  let jobs := ((← IO.getEnv "UPLC_TEST_SOLVER_JOBS").bind String.toNat?).getD 1
  let elaborate := fun (term : TSyntax `term) => do
    let goal ← Lean.Elab.Term.elabTerm term (some (mkSort .zero))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars goal
  let goal ← elaborate (← `(∀ n : Int, n * n ≠ 2))
  let blockedGoal ← if modelBlock then elaborate (← `(∀ n : Int, n * n ≠ 4)) else pure goal
  let diagnostics ← IO.mkRef (#[] : Array (String × Json))
  let first ← Solver.runQueryTimed (← getEnv) (pure blockedGoal) "blocked" 5 2 (some diagnostics) {} jobs none
  unless first.isNone do throwError "Blocked dispatch solver did not time out"
  let entries ← diagnostics.get
  unless entries.any (fun (_,d) => (d.getObjValAs? String "phase").toOption == some "z3" &&
      (d.getObjValAs? String "status").toOption == some "case_timeout") do
    throwError "Test did not reach the solver before cancellation"
  let second ← Solver.runQueryTimed (← getEnv) (pure goal) "recovery" 5 5 none {} 1 (some 1)
  unless second.isSome do throwError "Case cancellation affected the next query"
  IO.println "dispatch deadline recovered"
