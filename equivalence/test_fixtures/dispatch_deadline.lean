import Equivalence.Solver

/-! Used with the test-only Z3 proxy: the unseeded worker blocks, while the
seeded worker runs real Z3. Verify cancellation, process cleanup and recovery. -/
open Lean Equivalence

run_elab do
  let goal ← Lean.Elab.Term.elabTerm (← `(∀ n : Int, n * n ≠ 2)) (some (mkSort .zero))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let goal ← instantiateMVars goal
  let diagnostics ← IO.mkRef (#[] : Array (String × Json))
  let first ← Solver.runQueryTimed (← getEnv) goal "blocked" 5 2 (some diagnostics) {} 1 none
  unless first.isNone do throwError "Blocked dispatch solver did not time out"
  let entries ← diagnostics.get
  unless entries.any (fun (_,d) => (d.getObjValAs? String "phase").toOption == some "z3" &&
      (d.getObjValAs? String "status").toOption == some "case_timeout") do
    throwError "Test did not reach the solver before cancellation"
  let second ← Solver.runQueryTimed (← getEnv) goal "recovery" 5 5 none {} 1 (some 1)
  unless second.isSome do throwError "Case cancellation affected the next query"
  IO.println "dispatch deadline recovered"
