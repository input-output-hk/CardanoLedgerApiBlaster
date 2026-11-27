import Equivalence.Checker
import Tests.Equivalence.Support

namespace Tests.Equivalence.Checker

open Lean _root_.Equivalence

-- This test imports no CLI and passes decoded programs directly to the API.
#eval show IO Unit from Tests.Equivalence.Support.withSolverLock do
  let decode := fun term => IO.ofExcept
    (PlutusCore.UPLC.TextEncoding.programFromString s!"(program 1.1.0 {term})")
  let old ← decode "(lam c (con unit ()))"
  let new ← decode (Tests.Equivalence.Support.rejectDataAt [2, 1, 0] "I 42")
  let phases ← IO.mkRef (#[] : Array Solver.Phase)
  let settings : _root_.Equivalence.Checker.Config := {
    maxInputs := 1, maxOutputs := 1, maxSigners := 1, bounded := true, steps := 100, timeout := 60 }
  let result ← _root_.Equivalence.Checker.check settings old new {
    phase := fun phase => phases.modify (·.push phase) }
  unless (result.getObjValAs? String "verdict").toOption == some "bounded_regression" do
    throw <| IO.userError result.pretty
  let witness ← IO.ofExcept (result.getObjVal? "counterexample")
  unless (witness.getObjValAs? Bool "replayed").toOption == some true do
    throw <| IO.userError "Library counterexample was not replayed"
  unless (← phases.get).any (fun phase => phase.phase == "z3" &&
      phase.query == some "acceptance_preserved") do
    throw <| IO.userError "Library observer did not receive the solving phase"
  let observed ← phases.get
  unless observed.any (fun phase => phase.phase == "validation" &&
      phase.query == some "acceptance_preserved") do
    throw <| IO.userError "Successful solving skipped cleanup/validation"
  let identity ← _root_.Equivalence.Checker.check
    { mode := "function", inputs := "integer" } old old
  unless (identity.getObjValAs? String "verdict").toOption == some "equivalent" do
    throw <| IO.userError identity.pretty
  unless ({ settings with steps := 0 }.validate matches .error _) do
    throw <| IO.userError "Library accepted a zero step limit"

#eval show IO Unit from do
  let decode := fun term => IO.ofExcept
    (PlutusCore.UPLC.TextEncoding.programFromString s!"(program 1.1.0 {term})")
  let old ← decode (Support.rejectDataAt [2, 1, 0] "I 42")
  let new ← decode (Support.rejectDataAt [2, 1, 0] "I 43")
  let settings : _root_.Equivalence.Checker.Config := {
    equivalence := true, bounded := true, steps := 1000,
    maxInputs := 1, maxOutputs := 1, maxSigners := 0 }
  let domain := _root_.Equivalence.Checker.nativeDomainWitness settings
  let classify := fun (models : List (String × List String)) =>
    let results := (_root_.Equivalence.Checker.queryNames settings).map fun name =>
      (models.lookup name).map Blaster.Smt.Result.Falsified |>.getD .Undetermined
    _root_.Equivalence.Checker.classify settings results old new domain
  let forward := "no_acceptance_regression"
  for reverse in ["reverse_no_acceptance_regression", "reverse_acceptance_preserved"] do
    let report := classify [(forward, ["datum: (Data.I 41)"]), (reverse, ["datum: (Data.I 42)"])]
    Support.verdict report "bounded_inequivalent"
    Support.expect report ["counterexample", "direction"] "new_to_old"
    Support.expect report ["counterexample", "ledger_validity", "valid"] true
    Support.expect report ["counterexample", "replayed"] true
  let report := classify [("acceptance_preserved", ["datum: (Data.I 43)"]),
    ("reverse_no_acceptance_regression", ["datum: (Data.I 42)"])]
  Support.verdict report "bounded_inequivalent"
  Support.expect report ["counterexample", "direction"] "old_to_new"
  let report := classify [(forward, ["datum: (Data.I 41)"]), ("reverse_no_acceptance_regression", [])]
  Support.verdict report "inconclusive"
  Support.expect report ["diagnostic_counterexample", "replayed"] false

end Tests.Equivalence.Checker
