import Equivalence.Checker
import Tests.Equivalence.Support

namespace Tests.Equivalence.Checker

open Lean _root_.Equivalence

-- This test imports no CLI and passes decoded programs directly to the API.
#eval show IO Unit from do
  let decode := fun term => IO.ofExcept
    (PlutusCore.UPLC.TextEncoding.programFromString s!"(program 1.1.0 {term})")
  let old ← decode "(lam c (con unit ()))"
  let new ← decode (Tests.Equivalence.Support.rejectDataAt [2, 1, 0] "I 42")
  let phases ← IO.mkRef (#[] : Array Solver.Phase)
  let settings : _root_.Equivalence.Checker.Config := {
    maxInputs := 1, maxOutputs := 1, maxSigners := 1, bounded := true, steps := 100, timeout := 5 }
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

end Tests.Equivalence.Checker
