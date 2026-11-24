import Tests.Equivalence.Support

namespace Tests.Equivalence.UplcOptimize
open Support Lean
open _root_.Equivalence

def config : Support.Config := {
  mode := "function", inputs := "integer", format := "textual", timeout := 5, wallTimeout := 8 }

def paths (name : String) : Array String := #[
  s!"equivalence/examples/uplc-optimize/{name}.uplc",
  s!"equivalence/examples/uplc-optimize/{name}-opt.uplc"]

-- Native V2 acceptance still permits successful integer results. Validator
-- checking itself now uses only the V3 structured spending domain.
#eval show IO Unit from do
  let old ← Support.readProgram "equivalence/examples/uplc-optimize/ifthenelse.uplc" "textual"
  let new ← Support.readProgram "equivalence/examples/uplc-optimize/ifthenelseopt.uplc" "textual"
  for budget in [(1000000, 10000), (100000000, 1000000)] do
    let execute := fun p n => Function.execute p (Queries.args n) budget.1 budget.2 false true 100000
    unless Acceptance.accepts false (execute old 0) == some false &&
        Acceptance.accepts false (execute new 0) == some true do
      throw <| IO.userError "V2 acceptance must expose the optimizer regression"

-- A real optimizer bug: strict evaluation of an unused argument divides by zero.
-- Function checking catches it with V3 rules and uncosted execution.
#eval show IO Unit from do
  let r ← compareFixtures { config with scripts := #[
    "equivalence/examples/uplc-optimize/ifthenelse.uplc",
    "equivalence/examples/uplc-optimize/ifthenelseopt.uplc"] }
  verdict r "inequivalent"
  expect r ["mode"] "function"
  let w ← witness r
  expect w ["input"] (0 : Int)
  expect w ["old", "kind"] "error"
  expect w ["new", "result", "value"] (1 : Int)

-- Actual outputs from uplc optimize 1.71.0.0. The reference CEK evaluator also
-- confirms each mismatch under E and G; witnesses include negative/nonzero inputs.
#eval show IO Unit from do
  for (name, input, value) in [
      ("if-false-negative", (-3 : Int), (11 : Int)),
      ("choose-list-empty", 0, 7), ("choose-list-cons", 0, 7),
      ("choose-data-integer", 42, 9), ("head-list-empty", 0, 7),
      ("index-out-of-bounds", 0, 7), ("un-i-data-bytes", 42, 7),
      ("invalid-utf8", 0, 7), ("explicit-error", 0, 7)] do
    let scripts := paths name
    let old ← Support.readProgram scripts[0]! "textual"
    let new ← Support.readProgram scripts[1]! "textual"
    let execute := fun p n => Function.execute p (Queries.args n) 0 0 true false 100000
    unless execute old input matches .error do
      throw <| IO.userError s!"{name}: original must fail at {input}"
    unless Function.observation (execute new input) == some (.Integer value) do
      throw <| IO.userError s!"{name}: optimized must return {value} at {input}"
    -- Each original also succeeds: the mismatch is input-dependent.
    unless Function.observation (execute old (input + 1)) == some (.Integer value) do
      throw <| IO.userError s!"{name}: original must succeed away from the counterexample"
    let report ← compareFixtures { config with scripts }
    verdict report "inequivalent"
    let w ← witness report
    expect w ["input"] input
    expect w ["old", "kind"] "error"
    expect w ["new", "kind"] "success"
    expect w ["new", "result", "value"] value

-- Correct optimizations must prove equivalent, including a delayed dead branch
-- and strict arguments that fail at zero in both original and optimized scripts.
#eval show IO Unit from do
  for name in ["delayed-control", "unused-let", "case-field"] do
    for path in paths name do
      let p ← Support.readProgram path "textual"
      let result := Function.execute p (Queries.args 1) 0 0 true false 100000
      unless Function.observation result == some (.Integer 7) do
        throw <| IO.userError s!"{name}: control must return 7 at input 1"
    let report ← compareFixtures { config with scripts := paths name }
    verdict report "equivalent"
    noCounterexample report

-- The exact upstream fix from PR #8022 preserves the strict integer function.
#eval show IO Unit from do
  let report ← compareFixtures { config with
    scripts := #["equivalence/examples/uplc-optimize/ifthenelse.uplc",
      "equivalence/examples/uplc-optimize/ifthenelse-fixed.uplc"]
    steps := 1000, timeout := 10, wallTimeout := 60 }
  verdict report "equivalent"
  noCounterexample report

-- The tutorial uses actual before/after optimizer outputs for a V3 validator.
-- Check native-replayed acceptance differences and a non-vacuous positive proof.
#eval show IO Unit from do
  let tutorial : Support.Config := {
    mode := "validator", format := "textual", bounded := true, equivalence := true
    steps := 1000, maxInputs := 1, maxOutputs := 1, maxSigners := 1
    timeout := 10, wallTimeout := 60, solverSeed := some 0 }
  let original := "equivalence/examples/uplc-optimize/tutorial/validator.uplc"
  for datum in [(0 : Int), 1] do
    let some context := Checker.nativeDomainWitness
        { tutorial.toConfig with datum := some (.I datum) }
      | throw <| IO.userError "Tutorial needs a ledger-valid concrete context"
    for (path, buggy) in [(original, false),
        ("equivalence/examples/uplc-optimize/tutorial/validator-buggy.uplc", true),
        ("equivalence/examples/uplc-optimize/tutorial/validator-fixed.uplc", false)] do
      let program ← readProgram path "textual"
      let result := Function.executeValidator program [.Const (.Data context)]
        0 0 true true false tutorial.steps
      unless Acceptance.accepts true result == some (buggy || datum != 1) do
        throw <| IO.userError s!"Unexpected tutorial acceptance for {path}, datum {datum}"
  let bad ← compareFixtures { tutorial with scripts := #[original,
    "equivalence/examples/uplc-optimize/tutorial/validator-buggy.uplc"] }
  verdict bad "bounded_inequivalent"
  expect bad ["queries", "acceptance_preserved"] "valid"
  expect bad ["queries", "reverse_acceptance_preserved"] "falsified"
  let counterexample ← witness bad
  expect counterexample ["direction"] "new_to_old"
  expect counterexample ["ledger_validity", "valid"] true
  expect counterexample ["old", "accepts"] false
  expect counterexample ["new", "accepts"] true
  let fixed ← compareFixtures { tutorial with scripts := #[original,
    "equivalence/examples/uplc-optimize/tutorial/validator-fixed.uplc"] }
  verdict fixed "bounded_equivalent"
  expect fixed ["queries", "acceptance_preserved"] "valid"
  expect fixed ["queries", "reverse_acceptance_preserved"] "valid"
  expect fixed ["old_acceptance_status"] "accepted"
  expect fixed ["old_acceptance_witness", "replayed"] true
  expect fixed ["old_acceptance_witness", "ledger_validity", "valid"] true
  noCounterexample fixed

-- Additional acceptance is permitted by bounded preservation, so optimizer
-- verification needs strict function checking or bounded equivalence.
#eval show IO Unit from do
  let settings := { config with scripts := paths "choose-list-empty", bounded := true }
  verdict (← compareFixtures settings) "bounded_preserved"
  let report ← compareFixtures { settings with equivalence := true }
  verdict report "bounded_inequivalent"
  expect (← witness report) ["input"] (0 : Int)

-- The reference evaluator confirms this bug as well, but symbolic UTF-8 input
-- reaches BitVec operations unsupported by the pinned Blaster translator. Keep
-- the reproducer visible without counting it as successful mismatch detection.
#eval show IO Unit from do
  let scripts := paths "invalid-utf8-symbolic"
  let old ← Support.readProgram scripts[0]! "textual"
  let new ← Support.readProgram scripts[1]! "textual"
  let execute := fun p n => Function.execute p (Queries.args n) 0 0 true false 100000
  unless execute old 0 matches .error do
    throw <| IO.userError "Expected invalid UTF-8 to fail natively"
  unless Function.observation (execute new 0) == some (.Integer 7) &&
      Function.observation (execute old 1) == some (.Integer 7) do
    throw <| IO.userError "Unexpected native UTF-8 behavior"
  let report ← compareFixtures { config with scripts }
  match (report.getObjValAs? String "verdict").toOption with
  | some "inequivalent" =>
    expect (← witness report) ["input"] (0 : Int)
  | some "error" =>
    let explanation ← IO.ofExcept (report.getObjValAs? String "explanation")
    unless (explanation.splitOn "BitVec").length > 1 do
      throw <| IO.userError s!"Unexpected translation failure: {explanation}"
  | _ => throw <| IO.userError s!"UTF-8 mismatch must be caught or explicitly unsupported: {report.pretty}"

end Tests.Equivalence.UplcOptimize
