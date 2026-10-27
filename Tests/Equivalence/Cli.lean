import Tests.Equivalence.Support

namespace Tests.Equivalence.Cli
open Support Lean

-- An eager unused ifThenElse argument divides by zero at x=0. The optimized
-- program returns 1. This is additional acceptance, so only the reverse
-- implication fails; integer return values require the V2 acceptance rules.
#eval show IO Unit from do
  let settings : _root_.Equivalence.Cli.Config := {
    scripts := #["equivalence/examples/ifthenelse/ifthenelse.uplc",
      "equivalence/examples/ifthenelse/ifthenelseopt.uplc"]
    format := "textual"
    inputs := "integer"
    language := "PlutusV2"
    budget := some (100000000, 1000000)
    equivalence := true
    skipOldRejected := true
    timeout := 5
    wallTimeout := 5 }
  -- The smaller budget used to select expensive symbolic builtin-cost guards.
  for budget in [(1000000, 10000), (100000000, 1000000)] do
    let report ← runBounded { settings with budget := some budget }
    verdict report "inequivalent"
    let counterexample ← witness report
    expect counterexample ["input"] (0 : Int)
    expect counterexample ["direction"] "new_to_old"
    expect counterexample ["old", "kind"] "error"
    expect counterexample ["new", "accepts"] true
    expect counterexample ["new", "result", "value"] (1 : Int)
  let forward ← runBounded { settings with equivalence := false, skipOldRejected := false }
  verdict forward "preserved"
  expect forward ["old_acceptance_witness", "old", "accepts"] true

-- Successful values may differ: equivalence compares accepted inputs.
#eval do
  let report ← comparePrograms "(lam n (con integer 1))" "(lam n (con integer 2))"
    { config with language := "PlutusV2" }
  verdict report "equivalent"
  for name in ["acceptance_preserved", "reverse_acceptance_preserved"] do
    expect report ["queries", name] "valid"
  noCounterexample report

-- A reverse witness must come from the model, including large and negative inputs.
#eval do
  for n in ([-42, 987654321012345678901234567890] : List Int) do
    let old := rejectIf s!"[[(builtin equalsInteger) c] (con integer {n})]"
    let report ← comparePrograms old "(lam n (con unit ()))"
    verdict report "inequivalent"
    let w ← witness report
    expect w ["input"] n
    expect w ["direction"] "new_to_old"

-- Three-argument scripts must replay the redeemer binding in either direction.
#eval do
  let inspect := "(lam d (lam r (lam c (force [[[(force (builtin ifThenElse)) " ++
    "[[(builtin equalsData) r] (con data (I 42))]] (delay (error))] (delay (con unit ()))]))))"
  let accept := "(lam d (lam r (lam c (con unit ()))))"
  for symmetric in [false, true] do
    let report ← comparePrograms (if symmetric then inspect else accept)
      (if symmetric then accept else inspect)
      { config with equivalence := symmetric, inputs := "data3", language := "PlutusV2" }
    verdict report (if symmetric then "inequivalent" else "regression")
    let w ← witness report
    expect w ["input", "redeemer"] (Json.mkObj [("int", toJson (42 : Int))])
    let input ← IO.ofExcept ((← field w ["input"]).getObj?)
    check report (input.size == 3) "Expected datum, redeemer and context"
    for name in ["datum", "redeemer", "context"] do
      discard <| field w ["input", name]
    expect w ["direction"] (if symmetric then "new_to_old" else "old_to_new")
    expect w ["old", "accepts"] (!symmetric)
    expect w ["new", "accepts"] symmetric

-- Directional upgrade semantics include vacuous preservation when OLD rejects.
#eval do
  let accept := "(lam c (con unit ()))"
  let reject := "(lam c (error))"
  for (old, new, expected) in [(reject, accept, "vacuously_preserved"), (accept, reject, "regression"),
      (accept, accept, "preserved"), (reject, reject, "vacuously_preserved")] do
    let report ← comparePrograms old new acceptanceConfig
    verdict report expected
    if expected == "regression" then
      let w ← witness report
      expect w ["old", "accepts"] true
      expect w ["new", "accepts"] false

-- Exact shared-budget boundaries exercise startup, application and zero-cost returns.
#eval do
  let accept := "(lam c (con unit ()))"
  for (cpu, memory, expected) in [(64100, 500, "regression"),
      (64099, 500, "vacuously_preserved"), (64100, 499, "vacuously_preserved")] do
    let report ← comparePrograms accept "(lam c (error))"
      { acceptanceConfig with budget := some (cpu, memory) }
    verdict report expected
  let slower := "(lam c [(lam x (con unit ())) c])"
  for (cpu, expected) in [(64100, "regression"), (1000000, "preserved")] do
    let report ← comparePrograms accept slower { acceptanceConfig with budget := some (cpu, 10000) }
    verdict report expected
    if expected == "regression" then
      let w ← witness report
      expect w ["new", "kind"] "budget_exhausted"
      expect w ["old", "spent_cpu"] (64100 : Nat)
      expect w ["old", "spent_memory"] (500 : Nat)

-- The same budget must detect a difference in either orientation.
#eval do
  let accept := "(lam c (con unit ()))"
  let slower := "(lam c [(lam x (con unit ())) c])"
  for (old, new, direction, oldAccepts) in [(accept, slower, "old_to_new", true),
      (slower, accept, "new_to_old", false)] do
    let report ← comparePrograms old new { config with budget := some (64100, 10000) }
    verdict report "inequivalent"
    let w ← witness report
    expect w ["direction"] direction
    expect w ["old", "accepts"] oldAccepts
    expect w ["new", "accepts"] (!oldAccepts)
  let report ← comparePrograms accept "(lam c (error))" { config with budget := some (0, 0) }
  verdict report "vacuously_equivalent"
  noCounterexample report

-- Builtin charges are additional to the CEK machine-node charges.
#eval do
  let addition := "(lam c [(lam x (con unit ())) [[(builtin addInteger) (con integer 1)] (con integer 2)]])"
  for (cpu, memory, expected) in [(277308, 1202, "preserved"),
      (277307, 1202, "regression"), (277308, 1201, "regression")] do
    let report ← comparePrograms "(lam c (con unit ()))" addition
      { acceptanceConfig with budget := some (cpu, memory) }
    verdict report expected
    if expected == "regression" then
      let w ← witness report
      expect w ["new", "kind"] "budget_exhausted"

-- Ledger return rules differ by language; successful V1/V2 values are unrestricted.
#eval do
  for (language, expected) in [("PlutusV3", "regression"), ("PlutusV2", "preserved"), ("PlutusV1", "preserved")] do
    let report ← comparePrograms "(lam c (con unit ()))" "(lam c (con integer 42))"
      { acceptanceConfig with language }
    verdict report expected

-- Skip only the rejection query; comparisons and the accepting-witness
-- requirement still apply to integer and ledger-checked contexts.
#eval show IO Unit from do
  let settings : _root_.Equivalence.Cli.Config := {
    budget := some (1000000, 10000), timeout := 5, skipOldRejected := true }
  for mode in ["integer", "valid-context"] do
    let report ← comparePrograms "(lam c (con unit ()))" "(lam c (con unit ()))"
      { settings with inputs := mode }
    verdict report "preserved"
    let queries ← field report ["queries"]
    check report (queries.getObjVal? "old_rejected").toOption.isNone "OLD rejection query was not skipped"
    expect report ["queries", "acceptance_preserved"] "valid"
    expect report ["old_acceptance_witness", "replayed"] true
    expect report ["old_acceptance_witness", "old", "accepts"] true
  let report ← comparePrograms "(lam c (error))" "(lam c (error))"
    { settings with inputs := "integer" }
  verdict report "inconclusive"
  expect report ["inconclusive_reason"] "old_acceptance_unestablished"

-- The OLD-acceptance witness must come from the model, not just the zero input.
#eval show IO Unit from do
  let only42 := acceptIf "[[(builtin equalsInteger) c] (con integer 42)]"
  let report ← comparePrograms only42 "(lam c (con unit ()))"
    { acceptanceConfig with budget := some (1000000, 10000) }
  verdict report "preserved"
  expect report ["old_acceptance_witness", "input"] (42 : Int)
  expect report ["old_acceptance_witness", "replayed"] true
  expect report ["old_acceptance_witness", "old", "accepts"] true

-- Rejection discharges only the direction starting at the rejected script.
#eval show IO Unit from do
  let settings := selectFamily config "htlc-claim" 45 "baseline"
  let report ← comparePrograms "(lam c (error))" "(lam c (error))" settings
  verdict report "vacuously_equivalent"
  expect report ["derived_queries", "acceptance_preserved"] "old_rejected"
  expect report ["derived_queries", "reverse_acceptance_preserved"] "new_rejected"
  noCounterexample report
  let report ← comparePrograms "(lam c (error))" "(lam c (con unit ()))" settings
  verdict report "inequivalent"
  let counterexample ← witness report
  expect counterexample ["direction"] "new_to_old"
  let derived ← field report ["derived_queries"]
  check report (derived.getObjVal? "reverse_acceptance_preserved").toOption.isNone
    "Forward rejection discharged reverse preservation"

end Tests.Equivalence.Cli
