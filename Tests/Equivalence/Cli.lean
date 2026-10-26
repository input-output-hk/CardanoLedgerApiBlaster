import Tests.Equivalence.Support

namespace Tests.Equivalence.Cli
open Support Lean

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
  for (old, new, expected) in [(reject, accept, "preserved"), (accept, reject, "regression"),
      (accept, accept, "preserved"), (reject, reject, "preserved")] do
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
      (64099, 500, "preserved"), (64100, 499, "preserved")] do
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
  verdict report "equivalent"
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

end Tests.Equivalence.Cli
