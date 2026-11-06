import Tests.Equivalence.Support

namespace Tests.Equivalence.Validator
open Support Lean

-- V3 acceptance requires unit; V1/V2 return rules remain covered by the
-- evaluator tests, independently of the V3 spending-domain checker.
example : _root_.Equivalence.Acceptance.accepts false
    (.success (.VCon (.Integer 1)) ⟨⟨0⟩, ⟨0⟩⟩) = some true := by decide
example : _root_.Equivalence.Acceptance.accepts true
    (.success (.VCon (.Integer 1)) ⟨⟨0⟩, ⟨0⟩⟩) = some false := by decide

-- A reverse witness must come from the model, including large and negative inputs.
#eval do
  for n in ([-42, 987654321012345678901234567890] : List Int) do
    let old := rejectIf s!"[[(builtin equalsData) {datumTerm}] (con data (I {n}))]"
    let report ← comparePrograms old "(lam n (con unit ()))"
    verdict report "inequivalent"
    let w ← witness report
    expect (← dataField (← field w ["input"]) [2, 1, 0]) ["int"] n
    expect w ["direction"] "new_to_old"

-- The redeemer binding must replay in either direction.
#eval do
  let inspect := rejectDataAt [1] "I 42"
  let accept := "(lam c (con unit ()))"
  for symmetric in [false, true] do
    let report ← comparePrograms (if symmetric then inspect else accept)
      (if symmetric then accept else inspect) { config with equivalence := symmetric }
    verdict report (if symmetric then "inequivalent" else "regression")
    let w ← witness report
    expect (← dataField (← field w ["input"]) [1]) ["int"] (42 : Int)
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

#eval do
  let report ← comparePrograms "(lam c (con unit ()))" "(lam c (con integer 42))" acceptanceConfig
  verdict report "regression"

-- Skip only the rejection query; comparisons and the accepting-witness
-- requirement still apply to ledger-checked contexts.
#eval show IO Unit from do
  let settings : Support.Config := {
    budget := some (1000000, 10000), timeout := 5, skipOldRejected := true }
  let report ← comparePrograms "(lam c (con unit ()))" "(lam c (con unit ()))" settings
  verdict report "preserved"
  let queries ← field report ["queries"]
  check report (queries.getObjVal? "old_rejected").toOption.isNone "OLD rejection query was not skipped"
  expect report ["queries", "acceptance_preserved"] "valid"
  expect report ["old_acceptance_witness", "replayed"] true
  expect report ["old_acceptance_witness", "old", "accepts"] true
  let report ← comparePrograms "(lam c (error))" "(lam c (error))" settings
  verdict report "inconclusive"
  expect report ["inconclusive_reason"] "old_acceptance_unestablished"

-- The OLD-acceptance witness must come from the model, not just the zero input.
#eval show IO Unit from do
  let only42 := acceptIf s!"[[(builtin equalsData) {datumTerm}] (con data (I 42))]"
  let report ← comparePrograms only42 "(lam c (con unit ()))"
    { acceptanceConfig with budget := some (100000000, 1000000) }
  verdict report "preserved"
  expect (← dataField (← field report ["old_acceptance_witness", "input"]) [2, 1, 0]) ["int"] (42 : Int)
  expect report ["old_acceptance_witness", "replayed"] true
  expect report ["old_acceptance_witness", "old", "accepts"] true

-- Deferred rejection establishes vacuity; a confirmed regression needs no
-- rejection query in either direction.
#eval show IO Unit from do
  let settings := { config with inputs := "valid-context" }
  let report ← comparePrograms "(lam c (error))" "(lam c (error))" settings
  verdict report "vacuously_equivalent"
  expect report ["derived_queries", "acceptance_preserved"] "old_rejected"
  expect report ["queries", "reverse_acceptance_preserved"] "valid"
  noCounterexample report
  let report ← comparePrograms "(lam c (error))" "(lam c (con unit ()))" settings
  verdict report "inequivalent"
  let counterexample ← witness report
  expect counterexample ["direction"] "new_to_old"
  let checked ← field report ["queries"]
  for name in ["old_rejected", "new_rejected"] do
    check report (checked.getObjVal? name).toOption.isNone
      "Confirmed reverse regression unnecessarily checked rejection"

#eval show IO Unit from do
  let c : Support.Config := { acceptanceConfig with
    bounded := true, steps := 100, budget := none, timeout := 15, wallTimeout := 60 }
  unless _root_.Equivalence.Checker.queryNames c ==
      #["acceptance_preserved", "no_acceptance_regression", "old_rejected"] do
    throw <| IO.userError "OLD rejection must follow comparison"
  let accept := "(lam c (con unit ()))"
  let regression ← comparePrograms accept "(lam c (error))" c
  verdict regression "bounded_regression"
  discard <| witness regression
  let checked ← field regression ["queries"]
  check regression ((← IO.ofExcept checked.getObj?).size == 1)
    "Confirmed regression should stop after its comparison"
  let positive ← comparePrograms accept accept c
  verdict positive "bounded_preserved"
  expect positive ["old_acceptance_status"] "accepted"
  let checked ← field positive ["queries"]
  check positive (checked.getObjVal? "old_rejected").toOption.isNone
    "Native OLD witness should avoid the universal rejection query"
  let only42 := acceptIf s!"[[(builtin equalsData) {datumTerm}] (con data (I 42))]"
  let modeled ← comparePrograms only42 accept { c with steps := 1000 }
  verdict modeled "bounded_preserved"
  expect modeled ["queries", "old_rejected"] "falsified"
  expect (← dataField (← field modeled ["old_acceptance_witness", "input"]) [2, 1, 0]) ["int"] (42 : Int)

end Tests.Equivalence.Validator
