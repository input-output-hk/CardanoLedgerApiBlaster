import Tests.Equivalence.Support

namespace Tests.Equivalence.BoundedValidator
open Support Lean
open _root_.Equivalence

def settings : Cli.Config := {
  mode := "validator", bounded := true, steps := 100, timeout := 5, wallTimeout := 10 }

def accept : String := "(lam c (con unit ()))"
def loop : String := "(lam c [(lam x [x x]) (lam x [x x])])"

#eval show IO Unit from do
  let c ← IO.ofExcept (Cli.parse {} ["old.uplc", "new.uplc", "--bounded", "--steps", "100"])
  unless c.mode == "validator" && c.bounded && c.budget.isNone && c.steps == 100 do
    throw <| IO.userError "Unexpected step-bounded validator defaults"
  let r ← comparePrograms accept accept settings
  verdict r "bounded_preserved"
  expect r ["steps"] (100 : Nat)
  expect r ["bounded"] true
  expect r ["budget"] Json.null
  expect r ["execution"] "uncosted"
  expect r ["domain_status"] "nonempty"
  expect r ["old_acceptance_status"] "accepted"
  expect r ["old_acceptance_witness", "old", "accepts"] true
  -- The chosen bound must allow an OLD acceptance, even for identical scripts.
  let tiny ← comparePrograms accept accept { settings with steps := 1 }
  verdict tiny "vacuously_bounded_preserved"
  expect tiny ["old_acceptance_status"] "rejected_everywhere"
  expect tiny ["vacuity_reason"] "old_rejects_bounded_domain"
  unless Cli.exitCode tiny == 4 do throw <| IO.userError "Vacuous bounded result must exit 4"
  -- Without --bounded the same step limit remains an inconclusive analysis guard.
  let strict ← comparePrograms accept accept
    { settings with bounded := false, steps := 1, budget := some (100000000, 1000000) }
  verdict strict "inconclusive"
  let checked ← field strict ["queries"]
  check strict (checked.getObjVal? "old_rejected").toOption.isNone
    "A disproved comparison cannot be repaired by checking universal OLD rejection"

#eval show IO Unit from do
  let r ← comparePrograms accept loop settings
  verdict r "bounded_regression"
  let w ← witness r
  expect w ["old", "accepts"] true
  expect w ["new", "kind"] "unfinished"
  expect w ["new", "accepts"] false
  let r ← comparePrograms loop accept settings
  verdict r "vacuously_bounded_preserved"
  let r ← comparePrograms loop accept { settings with equivalence := true }
  verdict r "bounded_inequivalent"
  expect (← witness r) ["direction"] "new_to_old"
  let r ← comparePrograms accept accept { settings with equivalence := true }
  verdict r "bounded_equivalent"
  expect r ["old_acceptance_status"] "accepted"
  -- Execution budgets remain optional additional bounds.
  let r ← comparePrograms accept accept { settings with budget := some (1, 1) }
  verdict r "vacuously_bounded_preserved"
  expect r ["vacuity_reason"] "startup_budget_exhausted"

#eval show IO Unit from do
  for inputs in ["integer", "data", "spending"] do
    let r ← comparePrograms accept accept { settings with inputs }
    verdict r "bounded_preserved"
    expect r ["old_acceptance_status"] "accepted"
  let only42 := acceptIf "[[(builtin equalsInteger) c] (con integer 42)]"
  let r ← comparePrograms only42 accept { settings with inputs := "integer" }
  verdict r "bounded_preserved"
  expect r ["old_acceptance_witness", "input"] (42 : Int)
  -- V2 validator equivalence compares acceptance, not the returned constants.
  let r ← comparePrograms "(lam d (lam r (lam c (con integer 1))))"
    "(lam d (lam r (lam c (con integer 2))))"
    { settings with inputs := "data3", language := "PlutusV2", equivalence := true }
  verdict r "bounded_equivalent"
  expect r ["old_acceptance_status"] "accepted"
  -- V3 still requires unit, including in bounded mode.
  let r ← comparePrograms "(lam c (con integer 1))" accept settings
  verdict r "vacuously_bounded_preserved"
  -- Structured modes keep their ledger-model-valid witness requirements.
  for (inputs, index) in [("htlc-refund", 0), ("vesting-full", 20), ("escrow-accept", 12)] do
    let r ← comparePrograms accept accept { settings with inputs, caseIndex := some index }
    verdict r "bounded_preserved"
    expect r ["old_acceptance_status"] "accepted"
    expect r ["domain_status"] "nonempty"
  let invalidOnly := acceptIf "[[(builtin equalsData) c] (con data (I 42))]"
  let r ← comparePrograms invalidOnly accept settings
  verdict r "inconclusive"
  expect r ["old_acceptance_status"] "unestablished"

-- A real validator pair with a model-valid OLD acceptance, not just a synthetic
-- always-successful program. No execution-cost budget is supplied.
#eval show IO Unit from do
  let r ← runBounded { settings with
    scripts := #["equivalence/examples/linear_vesting/Plinth_1.45.0.0_Unisay.cbor_hex",
      "equivalence/examples/linear_vesting/Plinth_1.67.0.0_Unisay.cbor_hex"]
    inputs := "vesting-full"
    caseIndex := some 20
    steps := 2000
    wallTimeout := 15 }
  verdict r "bounded_preserved"
  expect r ["old_acceptance_status"] "accepted"
  expect r ["old_acceptance_witness", "ledger_validity", "valid"] true
  expect r ["old_acceptance_witness", "old", "accepts"] true
  expect r ["old_acceptance_witness", "new", "accepts"] true

end Tests.Equivalence.BoundedValidator
