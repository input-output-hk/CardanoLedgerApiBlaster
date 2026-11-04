import Tests.Equivalence.Support

namespace Tests.Equivalence.BoundedValidator
open Support Lean
open _root_.Equivalence

def settings : Support.Config := {
  mode := "validator", bounded := true, steps := 100, timeout := 5, wallTimeout := 10 }

def accept : String := "(lam c (con unit ()))"
def loop : String := "(lam c [(lam x [x x]) (lam x [x x])])"

#eval show IO Unit from do
  let r ← comparePrograms accept accept settings
  verdict r "bounded_preserved"
  expect r ["steps"] (100 : Nat)
  expect r ["bounded"] true
  expect r ["step_limit_kind"] "execution_bound"
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
  let only42 := acceptIf s!"[[(builtin equalsData) {datumTerm}] (con data (I 42))]"
  let r ← comparePrograms only42 accept { settings with steps := 1000 }
  verdict r "bounded_preserved"
  expect (← dataField (← field r ["old_acceptance_witness", "input"]) [2, 1, 0]) ["int"] (42 : Int)
  -- V3 still requires unit, including in bounded mode.
  let r ← comparePrograms "(lam c (con integer 1))" accept settings
  verdict r "vacuously_bounded_preserved"
  -- Structured contexts keep their ledger-model-valid witness requirements.
  let r ← comparePrograms accept accept settings
  verdict r "bounded_preserved"
  expect r ["old_acceptance_status"] "accepted"
  expect r ["domain_status"] "nonempty"
  let invalidOnly := acceptIf s!"[[(builtin equalsData) {contextFieldTerm [0, 3]}] (con data (I 0))]"
  let r ← comparePrograms invalidOnly accept settings
  verdict r "inconclusive"
  expect r ["old_acceptance_status"] "unestablished"

end Tests.Equivalence.BoundedValidator
