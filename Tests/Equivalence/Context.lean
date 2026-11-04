import Tests.Equivalence.Support

namespace Tests.Equivalence.Context

open Support Lean

set_option stderrAsMessages false

-- Raw proof fields can produce invalid countermodels; only ledger-valid native
-- replays establish regressions. Valid fee/treasury changes remain observable.
#eval show IO Unit from do
  let selected := { config with inputs := "valid-context" }
  let fee := s!"[(builtin unIData) {contextFieldTerm [0, 3]}]"
  let negative := rejectIf s!"[[(builtin lessThanInteger) {fee}] (con integer 0)]"
  let baseline ← comparePrograms negative "(lam c (con unit ()))" selected
  verdict baseline "inconclusive"
  noCounterexample baseline
  let fortyTwo := rejectDataAt [0, 3] "I 42"
  let varied ← comparePrograms fortyTwo "(lam c (con unit ()))" selected
  verdict varied "inequivalent"
  expect (← dataField (← field (← witness varied) ["input"]) [0, 3]) ["int"] (42 : Int)
  let treasury ← comparePrograms (rejectDataAt [0, 14] "Constr 0 [I 42]")
    "(lam c (con unit ()))" selected
  verdict treasury "inequivalent"
  let input ← field (← witness treasury) ["input"]
  expect (← dataField input [0, 14, 0]) ["int"] (42 : Int)

-- The configured profile supplies the common V3 spending outer shape.
#eval do
  let report ← comparePrograms "(lam c (con unit ()))" "(lam c (error))"
    { acceptanceConfig with inputs := "valid-context" }
  verdict report "regression"
  let w ← witness report
  expect w ["input", "constructor"] (0 : Nat)
  let fields ← IO.ofExcept ((← field w ["input", "fields"]).getArr?)
  check report (fields.size == 3) "Expected three script-context fields"
  let tx ← IO.ofExcept ((← field fields[0]! ["fields"]).getArr?)
  check report (tx.size == 16) "Expected 16 TxInfo fields"
  expect fields[2]! ["constructor"] (1 : Nat)
  let info ← IO.ofExcept ((← field fields[2]! ["fields"]).getArr?)
  check report (info.size == 2) "Expected spending reference and datum option"

end Tests.Equivalence.Context
