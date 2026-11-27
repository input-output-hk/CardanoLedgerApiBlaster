import Tests.Equivalence.Support

namespace Tests.Equivalence.MixedLanguage

open Support

private def firstMapValue (value : String) : String :=
  let pair := s!"[(force (builtin headList)) [(builtin unMapData) {value}]]"
  s!"[(force (force (builtin sndPair))) {pair}]"

private def spendingBody (datum redeemer fee : String) (maximum : Nat) (result : String) : String :=
  let conditions := [
    s!"[[(builtin equalsData) {datum}] (con data (I 0))]",
    s!"[[(builtin equalsData) {redeemer}] (con data (Constr 0 []))]",
    s!"[[(builtin lessThanEqualsInteger) [(builtin unIData) {fee}]] (con integer {maximum})]"]
  let body := conditions.foldr (fun condition branch =>
    s!"(force [[[(force (builtin ifThenElse)) {condition}] (delay {branch})] (delay (error))])") result
  s!"(lam c {body})"

private def compareSpending (maximum : Nat) (equivalence : Bool)
    (oldVersion := "1.0.0") (newVersion := "1.1.0") (newIsV2 := false) : IO Lean.Json :=
  let fee := contextFieldTerm [0, 3]
  let v2Fee := firstMapValue (firstMapValue fee)
  let v2Body := fun limit result =>
    s!"(lam datum (lam redeemer {spendingBody "datum" "redeemer" v2Fee limit result}))"
  let oldBody := v2Body 7 "(con integer 0)"
  let newBody := if newIsV2 then v2Body maximum "(con integer 1)"
    else spendingBody datumTerm (contextFieldTerm [1]) fee maximum "(con unit ())"
  runRequest {
    options := {
      languageOld := some "PlutusV2"
      languageNew := some (if newIsV2 then "PlutusV2" else "PlutusV3")
      bounded := true
      steps := 300
      maxInputs := 1
      maxOutputs := 1
      maxSigners := 0
      equivalence := equivalence }
    old := { source := s!"(program {oldVersion} {oldBody})", format := "textual" }
    new := { source := s!"(program {newVersion} {newBody})", format := "textual" } } 90

#eval show IO Unit from do
  for (oldVersion, newVersion, side, language, version) in [
      ("2.0.0", "1.1.0", "OLD", "PlutusV2", "2.0.0"),
      ("1.0.0", "1.2.0", "NEW", "PlutusV3", "1.2.0")] do
    let report ← compareSpending 7 false oldVersion newVersion
    verdict report "error"
    expect report ["explanation"]
      s!"{side} uses UPLC {version}, which is unsupported for {language} at protocol version 11. Expected UPLC 1.0.0 or 1.1.0."
    noCounterexample report

-- Both versions test the same payloads and fee. V2 accepts the integer result.
#eval show IO Unit from do
  let report ← compareSpending 7 true (oldVersion := "1.1.0") (newVersion := "1.0.0")
  verdict report "bounded_equivalent"
  expect report ["language_old"] "PlutusV2"
  expect report ["language_new"] "PlutusV3"
  expect report ["old_acceptance_status"] "accepted"
  expect report ["old_acceptance_witness", "old", "result", "kind"] "integer"
  expect report ["old_acceptance_witness", "old", "result", "value"] (0 : Int)

-- Tighten the V3 fee limit and inspect the two encodings of the replayed spend.
#eval show IO Unit from do
  let report ← compareSpending 6 false
  verdict report "bounded_regression"
  let w ← witness report
  expect w ["ledger_validity", "valid"] true
  expect w ["old", "accepts"] true
  expect w ["new", "accepts"] false
  let old ← IO.ofExcept ((← field w ["arguments", "old"]).getArr?)
  let new ← IO.ofExcept ((← field w ["arguments", "new"]).getArr?)
  let #[datum, redeemer, oldContext] := old
    | throw <| IO.userError s!"Expected three V2 arguments: {old}"
  let #[newContext] := new
    | throw <| IO.userError s!"Expected one V3 argument: {new}"
  let detailed := PlutusCore.Data.toDetailedJson
  check w (datum == detailed (.I 0)) "Unexpected V2 datum"
  check w (redeemer == detailed (.Constr 0 [])) "Unexpected V2 redeemer"
  check w (datum == (← dataField newContext [2, 1, 0])) "Different spending datums"
  check w (redeemer == (← dataField newContext [1])) "Different spending redeemers"
  let oldRef ← dataField oldContext [1, 0]
  let newRef ← dataField newContext [2, 0]
  expect (← dataField oldRef [0]) ["constructor"] (0 : Int)
  check w ((← dataField oldRef [0, 0]) == (← dataField newRef [0])) "Different spending transaction IDs"
  check w ((← dataField oldRef [1]) == (← dataField newRef [1])) "Different spending indices"
  check w ((← dataField oldContext [0, 3]) == detailed (_root_.Equivalence.Context.lovelace 7))
    "Expected the V2 fee to encode 7 lovelace"
  expect (← dataField newContext [0, 3]) ["int"] (7 : Int)

#eval show IO Unit from do
  let report ← compareSpending 7 true (newIsV2 := true)
  verdict report "bounded_equivalent"
  expect report ["language"] "PlutusV2"
  let w ← field report ["old_acceptance_witness"]
  expect w ["replayed"] true
  expect w ["ledger_validity", "predicate"] "V2 validSpendingContext"
  expect w ["old", "result", "value"] (0 : Int)
  expect w ["new", "result", "value"] (1 : Int)
  let old ← field w ["arguments", "old"]
  expect w ["arguments", "new"] old

#eval show IO Unit from do
  let report ← compareSpending 6 false (newIsV2 := true)
  verdict report "bounded_regression"
  let w ← witness report
  expect w ["old", "accepts"] true
  expect w ["new", "accepts"] false
  expect w ["ledger_validity", "valid"] true
  let #[_, _, ctx] ← IO.ofExcept ((← field w ["arguments", "old"]).getArr?)
    | throw <| IO.userError "Expected three V2 spending arguments"
  let detailed := PlutusCore.Data.toDetailedJson
  check w ((← dataField ctx [0, 3]) == detailed (_root_.Equivalence.Context.lovelace 7))
    "Expected a fee of seven lovelace"

end Tests.Equivalence.MixedLanguage
