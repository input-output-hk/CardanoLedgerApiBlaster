import Tests.Equivalence.Support

namespace Tests.Equivalence.Minting

open Support

private def policy (v3 : Bool) (limit : Int) : String :=
  let mintMap := s!"[(builtin unMapData) {contextFieldTerm [0, 4]}]"
  let assetMap := if v3 then mintMap else s!"[(force (builtin tailList)) {mintMap}]"
  let first := fun entries => s!"[(force (builtin headList)) {entries}]"
  let value := fun pair => s!"[(force (force (builtin sndPair))) {pair}]"
  let quantity := value (first s!"[(builtin unMapData) {value (first assetMap)}]")
  let redeemer := if v3 then contextFieldTerm [1] else "redeemer"
  let result := if v3 then "(con unit ())" else "(con integer 0)"
  let check := s!"[[(builtin lessThanEqualsInteger) [(builtin unIData) {quantity}]] (con integer {limit})]"
  let checkRedeemer := s!"[[(builtin equalsData) {redeemer}] (con data (Constr 0 []))]"
  let branch := fun condition result =>
    s!"(force [[[(force (builtin ifThenElse)) {condition}] (delay {result})] (delay (error))])"
  let body := s!"(lam c {branch checkRedeemer (branch check result)})"
  if v3 then body else s!"(lam redeemer {body})"

private def settings : Config := {
  purpose := "mint"
  languageOld := some "PlutusV2"
  bounded := true
  steps := 200
  maxInputs := 1
  maxOutputs := 1
  maxSigners := 0
  wallTimeout := 90 }

-- Compare the policy across versions and check the encoding of its replayed mint.
#eval show IO Unit from do
  let report ← comparePrograms (policy false 1) (policy true 1) { settings with equivalence := true }
  verdict report "bounded_equivalent"
  expect report ["purpose"] "mint"
  noCounterexample report
  let w ← field report ["old_acceptance_witness"]
  expect w ["replayed"] true
  expect w ["ledger_validity", "valid"] true
  expect w ["old", "accepts"] true
  expect w ["old", "result", "kind"] "integer"
  expect w ["new", "accepts"] true
  let #[redeemer, oldContext] ← IO.ofExcept ((← field w ["arguments", "old"]).getArr?)
    | throw <| IO.userError "Expected two V2 minting arguments"
  let #[newContext] ← IO.ofExcept ((← field w ["arguments", "new"]).getArr?)
    | throw <| IO.userError "Expected one V3 minting argument"
  check w (redeemer == (← dataField newContext [1])) "Different redeemers"
  let purpose ← dataField newContext [2]
  expect purpose ["constructor"] (0 : Int)
  check w (purpose == (← dataField oldContext [1])) "Different minting purposes"
  let oldMint ← IO.ofExcept ((← dataField oldContext [0, 4]).getObjValAs? (Array Lean.Json) "map")
  let newMint ← IO.ofExcept ((← dataField newContext [0, 4]).getObjValAs? (Array Lean.Json) "map")
  check w (oldMint.size == 2 && newMint.size == 1 && oldMint[1]? == newMint[0]?) "Different minted assets"
  let some asset := newMint[0]? | throw <| IO.userError "Missing minted asset"
  check w ((← field asset ["k"]) == (← dataField purpose [0])) "Minted asset uses the wrong policy"
  let #[token] ← IO.ofExcept ((← field asset ["v"]).getObjValAs? (Array Lean.Json) "map")
    | throw <| IO.userError "Expected one minted token"
  let quantity ← IO.ofExcept ((← field token ["v"]).getObjValAs? Int "int")
  check w (quantity != 0) "Expected a nonzero mint or burn"

#eval show IO Unit from do
  let report ← comparePrograms (policy false 1) (policy false 1) { settings with language := "PlutusV2" }
  verdict report "bounded_preserved"
  expect report ["old_acceptance_status"] "accepted"

#eval show IO Unit from do
  let selected := { settings with languageOld := none, timeout := 8, skipOldRejected := true }
  let report ← comparePrograms (policy true 1) (policy true 0) selected
  verdict report "bounded_regression"
  let w ← witness report
  expect w ["ledger_validity", "valid"] true
  expect w ["old", "accepts"] true
  expect w ["new", "accepts"] false
  let minted ← dataField (← field w ["input"]) [0, 4]
  let #[asset] ← IO.ofExcept (minted.getObjValAs? (Array Lean.Json) "map")
    | throw <| IO.userError "Expected one minted asset"
  let #[token] ← IO.ofExcept ((← field asset ["v"]).getObjValAs? (Array Lean.Json) "map")
    | throw <| IO.userError "Expected one minted token"
  expect token ["v", "int"] (1 : Int)

#eval show IO Unit from do
  let selected := { settings with languageOld := none, maxOutputs := 0 }
  let report ← comparePrograms (policy true (-1)) "(lam c (error))" selected
  verdict report "bounded_regression"
  let w ← witness report
  let minted ← dataField (← field w ["input"]) [0, 4]
  let #[asset] ← IO.ofExcept (minted.getObjValAs? (Array Lean.Json) "map")
    | throw <| IO.userError "Expected one burned asset"
  let #[token] ← IO.ofExcept ((← field asset ["v"]).getObjValAs? (Array Lean.Json) "map")
    | throw <| IO.userError "Expected one burned token"
  let quantity ← IO.ofExcept ((← field token ["v"]).getObjValAs? Int "int")
  check w (quantity < 0) "Expected a burn"

end Tests.Equivalence.Minting
