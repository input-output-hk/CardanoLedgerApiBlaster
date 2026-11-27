import Tests.Equivalence.Support

namespace Tests.Equivalence.Withdrawal

open Support
open _root_.Equivalence

private def settings : Config := {
  purpose := "withdraw"
  languageOld := some "PlutusV2"
  bounded := true
  steps := 500
  maxInputs := 1
  maxOutputs := 1
  maxSigners := 0
  wallTimeout := 90 }

-- The withdrawal side of a forwarding validator expects a zero-ADA withdrawal
-- for its own credential and a matching redeemer.
private def forwardingValidator (v3 : Bool) : String :=
  let withdrawals := contextFieldTerm [0, 6]
  let entry := s!"[(force (builtin headList)) [(builtin unMapData) {withdrawals}]]"
  let key := s!"[(force (force (builtin fstPair))) {entry}]"
  let amount := s!"[(force (force (builtin sndPair))) {entry}]"
  let own := contextFieldTerm (if v3 then [2, 0] else [1, 0])
  let redeemer := if v3 then contextFieldTerm [1] else "redeemer"
  let checks := [
    s!"[[(builtin equalsData) {key}] {own}]",
    s!"[[(builtin equalsData) {amount}] (con data (I 0))]",
    s!"[[(builtin equalsData) {redeemer}] (con data (Constr 0 []))]"]
  let result := if v3 then "(con unit ())" else "(con integer 0)"
  let body := checks.foldr (fun check rest =>
    s!"(force [[[(force (builtin ifThenElse)) {check}] (delay {rest})] (delay (error))])") result
  if v3 then s!"(lam c {body})" else s!"(lam redeemer (lam c {body}))"

#eval show IO Unit from do
  let report ← comparePrograms (forwardingValidator false) (forwardingValidator true)
    { settings with equivalence := true }
  verdict report "bounded_equivalent"
  expect report ["purpose"] "withdraw"
  let w ← field report ["old_acceptance_witness"]
  expect w ["replayed"] true
  expect w ["ledger_validity", "valid"] true
  expect w ["old", "result", "kind"] "integer"
  expect w ["old", "accepts"] true
  expect w ["new", "accepts"] true
  let #[redeemer, oldCtx] ← IO.ofExcept ((← field w ["arguments", "old"]).getArr?)
    | throw <| IO.userError "Expected two V2 withdrawal arguments"
  let #[newCtx] ← IO.ofExcept ((← field w ["arguments", "new"]).getArr?)
    | throw <| IO.userError "Expected one V3 withdrawal argument"
  check w (redeemer == (← dataField newCtx [1])) "Different redeemers"
  let oldKey ← dataField oldCtx [1, 0]
  let newKey ← dataField newCtx [2, 0]
  expect oldKey ["constructor"] (0 : Int)
  check w ((← dataField oldKey [0]) == newKey) "Expected the V2 staking credential wrapper"
  for (ctx, key, purposeIndex) in [(oldCtx, oldKey, 1), (newCtx, newKey, 2)] do
    let withdrawals ← dataField ctx [0, 6]
    let #[entry] ← IO.ofExcept (withdrawals.getObjValAs? (Array Lean.Json) "map")
      | throw <| IO.userError "Expected one withdrawal"
    expect entry ["k"] key
    expect entry ["v", "int"] (0 : Int)
    let redeemers ← dataField ctx [0, 9]
    let #[entry] ← IO.ofExcept (redeemers.getObjValAs? (Array Lean.Json) "map")
      | throw <| IO.userError "Expected one withdrawal redeemer"
    expect entry ["k"] (← dataField ctx [purposeIndex])
    expect entry ["v"] redeemer

-- A positive withdrawal contributes to the transaction balance. A negative
-- amount remains invalid even when the other amounts balance arithmetically.
#eval show IO Unit from do
  let input : ValidContext.Input := { isScript := false, hasDatum := false }
  for (amount, expected) in [(7, true), (0, true), (-1, false)] do
    let raw := ValidContext.withdrawalContext {} [input] [{ ada := input.ada + amount - 1 }] []
      input.addressHash amount
    unless Checker.validLedgerContext settings raw == expected do
      throw <| IO.userError s!"Unexpected withdrawal validity for {amount}"
  let model := ValidContext.modelContexts settings.toConfig.toLimits ["withdrawalAmount: 7"]
    (withdrawal := true)
  let replaysAmount (raw : PlutusCore.Data.Data) : Bool :=
    match raw with
    | .Constr 0 [.Constr 0 fields, _, _] =>
      (fields[6]?.any fun field => match field with
        | .Map [(_, .I 7)] => true
        | _ => false) && Checker.validLedgerContext settings raw
    | _ => false
  unless model.any replaysAmount do
    throw <| IO.userError "Could not reconstruct a balanced positive withdrawal"

end Tests.Equivalence.Withdrawal
