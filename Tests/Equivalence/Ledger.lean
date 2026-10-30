import Tests.Equivalence.Support
import Equivalence.Ledger

namespace Tests.Equivalence.Ledger

open _root_.Equivalence
open PlutusCore.Data (Data)
open Support

def fixture (datum : Data) : Data :=
  let ref := Context.outputReference ⟨String.mk (List.replicate 32 'r')⟩
  let address := Context.scriptAddress ⟨String.mk (List.replicate 28 's')⟩
  let receiver := Context.pubKeyAddress ⟨String.mk (List.replicate 28 'p')⟩
  let input := Context.txInput ref (Context.txOutput address (Context.lovelace 10000000) (some datum))
  let output := Context.txOutput receiver (Context.lovelace 9800000)
  let tx := ({ fee := .I 200000, outputs := .List [output] } : Context.RawUnusedTxInfo).txInfo
    [input] [] 1700000000000 1700000000100
  Context.spendingContext tx (.Constr 0 []) ref datum

def rawDatums : Data → Option (Data × Data)
  | .Constr _ [.Constr _ info, _, .Constr _ [reference, .Constr _ [datum]]] => do
    let .List inputs ← info[0]? | none
    let input ← inputs.find? (fun input => match input with
      | .Constr _ [ref, _] => ref == reference
      | _ => false)
    let .Constr _ [_, .Constr _ [_, _, .Constr 2 [inline], _]] := input | none
    return (datum, inline)
  | _ => none

#eval show IO Unit from do
  -- An application-invalid datum can still satisfy the ledger model.
  unless _root_.Equivalence.Ledger.validContext (fixture (.I 0)) do
    throw <| IO.userError s!"Positive ledger control failed: {(_root_.Equivalence.Ledger.audit (fixture (.I 0))).pretty}"
  -- Changing only ScriptInfo reproduces the former unreachable mutation.
  let mismatch := Context.modifyField (fixture (.I 0)) 2 (Context.mapSpendingDatum (fun _ => .I 1))
  if _root_.Equivalence.Ledger.validContext mismatch then
    throw <| IO.userError "Ledger model accepted inconsistent datums"
  let genericConfig := { config with inputs := "valid-context", rawContext := false }
  let some generic := Cli.nativeDomainWitness genericConfig
    | throw <| IO.userError "No generic ledger-model-valid context"
  unless Cli.validLedgerContext genericConfig generic do
    throw <| IO.userError "Invalid generic context witness"
  -- The generic mode covers non-spending script purposes too.
  let some decoded := _root_.Equivalence.Ledger.decode generic
    | throw <| IO.userError "Generic witness did not decode"
  let policy : PlutusCore.ByteString.ByteString := ⟨String.mk (List.replicate 28 'a')⟩
  let mint := [(Data.B policy, Data.Map [(.B "token", .I 1)])]
  let outputs := decoded.scriptContextTxInfo.txInfoOutputs.map fun output =>
    { output with txOutValue := CardanoLedgerApi.V2.add policy "token" 1 output.txOutValue }
  let minting := { decoded with
    scriptContextScriptInfo := .MintingScript policy
    scriptContextTxInfo := { decoded.scriptContextTxInfo with
      txInfoMint := mint
      txInfoOutputs := outputs
      txInfoRedeemers := [(.Minting policy, decoded.scriptContextRedeemer)] } }
  let rawMinting := CardanoLedgerApi.IsData.Class.IsData.toData minting
  unless Cli.validLedgerContext genericConfig rawMinting &&
      !_root_.Equivalence.Ledger.validContext rawMinting do
    throw <| IO.userError s!"Generic mode rejected valid minting context: {(Cli.auditLedgerContext genericConfig rawMinting).pretty}"
  for mode in ["htlc-claim", "htlc-refund", "vesting-full", "vesting-partial",
      "escrow-deposit", "escrow-accept", "escrow-refund"] do
    let selected := { config with inputs := mode, rawContext := false, caseIndex := some 0 }
    let some raw := Cli.nativeDomainWitness selected
      | throw <| IO.userError s!"No ledger-model-valid witness for {mode}"
    unless _root_.Equivalence.Ledger.validContext raw do
      throw <| IO.userError s!"Invalid domain witness for {mode}"
  for variation in ["fee-zero"] do
    let selected := selectFamily config "htlc-claim" 0 variation
    unless (Cli.nativeDomainWitness selected).isNone do
      throw <| IO.userError s!"Unexpected valid witness for {variation}"
  for (mode, index, variations) in [
      ("htlc-claim", 45, ["hash-empty", "hash-empty,inputs-one", "inputs-three,hash-empty",
        "hash-empty,input-fields", "datum-malformed", "recipient", "datum-any,inputs-one"]),
      ("vesting-partial", 81, ["datum-total", "datum-schedule,inputs-one", "beneficiary", "asset-policy", "datum-any"]),
      ("escrow-accept", 12, ["state-accepted", "datum-malformed", "datum-time,input-value", "datum-any"])] do
    for variation in variations do
      let selected := selectFamily config mode index variation
      let args := (Cli.contextFamilies selected)[0]! { datum := .I 42 } {} [] [] [] 200
      let [.Const (.Data raw)] := args | throw <| IO.userError "Expected one context"
      let some (datum, inline) := rawDatums raw | throw <| IO.userError s!"Missing datum in {mode}, {variation}"
      unless datum == inline do
        throw <| IO.userError s!"Inconsistent datum in {mode}, {variation}"

  -- Updating one UTxO must leave the independent second input's datum intact.
  let selected := selectFamily config "htlc-claim" 45 "hash-empty"
  let [.Const (.Data raw)] := (Cli.contextFamilies selected)[0]! {} {} [] [] [] 200
    | throw <| IO.userError "Expected one context"
  let some decoded := _root_.Equivalence.Ledger.decode raw | throw <| IO.userError "Context did not decode"
  let some second := decoded.scriptContextTxInfo.txInfoInputs[1]? | throw <| IO.userError "Missing second input"
  unless second.txInInfoResolved.txOutDatum == .OutputDatum HTLC.datum do
    throw <| IO.userError "Changed an unrelated input's datum"

-- The default context policy and explicit raw opt-out use the production parser.
#eval show IO Unit from do
  let settings : Cli.Config := { scripts := #["old", "new"], budget := some (100000000, 1000000) }
  let parsed ← IO.ofExcept (Cli.parse settings [])
  unless parsed.inputs == "valid-context" do throw <| IO.userError "Default input mode is not valid-context"
  let raw ← IO.ofExcept (Cli.parse settings ["--inputs", "data"])
  unless raw.inputs == "data" do throw <| IO.userError "Raw Data opt-out was not parsed"
  for args in [["--raw-context"], ["--language", "PlutusV2"], ["--case", "0"]] do
    unless (Cli.parse settings args).toOption.isNone do
      throw <| IO.userError s!"Invalid generic context options accepted: {args}"

#eval show IO Unit from do
  let settings : Cli.Config := { budget := some (100000000, 1000000), timeout := 5 }
  let accept := "(lam c (con unit ()))"
  let reject := "(lam c (error))"
  let report ← comparePrograms accept accept settings
  verdict report "preserved"
  expect report ["ledger_validity", "predicate"] "CardanoLedgerApi.V3.validScriptContext"
  expect report ["old_acceptance_witness", "ledger_validity", "valid"] true
  expect report ["proof_domain"] "unrestricted Data overapproximation"
  let explicit ← comparePrograms accept accept { settings with inputs := "valid-context" }
  verdict explicit "preserved"
  expect explicit ["input_domain"] (← field report ["input_domain"])

  let report ← comparePrograms accept reject settings
  verdict report "regression"
  expect (← witness report) ["ledger_validity", "valid"] true
  let zero := "[[(builtin equalsData) c] (con data (I 0))]"
  let report ← comparePrograms accept (rejectIf zero) settings
  verdict report "inconclusive"
  noCounterexample report
  let report ← comparePrograms (acceptIf zero) (acceptIf zero) settings
  verdict report "inconclusive"
  expect report ["inconclusive_reason"] "old_acceptance_unestablished"
  let report ← comparePrograms (acceptIf zero) (acceptIf zero) { settings with inputs := "data" }
  verdict report "preserved"
  expect report ["old_acceptance_witness", "input"]
    (Lean.Json.mkObj [("int", Lean.toJson (0 : Int))])

  let report ← comparePrograms reject reject { settings with budget := some (100, 100) }
  verdict report "vacuously_preserved"
  expect report ["ledger_validity", "valid"] true

#eval show IO Unit from do
  let settings := selectFamily { acceptanceConfig with rawContext := false } "htlc-claim" 0 "baseline"
  let accept := "(lam c (con unit ()))"
  let report ← comparePrograms accept accept settings
  verdict report "preserved"
  expect report ["domain_status"] "nonempty"
  expect report ["ledger_validity", "valid"] true
  expect report ["old_acceptance_witness", "ledger_validity", "valid"] true
  let report ← comparePrograms accept accept { settings with variation := "fee-zero" }
  verdict report "inconclusive"
  expect report ["domain_status"] "unestablished"
  let report ← comparePrograms accept (rejectDataAt [0, 3] "I 0") settings
  verdict report "inconclusive"
  noCounterexample report
  let report ← comparePrograms accept "(lam c (error))" settings
  verdict report "regression"
  expect (← witness report) ["ledger_validity", "valid"] true
  let zeroFee := acceptIf s!"[[(builtin equalsData) {contextFieldTerm [0, 3]}] (con data (I 0))]"
  let report ← comparePrograms zeroFee zeroFee settings
  verdict report "inconclusive"
  expect report ["inconclusive_reason"] "old_acceptance_unestablished"

end Tests.Equivalence.Ledger
