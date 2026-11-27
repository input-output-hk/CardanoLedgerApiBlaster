import Tests.Equivalence.Support
import Equivalence.Ledger

namespace Tests.Equivalence.Ledger

open _root_.Equivalence
open PlutusCore.Data (Data)
open Support

def fixture (datum : Data) (paid : Int := 9800000) (withdrawals : Data := .Map []) : Data :=
  let ref := Context.outputReference ⟨String.mk (List.replicate 32 'r')⟩
  let address := Context.scriptAddress ⟨String.mk (List.replicate 28 's')⟩
  let receiver := Context.pubKeyAddress ⟨String.mk (List.replicate 28 'p')⟩
  let input := Context.txInput ref (Context.txOutput address (Context.lovelace 10000000) (some datum))
  let output := Context.txOutput receiver (Context.lovelace paid)
  let tx := ({ fee := .I 200000, outputs := .List [output], withdrawals } : Context.RawUnusedTxInfo).txInfo
    [input] [] 1700000000000 1700000000100
  Context.spendingContext tx (.Constr 0 []) ref datum

#eval show IO Unit from do
  let credential (key : PlutusCore.ByteString.ByteString) := Data.Constr 0 [.B key]
  let first := credential ⟨String.mk (List.replicate 28 'a')⟩
  let second := credential ⟨String.mk (List.replicate 28 'b')⟩
  let rewards := Data.Map [(first, .I 1000000), (second, .I 2000000)]
  let valid paid withdrawals := _root_.Equivalence.Ledger.validContext (fixture (.I 0) paid withdrawals)
  unless valid 12800000 rewards && valid 9800000 (.Map [(first, .I 0)]) do
    throw <| IO.userError "Ledger model rejected a balanced reward withdrawal"
  if valid 9800000 rewards || valid 8800000 (.Map [(first, .I (-1000000))]) then
    throw <| IO.userError "Ledger model accepted unaccounted rewards or a negative withdrawal"

#eval show IO Unit from do
  -- An application-invalid datum can still satisfy the ledger model.
  unless _root_.Equivalence.Ledger.validContext (fixture (.I 0)) do
    throw <| IO.userError s!"Positive ledger control failed: {(_root_.Equivalence.Ledger.audit (fixture (.I 0))).pretty}"
  -- Changing only ScriptInfo reproduces the former unreachable mutation.
  let mismatch := Support.modifyField (fixture (.I 0)) 2 (Support.mapSpendingDatum (fun _ => .I 1))
  if _root_.Equivalence.Ledger.validContext mismatch then
    throw <| IO.userError "Ledger model accepted inconsistent datums"
  let genericConfig := { config with inputs := "valid-context" }
  let some generic := Checker.nativeDomainWitness genericConfig
    | throw <| IO.userError "No generic ledger-model-valid context"
  unless Checker.validLedgerContext genericConfig generic do
    throw <| IO.userError "Invalid generic context witness"
  -- Ledger-valid minting contexts are outside this spending profile.
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
  unless !Checker.validLedgerContext genericConfig rawMinting &&
      _root_.Equivalence.Ledger.validScriptContext rawMinting &&
      !_root_.Equivalence.Ledger.validContext rawMinting do
    throw <| IO.userError s!"Spending profile admitted minting context: {(Checker.auditLedgerContext genericConfig rawMinting).pretty}"
#eval show IO Unit from do
  let settings : Support.Config := { acceptanceConfig with budget := some (100000000, 1000000), timeout := 60, wallTimeout := 240 }
  let accept := "(lam c (con unit ()))"
  let reject := "(lam c (error))"
  let report ← comparePrograms accept accept settings
  verdict report "preserved"
  expect report ["ledger_validity", "predicate"] "CardanoLedgerApi.V3.validSpendingContext"
  expect report ["old_acceptance_witness", "ledger_validity", "valid"] true
  expect report ["proof_domain"] "ledger-valid structured spending contexts"
  let explicit ← comparePrograms accept accept { settings with inputs := "valid-context" }
  verdict explicit "preserved"
  expect explicit ["input_domain"] (← field report ["input_domain"])

  let report ← comparePrograms accept reject settings
  verdict report "regression"
  expect (← witness report) ["ledger_validity", "valid"] true
  let zero := "[[(builtin equalsData) c] (con data (I 0))]"
  let report ← comparePrograms accept (rejectIf zero) settings
  verdict report "preserved"
  noCounterexample report
  let report ← comparePrograms (acceptIf zero) (acceptIf zero) settings
  verdict report "vacuously_preserved"

  let report ← comparePrograms reject reject { settings with budget := some (100, 100) }
  verdict report "vacuously_preserved"
  expect report ["ledger_validity", "valid"] true

#eval show IO Unit from do
  let settings := { acceptanceConfig with inputs := "valid-context" }
  let accept := "(lam c (con unit ()))"
  let report ← comparePrograms accept accept settings
  verdict report "preserved"
  expect report ["domain_status"] "nonempty"
  expect report ["ledger_validity", "valid"] true
  expect report ["old_acceptance_witness", "ledger_validity", "valid"] true
  -- Seed 4 keeps the zero-fee preservation query within the test deadline.
  let report ← comparePrograms accept (rejectDataAt [0, 3] "I 0") { settings with solverSeed := some 4 }
  verdict report "preserved"
  noCounterexample report
  let malformedFee ← comparePrograms accept (rejectDataAt [0, 3] "B #00") settings
  verdict malformedFee "preserved"
  noCounterexample malformedFee
  expect malformedFee ["old_acceptance_witness", "replayed"] true
  let report ← comparePrograms accept "(lam c (error))" settings
  verdict report "regression"
  expect (← witness report) ["ledger_validity", "valid"] true
  let zeroFee := acceptIf s!"[[(builtin equalsData) {contextFieldTerm [0, 3]}] (con data (I 0))]"
  let report ← comparePrograms zeroFee zeroFee settings
  verdict report "vacuously_preserved"

end Tests.Equivalence.Ledger
