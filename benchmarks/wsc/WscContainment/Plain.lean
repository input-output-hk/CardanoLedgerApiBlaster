import WscContainment.Specification

namespace WscContainment
open CardanoLedgerApi.V3
open CardanoLedgerApi.IsData.Class (IsData)
open PlutusCore.UPLC.CekMachine (cekExecuteProgram)
open PlutusCore.UPLC.Utils (isSuccessful)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option stderrAsMessages false

/-- Every non-exempt asset in an accepted, valid context remains at the
    transaction-published base credential, accounting for signed mint/burn. -/
theorem successful_implies_programmable_token_containment_original :
    ∀ (pp : CurrencySymbol) (ctx : ScriptContext) (base : Credential)
      (directory currency : CurrencySymbol) (token : TokenName),
      validScriptContext ctx = true →
      Containment.parametersPublishedBy ctx = some (directory, IsData.toData base) →
      Containment.isProgrammable directory currency ctx.scriptContextTxInfo.txInfoReferenceInputs = true →
      isSuccessful (cekExecuteProgram programmableLogicGlobal.script
        (programmableLogicGlobalInputs pp ctx) 300000) →
      Containment.inputQuantityAt base currency token ctx.scriptContextTxInfo.txInfoInputs +
          valueOf currency token ctx.scriptContextTxInfo.txInfoMint ≤
        Containment.outputQuantityAt base currency token ctx.scriptContextTxInfo.txInfoOutputs := by
  blaster (timeout: 15) (gen-cex: 0)

theorem successful_implies_containment_or_exemption_original :
    ∀ (pp : CurrencySymbol) (ctx : ScriptContext) (base : Credential)
      (directory currency : CurrencySymbol) (token : TokenName),
      validScriptContext ctx = true →
      Containment.parametersPublishedBy ctx = some (directory, IsData.toData base) →
      isSuccessful (cekExecuteProgram programmableLogicGlobal.script
        (programmableLogicGlobalInputs pp ctx) 300000) →
      (Containment.inputQuantityAt base currency token ctx.scriptContextTxInfo.txInfoInputs +
          valueOf currency token ctx.scriptContextTxInfo.txInfoMint ≤
        Containment.outputQuantityAt base currency token ctx.scriptContextTxInfo.txInfoOutputs) ∨
      Containment.isExempt directory currency ctx.scriptContextTxInfo.txInfoReferenceInputs = true := by
  intro pp ctx base directory currency token valid parameters accepted
  by_cases exempt : Containment.isExempt directory currency ctx.scriptContextTxInfo.txInfoReferenceInputs = true
  · exact Or.inr exempt
  · apply Or.inl
    apply successful_implies_programmable_token_containment_original pp ctx base directory currency token
      valid parameters ?_ accepted
    simpa only [Containment.isProgrammable, Bool.not_eq_true'] using Bool.eq_false_iff.mpr exempt

end WscContainment

#print axioms WscContainment.successful_implies_programmable_token_containment_original
#print axioms WscContainment.successful_implies_containment_or_exemption_original
