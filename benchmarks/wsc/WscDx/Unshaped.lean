import WscDx.Specification

namespace WscDx

open CardanoLedgerApi.V3 (CurrencySymbol ScriptContext)
open PlutusCore.UPLC.Utils (isSuccessful)

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option stderrAsMessages false

/-- Original unshaped DX workload. The historical 300,000-step budget is
preserved; this is an opt-in proof attempt, not an established theorem. -/
#eval IO.eprintln "DX: starting 300000-step #prep_uplc"
#prep_uplc appliedGlobalUCeiling productionGlobal globalInputs 300000
#eval IO.eprintln "DX: preparation completed; attempting unshaped P1"

def P1_unshaped_stmt : Prop :=
  P1UnshapedFormH (fun (ppCS : CurrencySymbol) (ctx : ScriptContext) =>
    isSuccessful (appliedGlobalUCeiling.prop ppCS ctx))

theorem P1_unshaped : P1_unshaped_stmt := by blaster (timeout: 1800)

end WscDx

#print axioms WscDx.P1_unshaped
