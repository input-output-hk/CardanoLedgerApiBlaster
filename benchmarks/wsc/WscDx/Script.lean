import Blaster
import CardanoLedgerApi.V3
import PlutusCore.UPLC

namespace WscDx

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext CurrencySymbol rewardingInputs)
open PlutusCore.UPLC.Term (Term)

#import_uplc productionGlobal PlutusV3 double_cbor_hex
  "fixtures/wsc-dx/programmableLogicGlobal-2306678.flat"

/-- The original DX application order: protocol-parameter policy, then the
    rewarding context. Every context field remains symbolic. -/
def globalInputs (protocolParamsCS : CurrencySymbol) (ctx : ScriptContext) : List Term :=
  toTerm protocolParamsCS :: rewardingInputs ctx

end WscDx
