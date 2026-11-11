import Blaster
import CardanoLedgerApi.V3
import PlutusCore.UPLC

namespace WscContainment

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Term (Term)

/-!
`programmableLogicGlobal` is the WSC/CIP-143 global rewarding validator. It is
unapplied in the fixture, so its protocol-parameter state-token currency symbol
is supplied before the symbolic V3 `ScriptContext`.
-/

#import_uplc programmableLogicGlobal PlutusV3 double_cbor_hex
  "fixtures/wsc-poc/programmableLogicGlobal-2e815a1.flat"

def programmableLogicGlobalInputs
    (protocolParametersCurrencySymbol : ByteString)
    (ctx : ScriptContext) : List Term :=
  [toTerm protocolParametersCurrencySymbol, toTerm ctx]

end WscContainment
