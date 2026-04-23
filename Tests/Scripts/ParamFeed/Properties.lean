import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Tests.Scripts.ParamFeed.ParamFeed
import Blaster

namespace Tests.Scripts.ParamFeed
open CardanoLedgerApi.V3 (ScriptContext)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Utils

set_option warn.sorry false

def isMatchingOraclePriceParams : Data → Data → Data → Prop
  | .List (.B b1 :: .B b2 :: _), .B p2, .B p3 => b1 = p2 ∧ b2 = p3
  | _, _, _ => False

theorem successful_imp_valid_params :
  ∀ (params1 params2 params3 : Data) (ctx : ScriptContext),
     isSuccessful (appliedParamFeed.prop params1 params2 params3 ctx) →
     isMatchingOraclePriceParams params1 params2 params3 := by blaster

end Tests.Scripts.ParamFeed
