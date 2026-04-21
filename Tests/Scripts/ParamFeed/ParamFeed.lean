import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster

namespace Tests.Scripts.ParamFeed
open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext spendingInputs)
open PlutusCore.Data (Data)
open PlutusCore.UPLC.Term (Term)
open PlutusCore.UPLC.Utils

set_option warn.sorry false

#import_uplc oracleFeed PlutusV3 flat_hex "Tests/Scripts/ParamFeed/param_feed.flat"

def oracleInputs (params1 params2 params3 : Data) (ctx : ScriptContext) : List Term :=
  toTerm params1 :: toTerm params2 :: toTerm params3 :: spendingInputs ctx

#prep_uplc appliedParamFeed oracleFeed oracleInputs 10000

end Tests.Scripts.ParamFeed
