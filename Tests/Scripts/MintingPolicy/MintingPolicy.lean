import PlutusCore.UPLC
import CardanoLedgerApi.V3
import Blaster

namespace Tests.Scripts.MintingPolicy

open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext mintingInputs)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Term (Term)

#import_uplc mintingPolicy PlutusV3 single_cbor_hex "Tests/Scripts/MintingPolicy/minting_policy.flat"

def mintingPolicyInputs (paramsCs : ByteString) (ctx : ScriptContext) : List Term :=
  toTerm paramsCs :: mintingInputs ctx

#prep_uplc appliedMintingPolicy mintingPolicy mintingPolicyInputs 1200

end Tests.Scripts.MintingPolicy
