import PlutusCore.UPLC
import CardanoLedgerApi.V3

namespace Tests.Scripts.Governance
open CardanoLedgerApi.IsData.Class (toTerm)
open CardanoLedgerApi.V3 (ScriptContext proposingInputs)
open PlutusCore.ByteString (ByteString)
open PlutusCore.UPLC.Term (Term)

#import_uplc governance PlutusV3 single_cbor_hex "Tests/Scripts/Governance/governance.flat"

#prep_uplc appliedGovernance governance proposingInputs 9000

end Tests.Scripts.Governance
