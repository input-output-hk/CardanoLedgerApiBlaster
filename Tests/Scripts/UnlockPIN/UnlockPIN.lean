import PlutusCore.UPLC
import CardanoLedgerApi.V2

namespace Tests.Scripts.UnlockPIN
open CardanoLedgerApi.V2 (spendingInputs)


#import_uplc unlockPIN PlutusV2 single_cbor_hex "Tests/Scripts/UnlockPIN/unlock_pin.flat"

#prep_uplc appliedUnlockPIN unlockPIN spendingInputs 10000

end Tests.Scripts.UnlockPIN
