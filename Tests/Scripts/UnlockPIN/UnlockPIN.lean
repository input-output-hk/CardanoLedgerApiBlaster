import PlutusCore.UPLC
import CardanoLedgerApi.V3

namespace Tests.Scripts.UnlockPIN
open CardanoLedgerApi.V3 (spendingInputs)


#import_uplc unlockPIN PlutusV3 single_cbor_hex "Tests/Scripts/UnlockPIN/unlock_pin.flat"

#prep_uplc appliedUnlockPIN unlockPIN spendingInputs 10000

end Tests.Scripts.UnlockPIN
