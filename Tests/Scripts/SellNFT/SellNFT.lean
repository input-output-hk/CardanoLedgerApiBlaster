import PlutusCore.UPLC
import CardanoLedgerApi.V2

namespace Tests.Scripts.SellNFT
open CardanoLedgerApi.V2 (spendingInputs)

#import_uplc sellNFT PlutusV2 single_cbor_hex "Tests/Scripts/SellNFT/sell_nft.flat"

#prep_uplc appliedSellNFT sellNFT spendingInputs 1800


end Tests.Scripts.SellNFT
