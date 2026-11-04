import CardanoLedgerApi.V3.Contexts

namespace Tests.TreasuryDecoding

open PlutusCore.Data (Data)

-- A malformed Data value is not the Haskell `Nothing` constructor.
example : CardanoLedgerApi.V3.Contexts.validTreasuryAmount (Data.B "") = false := by decide
example : CardanoLedgerApi.V3.Contexts.validTreasuryDonation (Data.B "") = false := by decide

example : CardanoLedgerApi.V3.Contexts.validTreasuryAmount (Data.Constr 1 []) = true := by decide
example : CardanoLedgerApi.V3.Contexts.validTreasuryDonation (Data.Constr 1 []) = true := by decide

example : CardanoLedgerApi.V3.Contexts.validTreasuryAmount (Data.Constr 0 [Data.I 10]) = true := by decide
example : CardanoLedgerApi.V3.Contexts.validTreasuryDonation (Data.Constr 0 [Data.I 0]) = false := by decide

end Tests.TreasuryDecoding
