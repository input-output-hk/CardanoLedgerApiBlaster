import CardanoLedgerApi.V3.Contexts

namespace Tests.RawFieldDecoding

open PlutusCore.Data (Data)
open CardanoLedgerApi.IsData.Class

private def validInfo : CardanoLedgerApi.V3.Contexts.TxInfo :=
  { txInfoInputs := []
    txInfoReferenceInputs := []
    txInfoOutputs := []
    txInfoFee := 0
    txInfoMint := []
    txInfoTxCerts := []
    txInfoWdrl := []
    txInfoValidRange := IsData.toData CardanoLedgerApi.V1.Time.everything
    txInfoSignatories := []
    txInfoRedeemers := []
    txInfoData := []
    txInfoId := ""
    txInfoVotes := []
    txInfoProposalProcedures := []
    txInfoCurrentTreasuryAmount := Data.Constr 1 []
    txInfoTreasuryDonation := Data.Constr 1 [] }

example : CardanoLedgerApi.V3.Contexts.hasDecodableRawFields validInfo = true := by decide
example : CardanoLedgerApi.V3.Contexts.hasDecodableRawFields
    { validInfo with txInfoValidRange := Data.B "" } = false := by decide
example : CardanoLedgerApi.V3.Contexts.hasDecodableRawFields
    { validInfo with txInfoCurrentTreasuryAmount := Data.B "" } = false := by decide
example : CardanoLedgerApi.V3.Contexts.hasDecodableRawFields
    { validInfo with txInfoTreasuryDonation := Data.B "" } = false := by decide

-- A malformed Data value is not the Haskell `Nothing` constructor.
example : CardanoLedgerApi.V3.Contexts.validTreasuryAmount (Data.B "") = false := by decide
example : CardanoLedgerApi.V3.Contexts.validTreasuryDonation (Data.B "") = false := by decide

example : CardanoLedgerApi.V3.Contexts.validTreasuryAmount (Data.Constr 1 []) = true := by decide
example : CardanoLedgerApi.V3.Contexts.validTreasuryDonation (Data.Constr 1 []) = true := by decide

example : CardanoLedgerApi.V3.Contexts.validTreasuryAmount (Data.Constr 0 [Data.I 10]) = true := by decide
example : CardanoLedgerApi.V3.Contexts.validTreasuryDonation (Data.Constr 0 [Data.I 0]) = false := by decide

end Tests.RawFieldDecoding
