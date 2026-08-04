import CardanoLedgerApi.V1.Contexts
import CardanoLedgerApi.V1.Credential
import CardanoLedgerApi.V3.Contexts

/-!
# Regression guards: `ScriptPurpose` / `Credential` orderings

These examples pin the orderings used by `validRedeemerMap` / `validWithdrawals`
to the order in which the **Cardano ledger** emits the corresponding maps into
`TxInfo`, which is *not* the Plutus constructor order.  Each of them fails on the
constructor-order definitions.

Ledger citations (cardano-ledger @ `cd8b7fab8`):

* redeemer map — `transTxRedeemers = unsafeFromList <$> mapM … (Map.toList …)`
  (`eras/babbage/impl/src/Cardano/Ledger/Babbage/TxInfo.hs:217-221`, used for V3
  at `eras/conway/impl/src/Cardano/Ledger/Conway/TxInfo.hs:499,512`) does not
  re-sort, so the key order is the derived `Ord` of `ConwayPlutusPurpose`
  (`eras/conway/impl/src/Cardano/Ledger/Conway/Scripts.hs:202-213`):
  `Spending < Minting < Certifying < Rewarding < Voting < Proposing`
  (V1/V2: `AlonzoPlutusPurpose`,
  `eras/alonzo/impl/src/Cardano/Ledger/Alonzo/Scripts.hs:308-313`, same sequence
  restricted to the first four kinds);
* withdrawal map — `txInfoWdrl = transMap … (unWithdrawals …)`
  (`eras/conway/impl/src/Cardano/Ledger/Conway/TxInfo.hs:544-546,692-694`) is
  keyed by `Credential`, whose derived `Ord`
  (`libs/cardano-ledger-core/src/Cardano/Ledger/Credential.hs:96-99`) is
  `ScriptHashObj < KeyHashObj`.
-/

namespace Tests.LedgerOrdering

open CardanoLedgerApi

private def ref : V1.Tx.TxOutRef := ⟨"", 0⟩
private def ref3 : V3.Tx.TxOutRef := ⟨"", 0⟩

/-! ## V3 `ScriptPurpose`: `Spending < Minting` -/

-- A transaction that both spends and mints emits the spending redeemer first.
example : V3.Contexts.ltScriptPurpose (.Spending ref3) (.Minting "") = true := by decide
example : V3.Contexts.ltScriptPurpose (.Minting "") (.Spending ref3) = false := by decide

-- `Certifying < Rewarding`, likewise reversed before.
private def cert3 : V3.TxCert.TxCert := .TxCertRegStaking (.ScriptCredential "") none

example :
    V3.Contexts.ltScriptPurpose (.Certifying 0 cert3) (.Rewarding (.ScriptCredential "")) = true := by
  decide
example :
    V3.Contexts.ltScriptPurpose (.Rewarding (.ScriptCredential "")) (.Certifying 0 cert3) = false := by
  decide

/-! ## V1/V2 `ScriptPurpose`: same defect, `AlonzoPlutusPurpose` order -/

example : V1.Contexts.ltScriptPurpose (.Spending ref) (.Minting "") = true := by decide
example : V1.Contexts.ltScriptPurpose (.Minting "") (.Spending ref) = false := by decide
example :
    V1.Contexts.ltScriptPurpose (.Certifying .DCertGenesis)
      (.Rewarding (.StakingHash (.PubKeyCredential ""))) = true := by
  decide

/-! ## `Credential`: `ScriptCredential < PubKeyCredential` -/

example : V1.Credential.ltCredential (.ScriptCredential "") (.PubKeyCredential "") = true := by
  decide
example : V1.Credential.ltCredential (.PubKeyCredential "") (.ScriptCredential "") = false := by
  decide

end Tests.LedgerOrdering
