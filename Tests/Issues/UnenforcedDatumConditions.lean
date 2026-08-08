import CardanoLedgerApi.V1
import CardanoLedgerApi.V2

/-!
# Regression: datum conditions the ledger does not enforce

See issue #8.

`validOutputs` (V1 and V2) and `validReferenceInput` (V2) previously required a
datum on script-address outputs and reference inputs. No era of the ledger
imposes either requirement, so these predicates excluded transactions that occur
on chain.

Because the predicates are the *hypothesis* of every theorem
(`validSpendingContext input → P input`), the effect was not a safety margin but
a silent narrowing: any theorem proved under them said nothing about the
excluded transactions while appearing to cover everything.

The examples below are contexts the ledger permits. Each evaluated to `false`
before the fix.
-/

namespace Tests.Issues.UnenforcedDatumConditions

/-! ## V1 — an output to a script address carrying no datum hash

Permitted by the ledger. It creates a UTxO that a V1 script cannot later spend,
but the *paying* transaction is valid and a validator can observe it. The rule
that appears to forbid this, `UnspendableUTxONoDatumHash`, is raised from
`txInsNoDataHash` — spent inputs, not outputs.
-/

namespace V1
open CardanoLedgerApi.V1

/-- An output paying 2 ada to a script address, with no datum hash attached. -/
def scriptOutputNoDatumHash : TxOut :=
  { txOutAddress     := ⟨.ScriptCredential "script-hash", none⟩
  , txOutValue       := lovelaceValue 2000000
  , txOutDatumHash   := none }

example : validOutputs [scriptOutputNoDatumHash] = true := by native_decide

/-- A public-key output is unaffected, and was accepted before the fix too. -/
def pubKeyOutput : TxOut :=
  { txOutAddress     := ⟨.PubKeyCredential "pub-key-hash", none⟩
  , txOutValue       := lovelaceValue 2000000
  , txOutDatumHash   := none }

example : validOutputs [pubKeyOutput] = true := by native_decide

/-- A malformed value is still rejected: the fix removed only the datum
    condition, not the value well-formedness one. Zero ada is not a valid
    `TxOut` value. -/
def scriptOutputZeroAda : TxOut :=
  { txOutAddress     := ⟨.ScriptCredential "script-hash", none⟩
  , txOutValue       := lovelaceValue 0
  , txOutDatumHash   := none }

example : validOutputs [scriptOutputZeroAda] = false := by native_decide

end V1

/-! ## V2 — outputs and reference inputs at script addresses carrying no datum -/

namespace V2
open CardanoLedgerApi.V2

/-- An output paying 2 ada to a script address, with no datum of any kind. -/
def scriptOutputNoDatum : TxOut :=
  { txOutAddress         := ⟨.ScriptCredential "script-hash", none⟩
  , txOutValue           := lovelaceValue 2000000
  , txOutDatum           := .NoOutputDatum
  , txOutReferenceScript := none }

example : validOutputs [scriptOutputNoDatum] = true := by native_decide

/-- A reference input resolving to a script address with no datum.

    No era imposes a datum requirement on reference inputs:
    `getInputDataHashesTxBody` inspects only `inputsTxBodyL` and never
    `referenceInputsTxBodyL`. Reference input datums are read from the resolved
    UTxO when the context is built, so there is nothing to witness. -/
def scriptReferenceInputNoDatum : TxInInfo :=
  { txInInfoOutRef   := ⟨"tx-id", 0⟩
  , txInInfoResolved := scriptOutputNoDatum }

example : validReferenceInput scriptReferenceInputNoDatum = true := by native_decide

/-- Value well-formedness is still enforced for reference inputs. -/
def referenceInputZeroAda : TxInInfo :=
  { txInInfoOutRef   := ⟨"tx-id", 0⟩
  , txInInfoResolved :=
      { txOutAddress         := ⟨.ScriptCredential "script-hash", none⟩
      , txOutValue           := lovelaceValue 0
      , txOutDatum           := .NoOutputDatum
      , txOutReferenceScript := none } }

example : validReferenceInput referenceInputZeroAda = false := by native_decide

end V2

end Tests.Issues.UnenforcedDatumConditions
