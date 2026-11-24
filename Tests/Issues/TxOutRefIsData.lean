import CardanoLedgerApi.V1

open CardanoLedgerApi.V1
open CardanoLedgerApi.IsData.Class

namespace Tests.Issues.TxOutRefIsData

def reference : TxOutRef := ⟨"tx-id", 5⟩

-- TxId's IsData instance uses Constr 0 [B id], so TxOutRef must decode it.
example : (IsData.fromData (IsData.toData reference) : Option TxOutRef) = some reference := by
  native_decide

end Tests.Issues.TxOutRefIsData
