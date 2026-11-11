import CardanoLedgerApiFacts.Value
import CardanoLedgerApi.V2.Tx
import PlutusCoreFacts
import Blaster

namespace CardanoLedgerApi.V2.Tx
open IsData.Class
open PlutusCore.Integer (Integer)
open PlutusCore.Data (Data)

section BlasterFacts
set_option maxHeartbeats 0
set_option Elab.async false

/-- An inline datum read from the output's encoding. -/
@[blaster_library] theorem txOutInlineDatum_of_toData (o : TxOut) (i : Integer) (x : Data) (rest : List Data) :
    IsData.toData o.txOutDatum = Data.Constr i (x :: rest) → i = 2 → txOutInlineDatum o = some x := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

end BlasterFacts

end CardanoLedgerApi.V2.Tx
