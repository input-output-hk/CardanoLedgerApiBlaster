import CardanoLedgerApi.V3.Contexts
import CardanoLedgerApiFacts.OutputValues
import PlutusCoreFacts.Data

namespace CardanoLedgerApi.V1.Contexts
open PlutusCore.Data (Data)
open CardanoLedgerApi.V1
/-- Encoded map equality preserves the quantity observed at any asset key. -/
@[blaster_library] theorem valueOf_eqData (cs : CurrencySymbol) (tn : TokenName) (xs ys : Value) :
    PlutusCore.Data.eqData (Data.Map xs) (Data.Map ys) = true →
      valueOf cs tn xs = valueOf cs tn ys := by
  blaster (summaries: [PlutusCore.Data.eqData_true_imp_eq (Data.Map xs) (Data.Map ys)])
    (timeout: 5) (gen-cex: 0)

@[blaster_library] theorem valueOf_eqDataMap (cs : CurrencySymbol) (tn : TokenName) (xs ys : Value) :
    PlutusCore.Data.eqDataMap xs ys = true → valueOf cs tn xs = valueOf cs tn ys := by
  blaster (summaries: [PlutusCore.Data.eqDataMap_true_imp_eq xs ys]) (timeout: 5) (gen-cex: 0)

/-- A value with empty currency and token tails contains exactly one asset. -/
@[blaster_library] theorem valueOf_singleton_tails
    (cs currency : CurrencySymbol) (tn token : TokenName) (quantity : Int)
    (tokens currencies : Value) :
    tokens.isEmpty = true → currencies.isEmpty = true →
      valueOf cs tn ((Data.B currency, Data.Map ((Data.B token, Data.I quantity) :: tokens)) :: currencies) =
        if cs = currency ∧ tn = token then quantity else 0 := by
  cases tokens <;> cases currencies <;> blaster (timeout: 5) (gen-cex: 0)

end CardanoLedgerApi.V1.Contexts

namespace CardanoLedgerApi.V2.Contexts
@[blaster_library] theorem validOutputs_cons (output : CardanoLedgerApi.V2.TxOut) (rest : List CardanoLedgerApi.V2.TxOut) :
    CardanoLedgerApi.V2.validOutputs (output :: rest) = true →
      CardanoLedgerApi.V2.validTxOutValue output.txOutValue = true ∧ CardanoLedgerApi.V2.validOutputs rest = true := by
  blaster (timeout: 5) (gen-cex: 0)

@[blaster_library] theorem validOutputs_all_values (outputs : List CardanoLedgerApi.V2.TxOut) :
    CardanoLedgerApi.V2.validOutputs outputs = true →
      (outputs.all fun output => CardanoLedgerApi.V2.validTxOutValue output.txOutValue) = true := by
  induction outputs with
  | nil => blaster (timeout: 5) (gen-cex: 0)
  | cons output rest ih =>
    blaster (summaries: [validOutputs_cons output rest]) (timeout: 5) (gen-cex: 0)

end CardanoLedgerApi.V2.Contexts
