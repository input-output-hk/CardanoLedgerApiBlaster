import CardanoLedgerApi.V1.Value
import PlutusCoreFacts
import Blaster

namespace CardanoLedgerApi.V1.Value
open IsData.Class
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)

section BlasterFacts
open PlutusCore.Value (dataQuantity findToken)
set_option maxHeartbeats 0
set_option Elab.async false

@[blaster_library] theorem valueOf.find_token_eq (tn : ByteString) (tns : List (Data × Data)) :
    valueOf.find_token tn tns = findToken tn tns := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem valueOf_eq_dataQuantity (cs : CurrencySymbol) (tn : TokenName) (v : Value) :
    valueOf cs tn v = dataQuantity cs tn v := by
  blaster (induction: auto) (summaries: [valueOf.find_token_eq]) (timeout: 20) (gen-cex: 0)

/-- `valueOf` of a cons depends on the head and on `valueOf` of the tail only. -/
@[blaster_library] theorem valueOf_cons_congr (h : Data × Data) (xs ys : Value) (cs : CurrencySymbol) (tn : TokenName) :
    valueOf cs tn xs = valueOf cs tn ys → valueOf cs tn (h :: xs) = valueOf cs tn (h :: ys) := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

/-- An entry of another currency is skipped. -/
@[blaster_library] theorem valueOf_cons_skip (k : Data) (toks : List (Data × Data)) (xs : Value) (cs : CurrencySymbol) (tn : TokenName) :
    (Data.B cs == k) = false → valueOf cs tn ((k, Data.Map toks) :: xs) = valueOf cs tn xs := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

/-- An entry of another currency is skipped, unless it stops the walk (a
malformed entry, value 0). -/
@[blaster_library] theorem valueOf_cons_other (k v : Data) (xs : Value) (cs : CurrencySymbol) (tn : TokenName) :
    (Data.B cs == k) = false →
      valueOf cs tn ((k, v) :: xs) = valueOf cs tn xs ∨ valueOf cs tn ((k, v) :: xs) = 0 := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

/-- `valueOf` of a cons is monotone in the tail. -/
@[blaster_library] theorem valueOf_cons_mono (h : Data × Data) (xs ys : Value) (cs : CurrencySymbol) (tn : TokenName) :
    valueOf cs tn xs ≤ valueOf cs tn ys → valueOf cs tn (h :: xs) ≤ valueOf cs tn (h :: ys) := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

/-- An entry of another currency is skipped when every entry carries a token map. -/
@[blaster_library] theorem valueOf_cons_mapEntries (k v : Data) (xs : Value) (cs : CurrencySymbol) (tn : TokenName) :
    PlutusCore.Value.Internal.mapEntries ((k, v) :: xs) = true → (Data.B cs == k) = false →
      valueOf cs tn ((k, v) :: xs) = valueOf cs tn xs := by
  blaster (timeout: 20) (gen-cex: 0)

/-- The builtin value decoded from a ledger value reads the same quantities. -/
@[blaster_library] theorem unValueData_toData_lookup (v : Value) (w : PlutusCore.Value.Value)
    (cs : CurrencySymbol) (tn : TokenName) :
    PlutusCore.Value.unValueData (IsData.toData v) = .ok w →
      PlutusCore.Value.lookupCoin cs tn w = valueOf cs tn v := by
  blaster (summaries: [PlutusCore.Value.Internal.unValueData_lookup cs tn (IsData.toData v) w, valueOf_eq_dataQuantity cs tn v]) (timeout: 20) (gen-cex: 0)

/-- The builtin value decoded from an encoded value map reads the same quantities. -/
@[blaster_library] theorem unValueData_map_lookup (l : Value) (w : PlutusCore.Value.Value)
    (cs : CurrencySymbol) (tn : TokenName) :
    PlutusCore.Value.unValueData (Data.Map l) = .ok w →
      PlutusCore.Value.lookupCoin cs tn w = valueOf cs tn l := by
  blaster (summaries: [PlutusCore.Value.Internal.unValueData_lookup cs tn (Data.Map l) w, valueOf_eq_dataQuantity cs tn l]) (timeout: 20) (gen-cex: 0)

/-- `unValueData_map_lookup` for the builtin `mapData` encoding. -/
@[blaster_library] theorem unValueData_mapData_lookup (l : Value) (w : PlutusCore.Value.Value)
    (cs : CurrencySymbol) (tn : TokenName) :
    PlutusCore.Value.unValueData (PlutusCore.Data.mapData l) = .ok w →
      PlutusCore.Value.lookupCoin cs tn w = valueOf cs tn l := by
  blaster (summaries: [unValueData_map_lookup l w cs tn]) (timeout: 20) (gen-cex: 0)

end BlasterFacts

end CardanoLedgerApi.V1.Value
