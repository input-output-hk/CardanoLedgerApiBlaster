import CardanoLedgerApiFacts.Value
import CardanoLedgerApi.V1.Contexts
import PlutusCoreFacts
import Blaster

namespace CardanoLedgerApi.V1.Contexts
open CardanoLedgerApi.V1
open Address Credential IsData.Class Scripts Tx Time Value

section BlasterFacts
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
set_option maxHeartbeats 0
set_option Elab.async false

@[blaster_library] theorem validTokens_findToken (tns : List (Data × Data)) (prev tn : ByteString) :
    validTxOutValue.validTokens tns prev = true → 0 ≤ PlutusCore.Value.findToken tn tns := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem validCurrencySymbol_dataQuantity (v : List (Data × Data)) (prev cs tn : ByteString) :
    validTxOutValue.validCurrencySymbol v prev = true → 0 ≤ PlutusCore.Value.dataQuantity cs tn v := by
  blaster (induction: auto) (summaries: [validTokens_findToken]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem validTxOutValue_valueOf (v : Value) (cs : CurrencySymbol) (tn : TokenName) :
    validTxOutValue v = true → 0 ≤ valueOf cs tn v := by
  blaster (induction: auto) (summaries: [validTokens_findToken, validCurrencySymbol_dataQuantity])
    (timeout: 20) (gen-cex: 0)

/-- The names of a valid token walk lie above its bound: a name at or below
the bound is absent. -/
@[blaster_library] theorem validTokens_findToken_below (tns : List (Data × Data)) (prev tn : ByteString) :
    validTxOutValue.validTokens tns prev = true → tn ≤ prev →
      PlutusCore.Value.findToken tn tns = 0 := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

/-- In a valid token walk, a name below the head's name is absent (a walk
over an ascending map may stop there). -/
@[blaster_library] theorem validTokens_findToken_lt_head (q : Data) (xs : List (Data × Data)) (prev k tn : ByteString) :
    validTxOutValue.validTokens ((Data.B k, q) :: xs) prev = true → tn < k →
      PlutusCore.Value.findToken tn ((Data.B k, q) :: xs) = 0 := by
  blaster (summaries: [validTokens_findToken_below xs k tn]) (timeout: 20) (gen-cex: 0)

/-- The currencies of a valid currency walk lie above its bound: a currency at
or below the bound is absent. -/
@[blaster_library] theorem validCurrencySymbol_dataQuantity_below (v : List (Data × Data)) (prev cs tn : ByteString) :
    validTxOutValue.validCurrencySymbol v prev = true → cs ≤ prev →
      PlutusCore.Value.dataQuantity cs tn v = 0 := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

/-- In a valid currency walk, a currency below the head's currency is absent. -/
@[blaster_library] theorem validCurrencySymbol_dataQuantity_lt_head (m : Data) (xs : List (Data × Data)) (prev k cs tn : ByteString) :
    validTxOutValue.validCurrencySymbol ((Data.B k, m) :: xs) prev = true → cs < k →
      PlutusCore.Value.dataQuantity cs tn ((Data.B k, m) :: xs) = 0 := by
  blaster (summaries: [validCurrencySymbol_dataQuantity_below xs k cs tn]) (timeout: 20) (gen-cex: 0)

/-- The keys of an encoded map strictly ascend from a bound. -/
def keysAbove (p : ByteString) : List (Data × Data) → Bool
  | [] => true
  | (Data.B a, _) :: rest => decide (p < a) && keysAbove a rest
  | _ => false

/-- The keys of an encoded map strictly ascend (no bound: a walk's cursor
keeps it whatever it has skipped). -/
def keysAscending : List (Data × Data) → Bool
  | [] => true
  | (Data.B a, _) :: rest => keysAbove a rest
  | _ => false

@[blaster_library] theorem keysAscending_tail (e : Data × Data) (xs : List (Data × Data)) :
    keysAscending (e :: xs) = true → keysAscending xs = true := by
  blaster (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem keysAbove_findToken_below (xs : List (Data × Data)) (p tn : ByteString) :
    keysAbove p xs = true → tn ≤ p → PlutusCore.Value.findToken tn xs = 0 := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem keysAbove_dataQuantity_below (xs : List (Data × Data)) (p cs tn : ByteString) :
    keysAbove p xs = true → cs ≤ p → PlutusCore.Value.dataQuantity cs tn xs = 0 := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

/-- In an encoded map with ascending keys, a name below the head's is absent. -/
@[blaster_library] theorem keysAscending_findToken_lt_head (q : Data) (xs : List (Data × Data)) (k tn : ByteString) :
    keysAscending ((Data.B k, q) :: xs) = true → tn < k →
      PlutusCore.Value.findToken tn ((Data.B k, q) :: xs) = 0 := by
  blaster (summaries: [keysAbove_findToken_below xs k tn]) (timeout: 20) (gen-cex: 0)

/-- In an encoded value with ascending currencies, a currency below the head's is absent. -/
@[blaster_library] theorem keysAscending_dataQuantity_lt_head (m : Data) (xs : List (Data × Data)) (k cs tn : ByteString) :
    keysAscending ((Data.B k, m) :: xs) = true → cs < k →
      PlutusCore.Value.dataQuantity cs tn ((Data.B k, m) :: xs) = 0 := by
  blaster (summaries: [keysAbove_dataQuantity_below xs k cs tn]) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem validTokens_keysAbove (tns : List (Data × Data)) (prev : ByteString) :
    validTxOutValue.validTokens tns prev = true → keysAbove prev tns = true := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem validCurrencySymbol_keysAbove (v : List (Data × Data)) (prev : ByteString) :
    validTxOutValue.validCurrencySymbol v prev = true → keysAbove prev v = true := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

/-- A valid output value's currencies ascend (the Ada entry first). -/
@[blaster_library] theorem validTxOutValue_keysAscending (e : Data × Data) (xs : List (Data × Data)) :
    validTxOutValue (e :: xs) = true → keysAscending (e :: xs) = true := by
  blaster (summaries: [validCurrencySymbol_keysAbove xs ""]) (timeout: 20) (gen-cex: 0)

/-- The token map of a valid currency entry has ascending names. -/
@[blaster_library] theorem validCurrencySymbol_head_keysAscending (cs : Data) (tn : ByteString) (q : Data)
    (toks xs : List (Data × Data)) (prev : ByteString) :
    validTxOutValue.validCurrencySymbol ((cs, Data.Map ((Data.B tn, q) :: toks)) :: xs) prev = true →
      keysAscending ((Data.B tn, q) :: toks) = true := by
  blaster (summaries: [validTokens_keysAbove toks tn]) (timeout: 20) (gen-cex: 0)

/-- Decoding an encoded address gives it back. -/
@[blaster_library] theorem fromData_toData_address (a : Address.Address) :
    IsData.fromData (IsData.toData a) = some a := by
  blaster (timeout: 30)

/-- The builtin comparison of encoded credentials is credential equality. -/
@[blaster_library] theorem equalsData_toData_credential (a b : Credential) :
    PlutusCore.Data.equalsData (IsData.toData a) (IsData.toData b) = (a == b) := by
  blaster (timeout: 20)

/-- The builtin comparison of encoded addresses is address equality. -/
@[blaster_library] theorem equalsData_toData_address (a b : Address.Address) :
    PlutusCore.Data.equalsData (IsData.toData a) (IsData.toData b) = (a == b) := by
  blaster (timeout: 20)

/-- The Lovelace of a valid value is its Ada quantity. -/
@[blaster_library] theorem lovelaceOf_eq_valueOf (v : Value) :
    validTxOutValue v = true → lovelaceOf v = valueOf adaSymbol adaToken v := by
  blaster (timeout: 30)

/-- Dropping the leading (Ada) entry of a valid value keeps every other currency. -/
@[blaster_library] theorem valueOf_tailList (v t : Value) (cs : CurrencySymbol) (tn : TokenName) :
    validTxOutValue v = true → PlutusCore.List.tailList v = .ok t → (cs == adaSymbol) = false →
    valueOf cs tn t = valueOf cs tn v := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

/-- The leading entry of a valid value is Ada's: other currencies are read from the rest. -/
@[blaster_library] theorem valueOf_cons_valid (e : Data × Data) (rest : Value) (cs : CurrencySymbol) (tn : TokenName) :
    validTxOutValue (e :: rest) = true → (cs == adaSymbol) = false →
    valueOf cs tn (e :: rest) = valueOf cs tn rest := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

/-- The rest of a valid currency walk is valid from the empty (Ada) bound. -/
@[blaster_library] theorem validCurrencySymbol_tail (k v : Data) (xs : List (Data × Data)) :
    validTxOutValue.validCurrencySymbol ((k, v) :: xs) "" = true →
      validTxOutValue.validCurrencySymbol xs "" = true := by
  blaster (timeout: 20) (gen-cex: 0)

/-- In a valid currency walk, an entry of another currency is skipped. -/
@[blaster_library] theorem valueOf_cons_validWalk (k v : Data) (xs : Value) (prev : ByteString)
    (cs : CurrencySymbol) (tn : TokenName) :
    validTxOutValue.validCurrencySymbol ((k, v) :: xs) prev = true → (Data.B cs == k) = false →
      valueOf cs tn ((k, v) :: xs) = valueOf cs tn xs := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

/-- A valid currency walk carries token maps only. -/
@[blaster_library] theorem validCurrencySymbol_mapEntries (v : List (Data × Data)) (prev : ByteString) :
    validTxOutValue.validCurrencySymbol v prev = true → PlutusCore.Value.Internal.mapEntries v = true := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

/-- A valid output value carries token maps only. -/
@[blaster_library] theorem validTxOutValue_mapEntries (v : Value) :
    validTxOutValue v = true → PlutusCore.Value.Internal.mapEntries v = true := by
  blaster (induction: auto) (summaries: [validCurrencySymbol_mapEntries]) (timeout: 20) (gen-cex: 0)

/-- The entries after the leading (Ada) one of a valid output value carry token maps. -/
@[blaster_library] theorem validTxOutValue_tail_mapEntries (e : Data × Data) (es : List (Data × Data)) :
    validTxOutValue (e :: es) = true → PlutusCore.Value.Internal.mapEntries es = true := by
  blaster (induction: auto) (summaries: [validCurrencySymbol_mapEntries]) (timeout: 20) (gen-cex: 0)

/-- A valid output value's currencies ascend, for any value (the variable an
output walk starts from). -/
@[blaster_library] theorem validTxOutValue_keysAscending_any (v : List (Data × Data)) :
    validTxOutValue v = true → keysAscending v = true :=
  match v with
  | [] => by blaster (timeout: 20) (gen-cex: 0)
  | e :: xs => validTxOutValue_keysAscending e xs

/-- Every entry of an encoded value carries a token map with ascending names. -/
def tokenMapsAscending : List (Data × Data) → Bool
  | [] => true
  | (_, Data.Map toks) :: rest => keysAscending toks && tokenMapsAscending rest
  | _ => false

@[blaster_library] theorem tokenMapsAscending_tail (e : Data × Data) (xs : List (Data × Data)) :
    tokenMapsAscending (e :: xs) = true → tokenMapsAscending xs = true := by
  blaster (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem tokenMapsAscending_head (k : Data) (toks xs : List (Data × Data)) :
    tokenMapsAscending ((k, Data.Map toks) :: xs) = true → keysAscending toks = true := by
  blaster (timeout: 20) (gen-cex: 0)

@[blaster_library] theorem validCurrencySymbol_tokenMapsAscending (v : List (Data × Data)) (prev : ByteString) :
    validTxOutValue.validCurrencySymbol v prev = true → tokenMapsAscending v = true := by
  blaster (induction: auto) (summaries: [validTokens_keysAbove]) (timeout: 30) (gen-cex: 0)

@[blaster_library] theorem validTxOutValue_tokenMapsAscending_cons (e : Data × Data) (xs : List (Data × Data)) :
    validTxOutValue (e :: xs) = true → tokenMapsAscending (e :: xs) = true := by
  blaster (summaries: [validCurrencySymbol_tokenMapsAscending xs ""]) (timeout: 30) (gen-cex: 0)

/-- A valid output value's entries carry ascending token maps, for any value. -/
@[blaster_library] theorem validTxOutValue_tokenMapsAscending (v : List (Data × Data)) :
    validTxOutValue v = true → tokenMapsAscending v = true :=
  match v with
  | [] => by blaster (timeout: 20) (gen-cex: 0)
  | e :: xs => validTxOutValue_tokenMapsAscending_cons e xs

end BlasterFacts

end CardanoLedgerApi.V1.Contexts
