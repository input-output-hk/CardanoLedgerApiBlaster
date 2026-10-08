import CardanoLedgerApiFacts.OutputValues
import CardanoLedgerApiFacts.Value
import CardanoLedgerApi.V3.Contexts
import PlutusCoreFacts
import Blaster

namespace CardanoLedgerApi.V3.Contexts
open CardanoLedgerApi.V3
open CardanoLedgerApi.V1
open Address Credential IsData.Class Scripts Tx Time Value
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)

section BlasterFacts
open CardanoLedgerApi.V1.Value (valueOf)
set_option maxHeartbeats 0
set_option Elab.async false

/-- The rest of a valid mint currency walk is valid from the empty (Ada) bound. -/
@[blaster_library] theorem validMintCurrencySymbol_tail (k v : Data) (xs : List (Data × Data)) :
    validMintValue.validCurrencySymbol ((k, v) :: xs) "" = true →
      validMintValue.validCurrencySymbol xs "" = true := by
  blaster (timeout: 20) (gen-cex: 0)

/-- In a valid mint currency walk, an entry of another currency is skipped. -/
@[blaster_library] theorem valueOf_cons_validMintWalk (k v : Data) (xs : List (Data × Data)) (prev : ByteString)
    (cs : ByteString) (tn : ByteString) :
    validMintValue.validCurrencySymbol ((k, v) :: xs) prev = true → (Data.B cs == k) = false →
      valueOf cs tn ((k, v) :: xs) = valueOf cs tn xs := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

/-- `validMintCurrencySymbol_tail` at the Ada bound as the ledger spells it. -/
@[blaster_library] theorem validMintCurrencySymbol_tail_ada (k v : Data) (xs : List (Data × Data)) :
    validMintValue.validCurrencySymbol ((k, v) :: xs) CardanoLedgerApi.V1.adaSymbol = true →
      validMintValue.validCurrencySymbol xs CardanoLedgerApi.V1.adaSymbol = true := by
  blaster (timeout: 20) (gen-cex: 0)

/-- A valid mint currency walk carries token maps only. -/
@[blaster_library] theorem validMintCurrencySymbol_mapEntries (v : List (Data × Data)) (prev : ByteString) :
    validMintValue.validCurrencySymbol v prev = true → PlutusCore.Value.Internal.mapEntries v = true := by
  blaster (induction: auto) (timeout: 20) (gen-cex: 0)

/-- A valid mint value carries token maps only. -/
@[blaster_library] theorem validMintValue_mapEntries (v : MintValue) :
    validMintValue v = true → PlutusCore.Value.Internal.mapEntries v = true := by
  blaster (induction: auto) (summaries: [validMintCurrencySymbol_mapEntries]) (timeout: 20) (gen-cex: 0)

end BlasterFacts

end CardanoLedgerApi.V3.Contexts
