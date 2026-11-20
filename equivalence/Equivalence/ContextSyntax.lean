import Equivalence.Queries

/-!
Defines syntax for constructing raw transaction values and V3 TxInfo fields.
Expands these encodings directly into Data constructors before symbolic processing.
Keeps the field order shared across context builders without extra function calls.
-/

namespace Equivalence.ContextSyntax
open Lean
open PlutusCore.Data (Data)

-- Expand before Blaster sees the terms. Function helpers for these encodings
-- changed Blaster timings despite definitional equality.
syntax "context_value% " term:max term:max term:max term:max : term

macro_rules
  | `(context_value% $ada $policy $token $quantity) =>
    `(Data.Map [(.B "", .Map [(.B "", .I $ada)]),
      (.B $policy, .Map [(.B $token, .I $quantity)])])

syntax "context_tx_info% " term:max term:max term:max term:max term:max : term

macro_rules
  | `(context_tx_info% $unused $inputs $outputs $signers $validRange) =>
    `(Data.Constr 0 [.List $inputs, ($unused).referenceInputs, $outputs, ($unused).fee,
      ($unused).mint, ($unused).certificates, ($unused).withdrawals, $validRange,
      .List $signers, ($unused).redeemers, ($unused).datums, ($unused).txId,
      ($unused).votes, ($unused).proposals, ($unused).treasury, ($unused).donation])

end Equivalence.ContextSyntax
