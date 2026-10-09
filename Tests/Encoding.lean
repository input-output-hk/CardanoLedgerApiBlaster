import Blaster
import CardanoLedgerApi.V1

open CardanoLedgerApi.V1 CardanoLedgerApi.IsData.Class

set_option warn.sorry false

def payment_only_implies_same_encoding_cex :=
  ∀ (a b : Address),
    a.addressCredential = b.addressCredential → IsData.toData a == (IsData.toData b)

-- Counterexample expected by Blaster
#blaster (gen-cex: 0) (solve-result: 1) [payment_only_implies_same_encoding_cex]

theorem encoded_eq_iff_address_eq (a b : Address) : IsData.toData a == IsData.toData b ↔ (a == b) := by blaster
