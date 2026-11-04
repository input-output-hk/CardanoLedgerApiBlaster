import CardanoLedgerApi.V3
import PlutusCore.UPLC.BlueprintEncoding.Counterexample

namespace CardanoLedgerApi.Counterexample
open Blaster.Counterexample
open CardanoLedgerApi.IsData.Class

-- Preserve the actual ledger wire representation. Lean intentionally keeps
-- several TxInfo fields at Data level, so a guessed Haskell record is unsound.
instance : ToCEX V3.Contexts.ScriptContext := ⟨fun ctx =>
  .encoded "PlutusLedgerApi.V3.ScriptContext" "plutus-data"
    (toCEX (IsData.toData ctx))⟩

instance : ToCEX V3.Contexts.TxInfo := ⟨fun tx =>
  .encoded "PlutusLedgerApi.V3.TxInfo" "plutus-data"
    (toCEX (IsData.toData tx))⟩

instance : ToCEX V3.Contexts.ScriptInfo := ⟨fun info =>
  .encoded "PlutusLedgerApi.V3.ScriptInfo" "plutus-data"
    (toCEX (IsData.toData info))⟩

end CardanoLedgerApi.Counterexample
