import CardanoLedgerApiFacts
import FactTests.Support

open CardanoLedgerApi.V1 CardanoLedgerApi.V1.Value CardanoLedgerApi.V1.Contexts
open PlutusCore.Data (Data)

example (v : Value) (cs : CurrencySymbol) (tn : TokenName)
    (valid : validTxOutValue v = true) : 0 ≤ valueOf cs tn v := by
  blaster (summaries: [validTxOutValue_valueOf]) (timeout: 10) (gen-cex: 0)

-- Output validity supplies the nonnegative quantity premise; mint values may be negative.
#reject "Goal was falsified" in
example (q : Int) :
    0 ≤ valueOf "01" "02" [(Data.B "01", Data.Map [(Data.B "02", Data.I q)])] := by
  blaster (timeout: 10) (gen-cex: 0)

-- A malformed currency entry stops lookup, even if a later entry matches.
example (cs : CurrencySymbol) (tn : TokenName) (rest : Value) :
    valueOf cs tn ((Data.I 0, Data.I 1) :: rest) = 0 := by rfl
