import CardanoLedgerApi.IsData.Class
import PlutusCore

namespace CardanoLedgerApi.V1.Scripts
open IsData.Class
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)

/-- `Datum` is an alias to `Data` -/
abbrev Datum := Data

/-- `Redeemer` is an alias to `Data` -/
abbrev Redeemer := Data

/-- `ScriptHash` is an alias to `ByteString` -/
abbrev ScriptHash := ByteString

/-- IsData instance for ScriptHash -/
instance : IsData ScriptHash where
  toData := Data.B
  fromData
  | Data.B sh => some sh
  | _ => none

/-- `DatumHash` is an alias to `ByteString` -/
abbrev DatumHash := ByteString

/-- IsData instance for DatumHash -/
instance : IsData DatumHash where
  toData := Data.B
  fromData
  | Data.B dh => some dh
  | _ => none

end CardanoLedgerApi.V1.Scripts
