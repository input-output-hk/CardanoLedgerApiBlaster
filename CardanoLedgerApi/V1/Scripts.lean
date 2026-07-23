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
def ScriptHash : Type := ByteString

instance : Repr ScriptHash := inferInstanceAs (Repr ByteString)

/-- BEq instance for ScriptHash -/
instance : BEq ScriptHash := inferInstanceAs (BEq ByteString)

/-! LawfulBEq instance for ScriptHash -/
instance : LawfulBEq ScriptHash := inferInstanceAs (LawfulBEq ByteString)

/-! DecidableEq instance for ScriptHash -/
instance : DecidableEq ScriptHash := inferInstanceAs (DecidableEq ByteString)

/-- LT instance for ScriptHash -/
instance : LT ScriptHash := inferInstanceAs (LT ByteString)

/-- DecidableLT instance for TxOutRef -/
instance : DecidableLT (ScriptHash) := inferInstanceAs (DecidableLT ByteString)

@[simp] theorem beqScriptHash_iff_eq (x y : ScriptHash) : x == y ↔ x = y := by simp [BEq.beq]

@[simp] theorem beqScriptHash_false_iff_not_eq (x y : ScriptHash) : (x == y) = false ↔ x ≠ y := by simp [BEq.beq]

/-- Std.Irrefl instance for ScriptHash -/
instance : Std.Irrefl (. < . : ScriptHash → ScriptHash → Prop) :=
  inferInstanceAs (Std.Irrefl (. < . : ByteString → ByteString → Prop))

/-- LE instance for ScriptHash -/
instance : LE ScriptHash := inferInstanceAs (LE ByteString)

/-- DecidableLE instance for ScriptHash -/
instance : DecidableLE ScriptHash := inferInstanceAs (DecidableLE ByteString)

/-- ToString instance for ScriptHash -/
instance : ToString ScriptHash := inferInstanceAs (ToString ByteString)

/-- String to ScriptHash coercion to mimick OverloadedString in Haskell -/
instance : Coe String ScriptHash := inferInstanceAs (Coe String ByteString)

/-- IsData instance for ScriptHash -/
instance : IsData ScriptHash := inferInstanceAs (IsData ByteString)


/-- `DatumHash` is an alias to `ByteString` -/
def DatumHash : Type := ByteString

instance : Repr DatumHash := inferInstanceAs (Repr ByteString)

/-- BEq instance for DatumHash -/
instance : BEq DatumHash := inferInstanceAs (BEq ByteString)

/-! LawfulBEq instance for DatumHash -/
instance : LawfulBEq DatumHash := inferInstanceAs (LawfulBEq ByteString)

/-! DecidableEq instance for DatumHash -/
instance : DecidableEq DatumHash := inferInstanceAs (DecidableEq ByteString)

/-- LT instance for DatumHash -/
instance : LT DatumHash := inferInstanceAs (LT ByteString)

/-- DecidableLT instance for TxOutRef -/
instance : DecidableLT (DatumHash) := inferInstanceAs (DecidableLT ByteString)

@[simp] theorem beqDatumHash_iff_eq (x y : DatumHash) : x == y ↔ x = y := by simp [BEq.beq]

@[simp] theorem beqDatumHash_false_iff_not_eq (x y : DatumHash) : (x == y) = false ↔ x ≠ y := by simp [BEq.beq]

/-- Std.Irrefl instance for DatumHash -/
instance : Std.Irrefl (. < . : DatumHash → DatumHash → Prop) :=
  inferInstanceAs (Std.Irrefl (. < . : ByteString → ByteString → Prop))

/-- LE instance for DatumHash -/
instance : LE DatumHash := inferInstanceAs (LE ByteString)

/-- DecidableLE instance for DatumHash -/
instance : DecidableLE DatumHash := inferInstanceAs (DecidableLE ByteString)

/-- ToString instance for DatumHash -/
instance : ToString DatumHash := inferInstanceAs (ToString ByteString)

/-- String to DatumHash coercion to mimick OverloadedString in Haskell -/
instance : Coe String DatumHash := inferInstanceAs (Coe String ByteString)

/-- IsData instance for DatumHash -/
instance : IsData DatumHash := inferInstanceAs (IsData ByteString)

end CardanoLedgerApi.V1.Scripts
