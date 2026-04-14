import CardanoLedgerApi.IsData.Class
import PlutusCore

namespace CardanoLedgerApi.V3.Tx

open IsData.Class
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)

/-- Transaction ID, i.e. the hash of a transaction. Hashed with BLAKE2b-256. 32 byte. -/
abbrev TxId := ByteString

/-- IsData instance for TxId
    In V3, TxId is encoded as Data.B
-/
instance : IsData TxId where
  toData := Data.B
  fromData
  | Data.B tid => some tid
  | _ => none

/-- A reference to a transaction output.
   This is a pair of a transaction ID (`TxId`), and an index indicating which of the outputs
   of that transaction we are referring to.
-/
structure TxOutRef where
  txOutRefId : TxId
  txOutRefIdx : Integer
deriving Repr

def beqTxOutRef (x y : TxOutRef) : Bool :=
  x.txOutRefId == y.txOutRefId && x.txOutRefIdx == y.txOutRefIdx

/-- BEq instance for TxOutRef -/
instance : BEq TxOutRef := ⟨beqTxOutRef⟩

/-! DecidableEq instance for TxOutRef -/
@[simp] theorem beqTxOutRef_iff_eq (x y : TxOutRef) : beqTxOutRef x y ↔ x = y := by
  match x, y with
  | TxOutRef.mk tid1 idx1, TxOutRef.mk tid2 idx2 => simp [beqTxOutRef]

@[simp] theorem beqTxOutRef_false_iff_not_eq (x y : TxOutRef) : beqTxOutRef x y = false ↔ x ≠ y := by
  match x, y with
  | TxOutRef.mk .., TxOutRef.mk .. => simp [beqTxOutRef]

def TxOutRef.decEq (x y : TxOutRef) : Decidable (Eq x y) :=
  match h:(beqTxOutRef x y) with
  | true => isTrue ((beqTxOutRef_iff_eq _ _ ).1 h)
  | false => isFalse ((beqTxOutRef_false_iff_not_eq _ _).1 h)

instance : DecidableEq TxOutRef := TxOutRef.decEq

/-! LawfulBEq instance for TxOutRef -/
theorem beqTxOutRef_reflexive (x : TxOutRef) : beqTxOutRef x x = true := by simp [beqTxOutRef]

instance : LawfulBEq TxOutRef where
  eq_of_beq {a b} := (beqTxOutRef_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]


def ltTxOutRef (x y : TxOutRef) : Bool :=
  x.txOutRefId < y.txOutRefId ||
  (x.txOutRefId == y.txOutRefId && x.txOutRefIdx < y.txOutRefIdx)

/-- LT instance for TxOutRef -/
instance : LT TxOutRef where
  lt x y := ltTxOutRef x y

/-! DecidableLT instance for TxOutRef -/
theorem ltTxOutRef_true_imp_lt (x y : TxOutRef) : ltTxOutRef x y → x < y := by
  match x, y with
  | TxOutRef.mk .., TxOutRef.mk .. => simp only [ltTxOutRef, LT.lt]; simp

theorem ltTxOutRef_false_imp_not_lt (x y : TxOutRef) :
  ltTxOutRef x y = false → ¬ x < y := by
    cases x <;> cases y <;> simp only [ltTxOutRef, LT.lt]; simp

def TxOutRef.decLt (x y : TxOutRef) : Decidable (LT.lt x y) :=
  match h:(ltTxOutRef x y) with
  | true => isTrue (ltTxOutRef_true_imp_lt _ _ h)
  | false => isFalse (ltTxOutRef_false_imp_not_lt _ _ h)

instance : DecidableLT (TxOutRef) := TxOutRef.decLt

@[simp] theorem ltTxOutRef_same_false (x : TxOutRef) : ltTxOutRef x x = false := by
  match x with
  | TxOutRef.mk .. =>
     simp only [ltTxOutRef, LT.lt]; simp <;> constructor
     . apply String.le_refl
     . apply Int.lt_irrefl

/-! Std.Irrefl instance for TxOutRef -/
theorem TxOutRef.lt_irrefl (x : TxOutRef) : ¬ x < x := by cases x <;> simp [LT.lt]

instance : Std.Irrefl (. < . : TxOutRef → TxOutRef → Prop) where
  irrefl := TxOutRef.lt_irrefl

/-- LE instance for TxOutRef -/
instance : LE TxOutRef where
  le x y := ¬ (y < x)

/-! DecidableLE instance for TxOutRef -/
instance : DecidableLE (TxOutRef) :=
  fun x y => inferInstanceAs (Decidable (¬ (y < x)))


/-- IsData instance for TxOutRef -/
instance : IsData TxOutRef where
 toData tref := mkDataConstr 0 [IsData.toData tref.txOutRefId, IsData.toData tref.txOutRefIdx]
 fromData
 | Data.Constr 0 [Data.B tid, Data.I ref] => some ⟨tid, ref⟩
 | _ => none


end CardanoLedgerApi.V3.Tx
