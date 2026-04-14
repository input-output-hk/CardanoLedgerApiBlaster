import CardanoLedgerApi.IsData.Class
import CardanoLedgerApi.V1.Address
import CardanoLedgerApi.V1.Scripts
import CardanoLedgerApi.V1.Value
import PlutusCore

namespace CardanoLedgerApi.V1.Tx
open Address
open Credential
open IsData.Class
open PlutusCore.ByteString (ByteString)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)
open Scripts
open Value

/-- Transaction ID, i.e. the hash of a transaction. Hashed with BLAKE2b-256. 32 byte. -/
abbrev TxId := ByteString

/-- IsData instance for TxId
    In V1 and V2, TxId is encoded as Data.Constr 0 [Data.B txid]
-/
instance : IsData TxId where
  toData tid := Data.Constr 0 [Data.B tid]
  fromData
  | Data.Constr 0 [Data.B tid] => some tid
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

/-- A transaction output, consisting of an `Address`, a `Value` and optionally a `DatumHash` -/
structure TxOut where
  txOutAddress : Address
  txOutValue : Value
  txOutDatumHash : Option DatumHash
 deriving Repr

def beqTxOut (x y : TxOut) : Bool :=
  x.txOutAddress == y.txOutAddress &&
  x.txOutValue == y.txOutValue &&
  x.txOutDatumHash == y.txOutDatumHash

/-- BEq instance for TxOut -/
instance : BEq TxOut := ⟨beqTxOut⟩

/-! DecidableEq instance for TxOut -/
@[simp] theorem beqTxOut_iff_eq (x y : TxOut) : beqTxOut x y ↔ x = y := by
  match x, y with
  | TxOut.mk .., TxOut.mk .. => simp [beqTxOut]; apply and_assoc

@[simp] theorem beqTxOut_false_iff_not_eq (x y : TxOut) : beqTxOut x y = false ↔ x ≠ y := by
  match x, y with
  | TxOut.mk .., TxOut.mk .. => simp [beqTxOut];

def TxOut.decEq (x y : TxOut) : Decidable (Eq x y) :=
  match h:(beqTxOut x y) with
  | true => isTrue ((beqTxOut_iff_eq _ _).1 h)
  | false => isFalse ((beqTxOut_false_iff_not_eq _ _).1 h)

instance : DecidableEq TxOut := TxOut.decEq

/-! LawfulBEq instance for TxOut -/
theorem beqTxOut_reflexive (x : TxOut) : beqTxOut x x = true := by simp [beqTxOut]

instance : LawfulBEq TxOut where
  eq_of_beq {a b} := (beqTxOut_iff_eq a b).1
  rfl {bs} := by simp [BEq.beq]


/-- IsData instance for TxOut -/
instance : IsData TxOut where
  toData out :=
     mkDataConstr 0
     [ IsData.toData out.txOutAddress
     , IsData.toData out.txOutValue
     , IsData.toData out.txOutDatumHash
     ]
  fromData
  | Data.Constr 0 [r_addr, r_val, r_dh] =>
      match IsData.fromData r_addr, IsData.fromData r_val, IsData.fromData r_dh with
      | some addr, some val, some dh => some ⟨addr, val, dh⟩
      | _, _, _ => none
  | _ => none


/-! List of helpers and predicates -/

/-- Return the public key hash attached to a `TxOut`, if any. -/
def txOutPubKey (out : TxOut) : Option PubKeyHash :=
  toPubKeyHash out.txOutAddress

/-- Return the script hash attached to a `TxOut`, if any. -/
def txOutScriptHash (out : TxOut) : Option ScriptHash :=
  toScriptHash out.txOutAddress

/-- Return `true` only when `TxOut.txOutAddress` corresponds to validator hash `sh`. -/
def hasScriptAddress (sh : ScriptHash) (out : TxOut) : Bool :=
  hasScriptHash sh out.txOutAddress

/-- Return `true` only when `TxOut.txOutAddress` corresponds to public key hash `pk`. -/
def hasPubKeyAddress (pk : PubKeyHash) (out : TxOut) : Bool :=
  hasPubKeyHash pk out.txOutAddress

/-- Return `true` only when `TxOut.txOutDatumHash is set. -/
def hasDatumHash (out : TxOut) : Bool := out.txOutDatumHash.isSome


end CardanoLedgerApi.V1.Tx
